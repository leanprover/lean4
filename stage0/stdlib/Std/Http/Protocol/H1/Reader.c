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
lean_object* v_one_330_; lean_object* v_n_331_; uint8_t v___y_333_; lean_object* v___x_335_; lean_object* v_fst_336_; lean_object* v_snd_337_; lean_object* v___x_338_; lean_object* v_fst_339_; lean_object* v_snd_340_; uint8_t v___x_341_; 
v_one_330_ = lean_unsigned_to_nat(1u);
v_n_331_ = lean_nat_sub(v_x_327_, v_one_330_);
lean_dec(v_x_327_);
v___x_335_ = lean_array_fget_borrowed(v_xs_325_, v_n_331_);
v_fst_336_ = lean_ctor_get(v___x_335_, 0);
v_snd_337_ = lean_ctor_get(v___x_335_, 1);
v___x_338_ = lean_array_fget_borrowed(v_ys_326_, v_n_331_);
v_fst_339_ = lean_ctor_get(v___x_338_, 0);
v_snd_340_ = lean_ctor_get(v___x_338_, 1);
v___x_341_ = l_Std_Http_Chunk_instBEqExtensionName_beq(v_fst_336_, v_fst_339_);
if (v___x_341_ == 0)
{
v___y_333_ = v___x_341_;
goto v___jp_332_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_snd_337_, v_snd_340_);
v___y_333_ = v___x_342_;
goto v___jp_332_;
}
v___jp_332_:
{
if (v___y_333_ == 0)
{
lean_dec(v_n_331_);
return v___y_333_;
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
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg___boxed(lean_object* v_xs_343_, lean_object* v_ys_344_, lean_object* v_x_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_343_, v_ys_344_, v_x_345_);
lean_dec_ref(v_ys_344_);
lean_dec_ref(v_xs_343_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
switch(lean_obj_tag(v_x_348_))
{
case 0:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v_remaining_350_; lean_object* v_remaining_351_; uint8_t v___x_352_; 
v_remaining_350_ = lean_ctor_get(v_x_348_, 0);
v_remaining_351_ = lean_ctor_get(v_x_349_, 0);
v___x_352_ = lean_nat_dec_eq(v_remaining_350_, v_remaining_351_);
return v___x_352_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = 0;
return v___x_353_;
}
}
case 1:
{
if (lean_obj_tag(v_x_349_) == 1)
{
uint8_t v___x_354_; 
v___x_354_ = 1;
return v___x_354_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = 0;
return v___x_355_;
}
}
case 2:
{
if (lean_obj_tag(v_x_349_) == 2)
{
lean_object* v_ext_356_; lean_object* v_remaining_357_; lean_object* v_ext_358_; lean_object* v_remaining_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_ext_356_ = lean_ctor_get(v_x_348_, 0);
v_remaining_357_ = lean_ctor_get(v_x_348_, 1);
v_ext_358_ = lean_ctor_get(v_x_349_, 0);
v_remaining_359_ = lean_ctor_get(v_x_349_, 1);
v___x_360_ = lean_array_get_size(v_ext_356_);
v___x_361_ = lean_array_get_size(v_ext_358_);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_ext_356_, v_ext_358_, v___x_360_);
if (v___x_363_ == 0)
{
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = lean_nat_dec_eq(v_remaining_357_, v_remaining_359_);
return v___x_364_;
}
}
}
else
{
uint8_t v___x_365_; 
v___x_365_ = 0;
return v___x_365_;
}
}
default: 
{
if (lean_obj_tag(v_x_349_) == 3)
{
uint8_t v___x_366_; 
v___x_366_ = 1;
return v___x_366_;
}
else
{
uint8_t v___x_367_; 
v___x_367_ = 0;
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_x_368_, v_x_369_);
lean_dec(v_x_369_);
lean_dec(v_x_368_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(lean_object* v_xs_372_, lean_object* v_ys_373_, lean_object* v_hsz_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_372_, v_ys_373_, v_x_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(lean_object* v_xs_378_, lean_object* v_ys_379_, lean_object* v_hsz_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(v_xs_378_, v_ys_379_, v_hsz_380_, v_x_381_, v_x_382_);
lean_dec_ref(v_ys_379_);
lean_dec_ref(v_xs_378_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(lean_object* v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_obj_tag_nat(v_x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg___boxed(lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(v_x_389_);
lean_dec(v_x_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(uint8_t v_dir_391_, lean_object* v_x_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_obj_tag_nat(v_x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___boxed(lean_object* v_dir_394_, lean_object* v_x_395_){
_start:
{
uint8_t v_dir_boxed_396_; lean_object* v_res_397_; 
v_dir_boxed_396_ = lean_unbox(v_dir_394_);
v_res_397_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(v_dir_boxed_396_, v_x_395_);
lean_dec(v_x_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(lean_object* v_t_398_, lean_object* v_k_399_){
_start:
{
switch(lean_obj_tag(v_t_398_))
{
case 1:
{
lean_object* v_a_400_; lean_object* v___x_401_; 
v_a_400_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v_t_398_, 1);
v___x_401_ = lean_apply_1(v_k_399_, v_a_400_);
return v___x_401_;
}
case 2:
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v_t_398_, 1);
v___x_403_ = lean_apply_1(v_k_399_, v_a_402_);
return v___x_403_;
}
case 3:
{
lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_404_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v_t_398_, 1);
v___x_405_ = lean_apply_1(v_k_399_, v_a_404_);
return v___x_405_;
}
case 7:
{
lean_object* v_error_406_; lean_object* v___x_407_; 
v_error_406_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_error_406_);
lean_dec_ref_known(v_t_398_, 1);
v___x_407_ = lean_apply_1(v_k_399_, v_error_406_);
return v___x_407_;
}
default: 
{
lean_dec(v_t_398_);
return v_k_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim(uint8_t v_dir_408_, lean_object* v_motive_409_, lean_object* v_ctorIdx_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_k_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_411_, v_k_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(lean_object* v_dir_415_, lean_object* v_motive_416_, lean_object* v_ctorIdx_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_k_420_){
_start:
{
uint8_t v_dir_boxed_421_; lean_object* v_res_422_; 
v_dir_boxed_421_ = lean_unbox(v_dir_415_);
v_res_422_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(v_dir_boxed_421_, v_motive_416_, v_ctorIdx_417_, v_t_418_, v_h_419_, v_k_420_);
lean_dec(v_ctorIdx_417_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(lean_object* v_t_423_, lean_object* v_needStartLine_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_423_, v_needStartLine_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(uint8_t v_dir_426_, lean_object* v_motive_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_needStartLine_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_428_, v_needStartLine_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(lean_object* v_dir_432_, lean_object* v_motive_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_needStartLine_436_){
_start:
{
uint8_t v_dir_boxed_437_; lean_object* v_res_438_; 
v_dir_boxed_437_ = lean_unbox(v_dir_432_);
v_res_438_ = l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(v_dir_boxed_437_, v_motive_433_, v_t_434_, v_h_435_, v_needStartLine_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___redArg(lean_object* v_t_439_, lean_object* v_needHeader_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_439_, v_needHeader_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(uint8_t v_dir_442_, lean_object* v_motive_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_needHeader_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_444_, v_needHeader_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(lean_object* v_dir_448_, lean_object* v_motive_449_, lean_object* v_t_450_, lean_object* v_h_451_, lean_object* v_needHeader_452_){
_start:
{
uint8_t v_dir_boxed_453_; lean_object* v_res_454_; 
v_dir_boxed_453_ = lean_unbox(v_dir_448_);
v_res_454_ = l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(v_dir_boxed_453_, v_motive_449_, v_t_450_, v_h_451_, v_needHeader_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___redArg(lean_object* v_t_455_, lean_object* v_readBody_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_455_, v_readBody_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim(uint8_t v_dir_458_, lean_object* v_motive_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_readBody_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_460_, v_readBody_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(lean_object* v_dir_464_, lean_object* v_motive_465_, lean_object* v_t_466_, lean_object* v_h_467_, lean_object* v_readBody_468_){
_start:
{
uint8_t v_dir_boxed_469_; lean_object* v_res_470_; 
v_dir_boxed_469_ = lean_unbox(v_dir_464_);
v_res_470_ = l_Std_Http_Protocol_H1_Reader_State_readBody_elim(v_dir_boxed_469_, v_motive_465_, v_t_466_, v_h_467_, v_readBody_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___redArg(lean_object* v_t_471_, lean_object* v_continue_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_471_, v_continue_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim(uint8_t v_dir_474_, lean_object* v_motive_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_continue_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_476_, v_continue_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___boxed(lean_object* v_dir_480_, lean_object* v_motive_481_, lean_object* v_t_482_, lean_object* v_h_483_, lean_object* v_continue_484_){
_start:
{
uint8_t v_dir_boxed_485_; lean_object* v_res_486_; 
v_dir_boxed_485_ = lean_unbox(v_dir_480_);
v_res_486_ = l_Std_Http_Protocol_H1_Reader_State_continue_elim(v_dir_boxed_485_, v_motive_481_, v_t_482_, v_h_483_, v_continue_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___redArg(lean_object* v_t_487_, lean_object* v_pending_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_487_, v_pending_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim(uint8_t v_dir_490_, lean_object* v_motive_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_pending_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_492_, v_pending_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(lean_object* v_dir_496_, lean_object* v_motive_497_, lean_object* v_t_498_, lean_object* v_h_499_, lean_object* v_pending_500_){
_start:
{
uint8_t v_dir_boxed_501_; lean_object* v_res_502_; 
v_dir_boxed_501_ = lean_unbox(v_dir_496_);
v_res_502_ = l_Std_Http_Protocol_H1_Reader_State_pending_elim(v_dir_boxed_501_, v_motive_497_, v_t_498_, v_h_499_, v_pending_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___redArg(lean_object* v_t_503_, lean_object* v_complete_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_503_, v_complete_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim(uint8_t v_dir_506_, lean_object* v_motive_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_complete_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_508_, v_complete_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(lean_object* v_dir_512_, lean_object* v_motive_513_, lean_object* v_t_514_, lean_object* v_h_515_, lean_object* v_complete_516_){
_start:
{
uint8_t v_dir_boxed_517_; lean_object* v_res_518_; 
v_dir_boxed_517_ = lean_unbox(v_dir_512_);
v_res_518_ = l_Std_Http_Protocol_H1_Reader_State_complete_elim(v_dir_boxed_517_, v_motive_513_, v_t_514_, v_h_515_, v_complete_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___redArg(lean_object* v_t_519_, lean_object* v_closed_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_519_, v_closed_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim(uint8_t v_dir_522_, lean_object* v_motive_523_, lean_object* v_t_524_, lean_object* v_h_525_, lean_object* v_closed_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_524_, v_closed_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(lean_object* v_dir_528_, lean_object* v_motive_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_closed_532_){
_start:
{
uint8_t v_dir_boxed_533_; lean_object* v_res_534_; 
v_dir_boxed_533_ = lean_unbox(v_dir_528_);
v_res_534_ = l_Std_Http_Protocol_H1_Reader_State_closed_elim(v_dir_boxed_533_, v_motive_529_, v_t_530_, v_h_531_, v_closed_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___redArg(lean_object* v_t_535_, lean_object* v_failed_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_535_, v_failed_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim(uint8_t v_dir_538_, lean_object* v_motive_539_, lean_object* v_t_540_, lean_object* v_h_541_, lean_object* v_failed_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_540_, v_failed_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___boxed(lean_object* v_dir_544_, lean_object* v_motive_545_, lean_object* v_t_546_, lean_object* v_h_547_, lean_object* v_failed_548_){
_start:
{
uint8_t v_dir_boxed_549_; lean_object* v_res_550_; 
v_dir_boxed_549_ = lean_unbox(v_dir_544_);
v_res_550_ = l_Std_Http_Protocol_H1_Reader_State_failed_elim(v_dir_boxed_549_, v_motive_545_, v_t_546_, v_h_547_, v_failed_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg(){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_box(0);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg___boxed(lean_object* v___dummy_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t v_dir_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lean_box(0);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object* v_dir_557_){
_start:
{
uint8_t v_dir_boxed_558_; lean_object* v_res_559_; 
v_dir_boxed_558_ = lean_unbox(v_dir_557_);
v_res_559_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg(){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = lean_box(0);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg___boxed(lean_object* v___dummy_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t v_a_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_box(0);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object* v_a_566_){
_start:
{
uint8_t v_a_11__boxed_567_; lean_object* v_res_568_; 
v_a_11__boxed_567_ = lean_unbox(v_a_566_);
v_res_568_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_11__boxed_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(lean_object* v_x_605_, lean_object* v_prec_606_){
_start:
{
lean_object* v___y_608_; lean_object* v___y_615_; lean_object* v___y_622_; lean_object* v___y_629_; 
switch(lean_obj_tag(v_x_605_))
{
case 0:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(1024u);
v___x_636_ = lean_nat_dec_le(v___x_635_, v_prec_606_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_629_ = v___x_637_;
goto v___jp_628_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_629_ = v___x_638_;
goto v___jp_628_;
}
}
case 1:
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_659_; 
v_a_639_ = lean_ctor_get(v_x_605_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_659_ == 0)
{
v___x_641_ = v_x_605_;
v_isShared_642_ = v_isSharedCheck_659_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v_x_605_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_659_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___y_644_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(1024u);
v___x_656_ = lean_nat_dec_le(v___x_655_, v_prec_606_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_644_ = v___x_657_;
goto v___jp_643_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_644_ = v___x_658_;
goto v___jp_643_;
}
v___jp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_645_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10));
v___x_646_ = l_Nat_reprFast(v_a_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 3);
lean_ctor_set(v___x_641_, 0, v___x_646_);
v___x_648_ = v___x_641_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_654_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_645_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
lean_inc(v___y_644_);
v___x_650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_650_, 0, v___y_644_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = 0;
v___x_652_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*1, v___x_651_);
v___x_653_ = l_Repr_addAppParen(v___x_652_, v_prec_606_);
return v___x_653_;
}
}
}
}
case 2:
{
lean_object* v_a_660_; lean_object* v___y_662_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_a_660_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v_x_605_, 1);
v___x_671_ = lean_unsigned_to_nat(1024u);
v___x_672_ = lean_nat_dec_le(v___x_671_, v_prec_606_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_662_ = v___x_673_;
goto v___jp_661_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_662_ = v___x_674_;
goto v___jp_661_;
}
v___jp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_663_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13));
v___x_664_ = lean_unsigned_to_nat(1024u);
v___x_665_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_660_, v___x_664_);
v___x_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_663_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_inc(v___y_662_);
v___x_667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_667_, 0, v___y_662_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = 0;
v___x_669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_668_);
v___x_670_ = l_Repr_addAppParen(v___x_669_, v_prec_606_);
return v___x_670_;
}
}
case 3:
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v___y_678_; uint8_t v___x_686_; 
v_a_675_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v_x_605_, 1);
v___x_676_ = lean_unsigned_to_nat(1024u);
v___x_686_ = lean_nat_dec_le(v___x_676_, v_prec_606_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_678_ = v___x_687_;
goto v___jp_677_;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_678_ = v___x_688_;
goto v___jp_677_;
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_679_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16));
v___x_680_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_a_675_, v___x_676_);
v___x_681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_inc(v___y_678_);
v___x_682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_678_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = 0;
v___x_684_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*1, v___x_683_);
v___x_685_ = l_Repr_addAppParen(v___x_684_, v_prec_606_);
return v___x_685_;
}
}
case 4:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(1024u);
v___x_690_ = lean_nat_dec_le(v___x_689_, v_prec_606_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_622_ = v___x_691_;
goto v___jp_621_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_622_ = v___x_692_;
goto v___jp_621_;
}
}
case 5:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(1024u);
v___x_694_ = lean_nat_dec_le(v___x_693_, v_prec_606_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_615_ = v___x_695_;
goto v___jp_614_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_615_ = v___x_696_;
goto v___jp_614_;
}
}
case 6:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_unsigned_to_nat(1024u);
v___x_698_ = lean_nat_dec_le(v___x_697_, v_prec_606_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_608_ = v___x_699_;
goto v___jp_607_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_608_ = v___x_700_;
goto v___jp_607_;
}
}
default: 
{
lean_object* v_error_701_; lean_object* v___y_703_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_error_701_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_error_701_);
lean_dec_ref_known(v_x_605_, 1);
v___x_712_ = lean_unsigned_to_nat(1024u);
v___x_713_ = lean_nat_dec_le(v___x_712_, v_prec_606_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_703_ = v___x_714_;
goto v___jp_702_;
}
else
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_703_ = v___x_715_;
goto v___jp_702_;
}
v___jp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_704_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19));
v___x_705_ = lean_unsigned_to_nat(1024u);
v___x_706_ = l_Std_Http_Protocol_H1_instReprError_repr(v_error_701_, v___x_705_);
v___x_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_704_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
lean_inc(v___y_703_);
v___x_708_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_708_, 0, v___y_703_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = 0;
v___x_710_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*1, v___x_709_);
v___x_711_ = l_Repr_addAppParen(v___x_710_, v_prec_606_);
return v___x_711_;
}
}
}
v___jp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_609_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1));
lean_inc(v___y_608_);
v___x_610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_610_, 0, v___y_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = 0;
v___x_612_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*1, v___x_611_);
v___x_613_ = l_Repr_addAppParen(v___x_612_, v_prec_606_);
return v___x_613_;
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_616_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3));
lean_inc(v___y_615_);
v___x_617_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_617_, 0, v___y_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = 0;
v___x_619_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*1, v___x_618_);
v___x_620_ = l_Repr_addAppParen(v___x_619_, v_prec_606_);
return v___x_620_;
}
v___jp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_623_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5));
lean_inc(v___y_622_);
v___x_624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_624_, 0, v___y_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = 0;
v___x_626_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*1, v___x_625_);
v___x_627_ = l_Repr_addAppParen(v___x_626_, v_prec_606_);
return v___x_627_;
}
v___jp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7));
lean_inc(v___y_629_);
v___x_631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_631_, 0, v___y_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = 0;
v___x_633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*1, v___x_632_);
v___x_634_ = l_Repr_addAppParen(v___x_633_, v_prec_606_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(lean_object* v_x_716_, lean_object* v_prec_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_716_, v_prec_717_);
lean_dec(v_prec_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr(uint8_t v_dir_719_, lean_object* v_x_720_, lean_object* v_prec_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_720_, v_prec_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(lean_object* v_dir_723_, lean_object* v_x_724_, lean_object* v_prec_725_){
_start:
{
uint8_t v_dir_876__boxed_726_; lean_object* v_res_727_; 
v_dir_876__boxed_726_ = lean_unbox(v_dir_723_);
v_res_727_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(v_dir_876__boxed_726_, v_x_724_, v_prec_725_);
lean_dec(v_prec_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState(uint8_t v_dir_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_box(v_dir_728_);
v___x_730_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed), 3, 1);
lean_closure_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState___boxed(lean_object* v_dir_731_){
_start:
{
uint8_t v_dir_5__boxed_732_; lean_object* v_res_733_; 
v_dir_5__boxed_732_ = lean_unbox(v_dir_731_);
v_res_733_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_732_);
return v_res_733_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
switch(lean_obj_tag(v_x_734_))
{
case 0:
{
if (lean_obj_tag(v_x_735_) == 0)
{
uint8_t v___x_736_; 
v___x_736_ = 1;
return v___x_736_;
}
else
{
uint8_t v___x_737_; 
v___x_737_ = 0;
return v___x_737_;
}
}
case 1:
{
if (lean_obj_tag(v_x_735_) == 1)
{
lean_object* v_a_738_; lean_object* v_a_739_; uint8_t v___x_740_; 
v_a_738_ = lean_ctor_get(v_x_734_, 0);
v_a_739_ = lean_ctor_get(v_x_735_, 0);
v___x_740_ = lean_nat_dec_eq(v_a_738_, v_a_739_);
return v___x_740_;
}
else
{
uint8_t v___x_741_; 
v___x_741_ = 0;
return v___x_741_;
}
}
case 2:
{
if (lean_obj_tag(v_x_735_) == 2)
{
lean_object* v_a_742_; lean_object* v_a_743_; uint8_t v___x_744_; 
v_a_742_ = lean_ctor_get(v_x_734_, 0);
v_a_743_ = lean_ctor_get(v_x_735_, 0);
v___x_744_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_a_742_, v_a_743_);
return v___x_744_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = 0;
return v___x_745_;
}
}
case 3:
{
if (lean_obj_tag(v_x_735_) == 3)
{
lean_object* v_a_746_; lean_object* v_a_747_; 
v_a_746_ = lean_ctor_get(v_x_734_, 0);
v_a_747_ = lean_ctor_get(v_x_735_, 0);
v_x_734_ = v_a_746_;
v_x_735_ = v_a_747_;
goto _start;
}
else
{
uint8_t v___x_749_; 
v___x_749_ = 0;
return v___x_749_;
}
}
case 4:
{
if (lean_obj_tag(v_x_735_) == 4)
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
case 5:
{
if (lean_obj_tag(v_x_735_) == 5)
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
case 6:
{
if (lean_obj_tag(v_x_735_) == 6)
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
default: 
{
if (lean_obj_tag(v_x_735_) == 7)
{
lean_object* v_error_756_; lean_object* v_error_757_; uint8_t v___x_758_; 
v_error_756_ = lean_ctor_get(v_x_734_, 0);
v_error_757_ = lean_ctor_get(v_x_735_, 0);
v___x_758_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_error_756_, v_error_757_);
return v___x_758_;
}
else
{
uint8_t v___x_759_; 
v___x_759_ = 0;
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_760_, v_x_761_);
lean_dec(v_x_761_);
lean_dec(v_x_760_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq(uint8_t v_dir_764_, lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(lean_object* v_dir_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
uint8_t v_dir_183__boxed_771_; uint8_t v_res_772_; lean_object* v_r_773_; 
v_dir_183__boxed_771_ = lean_unbox(v_dir_768_);
v_res_772_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(v_dir_183__boxed_771_, v_x_769_, v_x_770_);
lean_dec(v_x_770_);
lean_dec(v_x_769_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState(uint8_t v_dir_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_box(v_dir_774_);
v___x_776_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed), 3, 1);
lean_closure_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(lean_object* v_dir_777_){
_start:
{
uint8_t v_dir_5__boxed_778_; lean_object* v_res_779_; 
v_dir_5__boxed_778_ = lean_unbox(v_dir_777_);
v_res_779_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_778_);
return v_res_779_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object* v_reader_780_){
_start:
{
lean_object* v_state_781_; 
v_state_781_ = lean_ctor_get(v_reader_780_, 0);
if (lean_obj_tag(v_state_781_) == 6)
{
uint8_t v___x_782_; 
v___x_782_ = 1;
return v___x_782_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object* v_reader_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_784_);
lean_dec_ref(v_reader_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t v_dir_787_, lean_object* v_reader_788_){
_start:
{
lean_object* v_state_789_; 
v_state_789_ = lean_ctor_get(v_reader_788_, 0);
if (lean_obj_tag(v_state_789_) == 6)
{
uint8_t v___x_790_; 
v___x_790_ = 1;
return v___x_790_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = 0;
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object* v_dir_792_, lean_object* v_reader_793_){
_start:
{
uint8_t v_dir_boxed_794_; uint8_t v_res_795_; lean_object* v_r_796_; 
v_dir_boxed_794_ = lean_unbox(v_dir_792_);
v_res_795_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_794_, v_reader_793_);
lean_dec_ref(v_reader_793_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object* v_reader_797_){
_start:
{
lean_object* v_state_798_; 
v_state_798_ = lean_ctor_get(v_reader_797_, 0);
if (lean_obj_tag(v_state_798_) == 5)
{
uint8_t v___x_799_; 
v___x_799_ = 1;
return v___x_799_;
}
else
{
uint8_t v___x_800_; 
v___x_800_ = 0;
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object* v_reader_801_){
_start:
{
uint8_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_801_);
lean_dec_ref(v_reader_801_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t v_dir_804_, lean_object* v_reader_805_){
_start:
{
lean_object* v_state_806_; 
v_state_806_ = lean_ctor_get(v_reader_805_, 0);
if (lean_obj_tag(v_state_806_) == 5)
{
uint8_t v___x_807_; 
v___x_807_ = 1;
return v___x_807_;
}
else
{
uint8_t v___x_808_; 
v___x_808_ = 0;
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object* v_dir_809_, lean_object* v_reader_810_){
_start:
{
uint8_t v_dir_boxed_811_; uint8_t v_res_812_; lean_object* v_r_813_; 
v_dir_boxed_811_ = lean_unbox(v_dir_809_);
v_res_812_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_811_, v_reader_810_);
lean_dec_ref(v_reader_810_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(lean_object* v_reader_814_){
_start:
{
lean_object* v_state_815_; 
v_state_815_ = lean_ctor_get(v_reader_814_, 0);
if (lean_obj_tag(v_state_815_) == 7)
{
uint8_t v___x_816_; 
v___x_816_ = 1;
return v___x_816_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___redArg___boxed(lean_object* v_reader_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_818_);
lean_dec_ref(v_reader_818_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed(uint8_t v_dir_821_, lean_object* v_reader_822_){
_start:
{
lean_object* v_state_823_; 
v_state_823_ = lean_ctor_get(v_reader_822_, 0);
if (lean_obj_tag(v_state_823_) == 7)
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___boxed(lean_object* v_dir_826_, lean_object* v_reader_827_){
_start:
{
uint8_t v_dir_boxed_828_; uint8_t v_res_829_; lean_object* v_r_830_; 
v_dir_boxed_828_ = lean_unbox(v_dir_826_);
v_res_829_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_boxed_828_, v_reader_827_);
lean_dec_ref(v_reader_827_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___redArg(lean_object* v_data_831_, lean_object* v_reader_832_){
_start:
{
lean_object* v_input_833_; lean_object* v_state_834_; lean_object* v_messageHead_835_; lean_object* v_messageCount_836_; lean_object* v_bodyBytesRead_837_; lean_object* v_headerBytesRead_838_; uint8_t v_noMoreInput_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_860_; 
v_input_833_ = lean_ctor_get(v_reader_832_, 1);
v_state_834_ = lean_ctor_get(v_reader_832_, 0);
v_messageHead_835_ = lean_ctor_get(v_reader_832_, 2);
v_messageCount_836_ = lean_ctor_get(v_reader_832_, 3);
v_bodyBytesRead_837_ = lean_ctor_get(v_reader_832_, 4);
v_headerBytesRead_838_ = lean_ctor_get(v_reader_832_, 5);
v_noMoreInput_839_ = lean_ctor_get_uint8(v_reader_832_, sizeof(void*)*6);
v_isSharedCheck_860_ = !lean_is_exclusive(v_reader_832_);
if (v_isSharedCheck_860_ == 0)
{
v___x_841_ = v_reader_832_;
v_isShared_842_ = v_isSharedCheck_860_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_headerBytesRead_838_);
lean_inc(v_bodyBytesRead_837_);
lean_inc(v_messageCount_836_);
lean_inc(v_messageHead_835_);
lean_inc(v_input_833_);
lean_inc(v_state_834_);
lean_dec(v_reader_832_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_860_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_array_843_; lean_object* v_idx_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_array_843_ = lean_ctor_get(v_input_833_, 0);
lean_inc_ref(v_array_843_);
v_idx_844_ = lean_ctor_get(v_input_833_, 1);
lean_inc(v_idx_844_);
lean_dec_ref(v_input_833_);
v___x_845_ = lean_byte_array_size(v_array_843_);
v___x_846_ = lean_nat_dec_le(v___x_845_, v_idx_844_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_847_ = l_ByteArray_extract(v_array_843_, v_idx_844_, v___x_845_);
lean_dec_ref(v_array_843_);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_byte_array_size(v___x_847_);
v___x_850_ = lean_byte_array_size(v_data_831_);
v___x_851_ = lean_byte_array_copy_slice(v_data_831_, v___x_848_, v___x_847_, v___x_849_, v___x_850_, v___x_846_);
lean_dec_ref(v_data_831_);
v___x_852_ = l_ByteArray_mkIterator(v___x_851_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_852_);
v___x_854_ = v___x_841_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_state_834_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_messageHead_835_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_messageCount_836_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_bodyBytesRead_837_);
lean_ctor_set(v_reuseFailAlloc_855_, 5, v_headerBytesRead_838_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*6, v_noMoreInput_839_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
else
{
lean_object* v___x_856_; lean_object* v___x_858_; 
lean_dec(v_idx_844_);
lean_dec_ref(v_array_843_);
v___x_856_ = l_ByteArray_mkIterator(v_data_831_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_856_);
v___x_858_ = v___x_841_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_state_834_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_messageHead_835_);
lean_ctor_set(v_reuseFailAlloc_859_, 3, v_messageCount_836_);
lean_ctor_set(v_reuseFailAlloc_859_, 4, v_bodyBytesRead_837_);
lean_ctor_set(v_reuseFailAlloc_859_, 5, v_headerBytesRead_838_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*6, v_noMoreInput_839_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed(uint8_t v_dir_861_, lean_object* v_data_862_, lean_object* v_reader_863_){
_start:
{
lean_object* v_input_864_; lean_object* v_state_865_; lean_object* v_messageHead_866_; lean_object* v_messageCount_867_; lean_object* v_bodyBytesRead_868_; lean_object* v_headerBytesRead_869_; uint8_t v_noMoreInput_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_891_; 
v_input_864_ = lean_ctor_get(v_reader_863_, 1);
v_state_865_ = lean_ctor_get(v_reader_863_, 0);
v_messageHead_866_ = lean_ctor_get(v_reader_863_, 2);
v_messageCount_867_ = lean_ctor_get(v_reader_863_, 3);
v_bodyBytesRead_868_ = lean_ctor_get(v_reader_863_, 4);
v_headerBytesRead_869_ = lean_ctor_get(v_reader_863_, 5);
v_noMoreInput_870_ = lean_ctor_get_uint8(v_reader_863_, sizeof(void*)*6);
v_isSharedCheck_891_ = !lean_is_exclusive(v_reader_863_);
if (v_isSharedCheck_891_ == 0)
{
v___x_872_ = v_reader_863_;
v_isShared_873_ = v_isSharedCheck_891_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_headerBytesRead_869_);
lean_inc(v_bodyBytesRead_868_);
lean_inc(v_messageCount_867_);
lean_inc(v_messageHead_866_);
lean_inc(v_input_864_);
lean_inc(v_state_865_);
lean_dec(v_reader_863_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_891_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_array_874_; lean_object* v_idx_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_array_874_ = lean_ctor_get(v_input_864_, 0);
lean_inc_ref(v_array_874_);
v_idx_875_ = lean_ctor_get(v_input_864_, 1);
lean_inc(v_idx_875_);
lean_dec_ref(v_input_864_);
v___x_876_ = lean_byte_array_size(v_array_874_);
v___x_877_ = lean_nat_dec_le(v___x_876_, v_idx_875_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_878_ = l_ByteArray_extract(v_array_874_, v_idx_875_, v___x_876_);
lean_dec_ref(v_array_874_);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_byte_array_size(v___x_878_);
v___x_881_ = lean_byte_array_size(v_data_862_);
v___x_882_ = lean_byte_array_copy_slice(v_data_862_, v___x_879_, v___x_878_, v___x_880_, v___x_881_, v___x_877_);
lean_dec_ref(v_data_862_);
v___x_883_ = l_ByteArray_mkIterator(v___x_882_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_883_);
v___x_885_ = v___x_872_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_state_865_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_messageHead_866_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_messageCount_867_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_bodyBytesRead_868_);
lean_ctor_set(v_reuseFailAlloc_886_, 5, v_headerBytesRead_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*6, v_noMoreInput_870_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_889_; 
lean_dec(v_idx_875_);
lean_dec_ref(v_array_874_);
v___x_887_ = l_ByteArray_mkIterator(v_data_862_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_887_);
v___x_889_ = v___x_872_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_state_865_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_messageHead_866_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v_messageCount_867_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v_bodyBytesRead_868_);
lean_ctor_set(v_reuseFailAlloc_890_, 5, v_headerBytesRead_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_890_, sizeof(void*)*6, v_noMoreInput_870_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___boxed(lean_object* v_dir_892_, lean_object* v_data_893_, lean_object* v_reader_894_){
_start:
{
uint8_t v_dir_boxed_895_; lean_object* v_res_896_; 
v_dir_boxed_895_ = lean_unbox(v_dir_892_);
v_res_896_ = l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_895_, v_data_893_, v_reader_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___redArg(lean_object* v_input_897_, lean_object* v_reader_898_){
_start:
{
lean_object* v_state_899_; lean_object* v_messageHead_900_; lean_object* v_messageCount_901_; lean_object* v_bodyBytesRead_902_; lean_object* v_headerBytesRead_903_; uint8_t v_noMoreInput_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_state_899_ = lean_ctor_get(v_reader_898_, 0);
v_messageHead_900_ = lean_ctor_get(v_reader_898_, 2);
v_messageCount_901_ = lean_ctor_get(v_reader_898_, 3);
v_bodyBytesRead_902_ = lean_ctor_get(v_reader_898_, 4);
v_headerBytesRead_903_ = lean_ctor_get(v_reader_898_, 5);
v_noMoreInput_904_ = lean_ctor_get_uint8(v_reader_898_, sizeof(void*)*6);
v_isSharedCheck_911_ = !lean_is_exclusive(v_reader_898_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v_reader_898_, 1);
lean_dec(v_unused_912_);
v___x_906_ = v_reader_898_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_headerBytesRead_903_);
lean_inc(v_bodyBytesRead_902_);
lean_inc(v_messageCount_901_);
lean_inc(v_messageHead_900_);
lean_inc(v_state_899_);
lean_dec(v_reader_898_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v_input_897_);
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_state_899_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_input_897_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_messageHead_900_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_messageCount_901_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_bodyBytesRead_902_);
lean_ctor_set(v_reuseFailAlloc_910_, 5, v_headerBytesRead_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_910_, sizeof(void*)*6, v_noMoreInput_904_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput(uint8_t v_dir_913_, lean_object* v_input_914_, lean_object* v_reader_915_){
_start:
{
lean_object* v_state_916_; lean_object* v_messageHead_917_; lean_object* v_messageCount_918_; lean_object* v_bodyBytesRead_919_; lean_object* v_headerBytesRead_920_; uint8_t v_noMoreInput_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_state_916_ = lean_ctor_get(v_reader_915_, 0);
v_messageHead_917_ = lean_ctor_get(v_reader_915_, 2);
v_messageCount_918_ = lean_ctor_get(v_reader_915_, 3);
v_bodyBytesRead_919_ = lean_ctor_get(v_reader_915_, 4);
v_headerBytesRead_920_ = lean_ctor_get(v_reader_915_, 5);
v_noMoreInput_921_ = lean_ctor_get_uint8(v_reader_915_, sizeof(void*)*6);
v_isSharedCheck_928_ = !lean_is_exclusive(v_reader_915_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_reader_915_, 1);
lean_dec(v_unused_929_);
v___x_923_ = v_reader_915_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_headerBytesRead_920_);
lean_inc(v_bodyBytesRead_919_);
lean_inc(v_messageCount_918_);
lean_inc(v_messageHead_917_);
lean_inc(v_state_916_);
lean_dec(v_reader_915_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v_input_914_);
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_state_916_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_input_914_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_messageHead_917_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_messageCount_918_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_bodyBytesRead_919_);
lean_ctor_set(v_reuseFailAlloc_927_, 5, v_headerBytesRead_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_927_, sizeof(void*)*6, v_noMoreInput_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___boxed(lean_object* v_dir_930_, lean_object* v_input_931_, lean_object* v_reader_932_){
_start:
{
uint8_t v_dir_boxed_933_; lean_object* v_res_934_; 
v_dir_boxed_933_ = lean_unbox(v_dir_930_);
v_res_934_ = l_Std_Http_Protocol_H1_Reader_setInput(v_dir_boxed_933_, v_input_931_, v_reader_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(lean_object* v_messageHead_935_, lean_object* v_reader_936_){
_start:
{
lean_object* v_state_937_; lean_object* v_input_938_; lean_object* v_messageCount_939_; lean_object* v_bodyBytesRead_940_; lean_object* v_headerBytesRead_941_; uint8_t v_noMoreInput_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_state_937_ = lean_ctor_get(v_reader_936_, 0);
v_input_938_ = lean_ctor_get(v_reader_936_, 1);
v_messageCount_939_ = lean_ctor_get(v_reader_936_, 3);
v_bodyBytesRead_940_ = lean_ctor_get(v_reader_936_, 4);
v_headerBytesRead_941_ = lean_ctor_get(v_reader_936_, 5);
v_noMoreInput_942_ = lean_ctor_get_uint8(v_reader_936_, sizeof(void*)*6);
v_isSharedCheck_949_ = !lean_is_exclusive(v_reader_936_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_reader_936_, 2);
lean_dec(v_unused_950_);
v___x_944_ = v_reader_936_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_headerBytesRead_941_);
lean_inc(v_bodyBytesRead_940_);
lean_inc(v_messageCount_939_);
lean_inc(v_input_938_);
lean_inc(v_state_937_);
lean_dec(v_reader_936_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 2, v_messageHead_935_);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_state_937_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_input_938_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_messageHead_935_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_messageCount_939_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_bodyBytesRead_940_);
lean_ctor_set(v_reuseFailAlloc_948_, 5, v_headerBytesRead_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*6, v_noMoreInput_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead(uint8_t v_dir_951_, lean_object* v_messageHead_952_, lean_object* v_reader_953_){
_start:
{
lean_object* v_state_954_; lean_object* v_input_955_; lean_object* v_messageCount_956_; lean_object* v_bodyBytesRead_957_; lean_object* v_headerBytesRead_958_; uint8_t v_noMoreInput_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_state_954_ = lean_ctor_get(v_reader_953_, 0);
v_input_955_ = lean_ctor_get(v_reader_953_, 1);
v_messageCount_956_ = lean_ctor_get(v_reader_953_, 3);
v_bodyBytesRead_957_ = lean_ctor_get(v_reader_953_, 4);
v_headerBytesRead_958_ = lean_ctor_get(v_reader_953_, 5);
v_noMoreInput_959_ = lean_ctor_get_uint8(v_reader_953_, sizeof(void*)*6);
v_isSharedCheck_966_ = !lean_is_exclusive(v_reader_953_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v_reader_953_, 2);
lean_dec(v_unused_967_);
v___x_961_ = v_reader_953_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_headerBytesRead_958_);
lean_inc(v_bodyBytesRead_957_);
lean_inc(v_messageCount_956_);
lean_inc(v_input_955_);
lean_inc(v_state_954_);
lean_dec(v_reader_953_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 2, v_messageHead_952_);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_state_954_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_input_955_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_messageHead_952_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_messageCount_956_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_bodyBytesRead_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 5, v_headerBytesRead_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*6, v_noMoreInput_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(lean_object* v_dir_968_, lean_object* v_messageHead_969_, lean_object* v_reader_970_){
_start:
{
uint8_t v_dir_boxed_971_; lean_object* v_res_972_; 
v_dir_boxed_971_ = lean_unbox(v_dir_968_);
v_res_972_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(v_dir_boxed_971_, v_messageHead_969_, v_reader_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___lam__0(lean_object* v_i_973_, lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_974_) == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_mk_empty_array_with_capacity(v___x_975_);
v___x_977_ = lean_array_push(v___x_976_, v_i_973_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
else
{
lean_object* v_val_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_val_979_ = lean_ctor_get(v_x_974_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v_x_974_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_val_979_);
lean_dec(v_x_974_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_array_push(v_val_979_, v_i_973_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader(uint8_t v_dir_990_, lean_object* v_name_991_, lean_object* v_value_992_, lean_object* v_reader_993_){
_start:
{
if (v_dir_990_ == 0)
{
lean_object* v_messageHead_994_; lean_object* v_state_995_; lean_object* v_input_996_; lean_object* v_messageCount_997_; lean_object* v_bodyBytesRead_998_; lean_object* v_headerBytesRead_999_; uint8_t v_noMoreInput_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1036_; 
v_messageHead_994_ = lean_ctor_get(v_reader_993_, 2);
v_state_995_ = lean_ctor_get(v_reader_993_, 0);
v_input_996_ = lean_ctor_get(v_reader_993_, 1);
v_messageCount_997_ = lean_ctor_get(v_reader_993_, 3);
v_bodyBytesRead_998_ = lean_ctor_get(v_reader_993_, 4);
v_headerBytesRead_999_ = lean_ctor_get(v_reader_993_, 5);
v_noMoreInput_1000_ = lean_ctor_get_uint8(v_reader_993_, sizeof(void*)*6);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_reader_993_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1002_ = v_reader_993_;
v_isShared_1003_ = v_isSharedCheck_1036_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_headerBytesRead_999_);
lean_inc(v_bodyBytesRead_998_);
lean_inc(v_messageCount_997_);
lean_inc(v_messageHead_994_);
lean_inc(v_input_996_);
lean_inc(v_state_995_);
lean_dec(v_reader_993_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1036_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
uint8_t v_method_1004_; uint8_t v_version_1005_; lean_object* v_uri_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1033_; 
v_method_1004_ = lean_ctor_get_uint8(v_messageHead_994_, sizeof(void*)*2);
v_version_1005_ = lean_ctor_get_uint8(v_messageHead_994_, sizeof(void*)*2 + 1);
v_uri_1006_ = lean_ctor_get(v_messageHead_994_, 0);
lean_inc(v_uri_1006_);
v___x_1007_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_990_, v_messageHead_994_);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_messageHead_994_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; lean_object* v_unused_1035_; 
v_unused_1034_ = lean_ctor_get(v_messageHead_994_, 1);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_messageHead_994_, 0);
lean_dec(v_unused_1035_);
v___x_1009_ = v_messageHead_994_;
v_isShared_1010_ = v_isSharedCheck_1033_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v_messageHead_994_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1033_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_entries_1011_; lean_object* v_indexes_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1032_; 
v_entries_1011_ = lean_ctor_get(v___x_1007_, 0);
v_indexes_1012_ = lean_ctor_get(v___x_1007_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1014_ = v___x_1007_;
v_isShared_1015_ = v_isSharedCheck_1032_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_indexes_1012_);
lean_inc(v_entries_1011_);
lean_dec(v___x_1007_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1032_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v_i_1018_; lean_object* v_f_1019_; lean_object* v___x_1020_; lean_object* v_entries_1021_; lean_object* v_indexes_1022_; lean_object* v___x_1024_; 
v___f_1016_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1017_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1018_ = lean_array_get_size(v_entries_1011_);
v_f_1019_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1019_, 0, v_i_1018_);
lean_inc_ref(v_name_991_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_name_991_);
lean_ctor_set(v___x_1020_, 1, v_value_992_);
v_entries_1021_ = lean_array_push(v_entries_1011_, v___x_1020_);
v_indexes_1022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1016_, v___f_1017_, v_indexes_1012_, v_name_991_, v_f_1019_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v_indexes_1022_);
lean_ctor_set(v___x_1014_, 0, v_entries_1021_);
v___x_1024_ = v___x_1014_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_entries_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_indexes_1022_);
v___x_1024_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1024_);
v___x_1026_ = v___x_1009_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_uri_1006_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___x_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1030_, sizeof(void*)*2, v_method_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1030_, sizeof(void*)*2 + 1, v_version_1005_);
v___x_1026_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1028_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 2, v___x_1026_);
v___x_1028_ = v___x_1002_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_state_995_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_input_996_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_messageCount_997_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_bodyBytesRead_998_);
lean_ctor_set(v_reuseFailAlloc_1029_, 5, v_headerBytesRead_999_);
lean_ctor_set_uint8(v_reuseFailAlloc_1029_, sizeof(void*)*6, v_noMoreInput_1000_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
}
else
{
lean_object* v_messageHead_1037_; lean_object* v_state_1038_; lean_object* v_input_1039_; lean_object* v_messageCount_1040_; lean_object* v_bodyBytesRead_1041_; lean_object* v_headerBytesRead_1042_; uint8_t v_noMoreInput_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1078_; 
v_messageHead_1037_ = lean_ctor_get(v_reader_993_, 2);
v_state_1038_ = lean_ctor_get(v_reader_993_, 0);
v_input_1039_ = lean_ctor_get(v_reader_993_, 1);
v_messageCount_1040_ = lean_ctor_get(v_reader_993_, 3);
v_bodyBytesRead_1041_ = lean_ctor_get(v_reader_993_, 4);
v_headerBytesRead_1042_ = lean_ctor_get(v_reader_993_, 5);
v_noMoreInput_1043_ = lean_ctor_get_uint8(v_reader_993_, sizeof(void*)*6);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_reader_993_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1045_ = v_reader_993_;
v_isShared_1046_ = v_isSharedCheck_1078_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_headerBytesRead_1042_);
lean_inc(v_bodyBytesRead_1041_);
lean_inc(v_messageCount_1040_);
lean_inc(v_messageHead_1037_);
lean_inc(v_input_1039_);
lean_inc(v_state_1038_);
lean_dec(v_reader_993_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1078_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v_status_1047_; uint8_t v_version_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1075_; 
v_status_1047_ = lean_ctor_get(v_messageHead_1037_, 0);
lean_inc(v_status_1047_);
v_version_1048_ = lean_ctor_get_uint8(v_messageHead_1037_, sizeof(void*)*2);
v___x_1049_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_990_, v_messageHead_1037_);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_messageHead_1037_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; lean_object* v_unused_1077_; 
v_unused_1076_ = lean_ctor_get(v_messageHead_1037_, 1);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_messageHead_1037_, 0);
lean_dec(v_unused_1077_);
v___x_1051_ = v_messageHead_1037_;
v_isShared_1052_ = v_isSharedCheck_1075_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v_messageHead_1037_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1075_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_entries_1053_; lean_object* v_indexes_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1074_; 
v_entries_1053_ = lean_ctor_get(v___x_1049_, 0);
v_indexes_1054_ = lean_ctor_get(v___x_1049_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1056_ = v___x_1049_;
v_isShared_1057_ = v_isSharedCheck_1074_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_indexes_1054_);
lean_inc(v_entries_1053_);
lean_dec(v___x_1049_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1074_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v_i_1060_; lean_object* v_f_1061_; lean_object* v___x_1062_; lean_object* v_entries_1063_; lean_object* v_indexes_1064_; lean_object* v___x_1066_; 
v___f_1058_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1059_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1060_ = lean_array_get_size(v_entries_1053_);
v_f_1061_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1061_, 0, v_i_1060_);
lean_inc_ref(v_name_991_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_name_991_);
lean_ctor_set(v___x_1062_, 1, v_value_992_);
v_entries_1063_ = lean_array_push(v_entries_1053_, v___x_1062_);
v_indexes_1064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1058_, v___f_1059_, v_indexes_1054_, v_name_991_, v_f_1061_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v_indexes_1064_);
lean_ctor_set(v___x_1056_, 0, v_entries_1063_);
v___x_1066_ = v___x_1056_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_entries_1063_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_indexes_1064_);
v___x_1066_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1066_);
v___x_1068_ = v___x_1051_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_status_1047_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1066_);
lean_ctor_set_uint8(v_reuseFailAlloc_1072_, sizeof(void*)*2, v_version_1048_);
v___x_1068_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 2, v___x_1068_);
v___x_1070_ = v___x_1045_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_state_1038_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_input_1039_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v_messageCount_1040_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v_bodyBytesRead_1041_);
lean_ctor_set(v_reuseFailAlloc_1071_, 5, v_headerBytesRead_1042_);
lean_ctor_set_uint8(v_reuseFailAlloc_1071_, sizeof(void*)*6, v_noMoreInput_1043_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___boxed(lean_object* v_dir_1079_, lean_object* v_name_1080_, lean_object* v_value_1081_, lean_object* v_reader_1082_){
_start:
{
uint8_t v_dir_boxed_1083_; lean_object* v_res_1084_; 
v_dir_boxed_1083_ = lean_unbox(v_dir_1079_);
v_res_1084_ = l_Std_Http_Protocol_H1_Reader_addHeader(v_dir_boxed_1083_, v_name_1080_, v_value_1081_, v_reader_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___redArg(lean_object* v_reader_1085_){
_start:
{
lean_object* v_input_1086_; lean_object* v_messageHead_1087_; lean_object* v_messageCount_1088_; lean_object* v_bodyBytesRead_1089_; lean_object* v_headerBytesRead_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
v_input_1086_ = lean_ctor_get(v_reader_1085_, 1);
v_messageHead_1087_ = lean_ctor_get(v_reader_1085_, 2);
v_messageCount_1088_ = lean_ctor_get(v_reader_1085_, 3);
v_bodyBytesRead_1089_ = lean_ctor_get(v_reader_1085_, 4);
v_headerBytesRead_1090_ = lean_ctor_get(v_reader_1085_, 5);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_reader_1085_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v_reader_1085_, 0);
lean_dec(v_unused_1100_);
v___x_1092_ = v_reader_1085_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_headerBytesRead_1090_);
lean_inc(v_bodyBytesRead_1089_);
lean_inc(v_messageCount_1088_);
lean_inc(v_messageHead_1087_);
lean_inc(v_input_1086_);
lean_dec(v_reader_1085_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1097_; 
v___x_1094_ = lean_box(6);
v___x_1095_ = 1;
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_input_1086_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_messageHead_1087_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_messageCount_1088_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v_bodyBytesRead_1089_);
lean_ctor_set(v_reuseFailAlloc_1098_, 5, v_headerBytesRead_1090_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*6, v___x_1095_);
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close(uint8_t v_dir_1101_, lean_object* v_reader_1102_){
_start:
{
lean_object* v_input_1103_; lean_object* v_messageHead_1104_; lean_object* v_messageCount_1105_; lean_object* v_bodyBytesRead_1106_; lean_object* v_headerBytesRead_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1116_; 
v_input_1103_ = lean_ctor_get(v_reader_1102_, 1);
v_messageHead_1104_ = lean_ctor_get(v_reader_1102_, 2);
v_messageCount_1105_ = lean_ctor_get(v_reader_1102_, 3);
v_bodyBytesRead_1106_ = lean_ctor_get(v_reader_1102_, 4);
v_headerBytesRead_1107_ = lean_ctor_get(v_reader_1102_, 5);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_reader_1102_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v_reader_1102_, 0);
lean_dec(v_unused_1117_);
v___x_1109_ = v_reader_1102_;
v_isShared_1110_ = v_isSharedCheck_1116_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_headerBytesRead_1107_);
lean_inc(v_bodyBytesRead_1106_);
lean_inc(v_messageCount_1105_);
lean_inc(v_messageHead_1104_);
lean_inc(v_input_1103_);
lean_dec(v_reader_1102_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1116_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1114_; 
v___x_1111_ = lean_box(6);
v___x_1112_ = 1;
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1111_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_input_1103_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_messageHead_1104_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_messageCount_1105_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_bodyBytesRead_1106_);
lean_ctor_set(v_reuseFailAlloc_1115_, 5, v_headerBytesRead_1107_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*6, v___x_1112_);
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___boxed(lean_object* v_dir_1118_, lean_object* v_reader_1119_){
_start:
{
uint8_t v_dir_boxed_1120_; lean_object* v_res_1121_; 
v_dir_boxed_1120_ = lean_unbox(v_dir_1118_);
v_res_1121_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_boxed_1120_, v_reader_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object* v_reader_1122_){
_start:
{
lean_object* v_input_1123_; lean_object* v_messageHead_1124_; lean_object* v_messageCount_1125_; lean_object* v_bodyBytesRead_1126_; lean_object* v_headerBytesRead_1127_; uint8_t v_noMoreInput_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1138_; 
v_input_1123_ = lean_ctor_get(v_reader_1122_, 1);
v_messageHead_1124_ = lean_ctor_get(v_reader_1122_, 2);
v_messageCount_1125_ = lean_ctor_get(v_reader_1122_, 3);
v_bodyBytesRead_1126_ = lean_ctor_get(v_reader_1122_, 4);
v_headerBytesRead_1127_ = lean_ctor_get(v_reader_1122_, 5);
v_noMoreInput_1128_ = lean_ctor_get_uint8(v_reader_1122_, sizeof(void*)*6);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_reader_1122_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v_reader_1122_, 0);
lean_dec(v_unused_1139_);
v___x_1130_ = v_reader_1122_;
v_isShared_1131_ = v_isSharedCheck_1138_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_headerBytesRead_1127_);
lean_inc(v_bodyBytesRead_1126_);
lean_inc(v_messageCount_1125_);
lean_inc(v_messageHead_1124_);
lean_inc(v_input_1123_);
lean_dec(v_reader_1122_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1138_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1132_ = lean_box(5);
v___x_1133_ = lean_unsigned_to_nat(1u);
v___x_1134_ = lean_nat_add(v_messageCount_1125_, v___x_1133_);
lean_dec(v_messageCount_1125_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 3, v___x_1134_);
lean_ctor_set(v___x_1130_, 0, v___x_1132_);
v___x_1136_ = v___x_1130_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_input_1123_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_messageHead_1124_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_bodyBytesRead_1126_);
lean_ctor_set(v_reuseFailAlloc_1137_, 5, v_headerBytesRead_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1137_, sizeof(void*)*6, v_noMoreInput_1128_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t v_dir_1140_, lean_object* v_reader_1141_){
_start:
{
lean_object* v_input_1142_; lean_object* v_messageHead_1143_; lean_object* v_messageCount_1144_; lean_object* v_bodyBytesRead_1145_; lean_object* v_headerBytesRead_1146_; uint8_t v_noMoreInput_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1157_; 
v_input_1142_ = lean_ctor_get(v_reader_1141_, 1);
v_messageHead_1143_ = lean_ctor_get(v_reader_1141_, 2);
v_messageCount_1144_ = lean_ctor_get(v_reader_1141_, 3);
v_bodyBytesRead_1145_ = lean_ctor_get(v_reader_1141_, 4);
v_headerBytesRead_1146_ = lean_ctor_get(v_reader_1141_, 5);
v_noMoreInput_1147_ = lean_ctor_get_uint8(v_reader_1141_, sizeof(void*)*6);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_reader_1141_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_reader_1141_, 0);
lean_dec(v_unused_1158_);
v___x_1149_ = v_reader_1141_;
v_isShared_1150_ = v_isSharedCheck_1157_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_headerBytesRead_1146_);
lean_inc(v_bodyBytesRead_1145_);
lean_inc(v_messageCount_1144_);
lean_inc(v_messageHead_1143_);
lean_inc(v_input_1142_);
lean_dec(v_reader_1141_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1157_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1151_ = lean_box(5);
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_nat_add(v_messageCount_1144_, v___x_1152_);
lean_dec(v_messageCount_1144_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 3, v___x_1153_);
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1155_ = v___x_1149_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_input_1142_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_messageHead_1143_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_bodyBytesRead_1145_);
lean_ctor_set(v_reuseFailAlloc_1156_, 5, v_headerBytesRead_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1156_, sizeof(void*)*6, v_noMoreInput_1147_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___boxed(lean_object* v_dir_1159_, lean_object* v_reader_1160_){
_start:
{
uint8_t v_dir_boxed_1161_; lean_object* v_res_1162_; 
v_dir_boxed_1161_ = lean_unbox(v_dir_1159_);
v_res_1162_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_boxed_1161_, v_reader_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___redArg(lean_object* v_error_1163_, lean_object* v_reader_1164_){
_start:
{
lean_object* v_input_1165_; lean_object* v_messageHead_1166_; lean_object* v_messageCount_1167_; lean_object* v_bodyBytesRead_1168_; lean_object* v_headerBytesRead_1169_; uint8_t v_noMoreInput_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
v_input_1165_ = lean_ctor_get(v_reader_1164_, 1);
v_messageHead_1166_ = lean_ctor_get(v_reader_1164_, 2);
v_messageCount_1167_ = lean_ctor_get(v_reader_1164_, 3);
v_bodyBytesRead_1168_ = lean_ctor_get(v_reader_1164_, 4);
v_headerBytesRead_1169_ = lean_ctor_get(v_reader_1164_, 5);
v_noMoreInput_1170_ = lean_ctor_get_uint8(v_reader_1164_, sizeof(void*)*6);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_reader_1164_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v_reader_1164_, 0);
lean_dec(v_unused_1179_);
v___x_1172_ = v_reader_1164_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_headerBytesRead_1169_);
lean_inc(v_bodyBytesRead_1168_);
lean_inc(v_messageCount_1167_);
lean_inc(v_messageHead_1166_);
lean_inc(v_input_1165_);
lean_dec(v_reader_1164_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_error_1163_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_input_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_messageHead_1166_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_messageCount_1167_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_bodyBytesRead_1168_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_headerBytesRead_1169_);
lean_ctor_set_uint8(v_reuseFailAlloc_1177_, sizeof(void*)*6, v_noMoreInput_1170_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail(uint8_t v_dir_1180_, lean_object* v_error_1181_, lean_object* v_reader_1182_){
_start:
{
lean_object* v_input_1183_; lean_object* v_messageHead_1184_; lean_object* v_messageCount_1185_; lean_object* v_bodyBytesRead_1186_; lean_object* v_headerBytesRead_1187_; uint8_t v_noMoreInput_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
v_input_1183_ = lean_ctor_get(v_reader_1182_, 1);
v_messageHead_1184_ = lean_ctor_get(v_reader_1182_, 2);
v_messageCount_1185_ = lean_ctor_get(v_reader_1182_, 3);
v_bodyBytesRead_1186_ = lean_ctor_get(v_reader_1182_, 4);
v_headerBytesRead_1187_ = lean_ctor_get(v_reader_1182_, 5);
v_noMoreInput_1188_ = lean_ctor_get_uint8(v_reader_1182_, sizeof(void*)*6);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_reader_1182_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v_reader_1182_, 0);
lean_dec(v_unused_1197_);
v___x_1190_ = v_reader_1182_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_headerBytesRead_1187_);
lean_inc(v_bodyBytesRead_1186_);
lean_inc(v_messageCount_1185_);
lean_inc(v_messageHead_1184_);
lean_inc(v_input_1183_);
lean_dec(v_reader_1182_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_error_1181_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_input_1183_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_messageHead_1184_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_messageCount_1185_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v_bodyBytesRead_1186_);
lean_ctor_set(v_reuseFailAlloc_1195_, 5, v_headerBytesRead_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1195_, sizeof(void*)*6, v_noMoreInput_1188_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___boxed(lean_object* v_dir_1198_, lean_object* v_error_1199_, lean_object* v_reader_1200_){
_start:
{
uint8_t v_dir_boxed_1201_; lean_object* v_res_1202_; 
v_dir_boxed_1201_ = lean_unbox(v_dir_1198_);
v_res_1202_ = l_Std_Http_Protocol_H1_Reader_fail(v_dir_boxed_1201_, v_error_1199_, v_reader_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t v_dir_1203_, lean_object* v_reader_1204_){
_start:
{
lean_object* v_input_1205_; lean_object* v_messageCount_1206_; uint8_t v_noMoreInput_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1217_; 
v_input_1205_ = lean_ctor_get(v_reader_1204_, 1);
v_messageCount_1206_ = lean_ctor_get(v_reader_1204_, 3);
v_noMoreInput_1207_ = lean_ctor_get_uint8(v_reader_1204_, sizeof(void*)*6);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_reader_1204_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; lean_object* v_unused_1219_; lean_object* v_unused_1220_; lean_object* v_unused_1221_; 
v_unused_1218_ = lean_ctor_get(v_reader_1204_, 5);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_reader_1204_, 4);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_reader_1204_, 2);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_reader_1204_, 0);
lean_dec(v_unused_1221_);
v___x_1209_ = v_reader_1204_;
v_isShared_1210_ = v_isSharedCheck_1217_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_messageCount_1206_);
lean_inc(v_input_1205_);
lean_dec(v_reader_1204_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1217_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_1203_);
v___x_1213_ = lean_unsigned_to_nat(0u);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 5, v___x_1213_);
lean_ctor_set(v___x_1209_, 4, v___x_1213_);
lean_ctor_set(v___x_1209_, 2, v___x_1212_);
lean_ctor_set(v___x_1209_, 0, v___x_1211_);
v___x_1215_ = v___x_1209_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_input_1205_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_messageCount_1206_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1216_, 5, v___x_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*6, v_noMoreInput_1207_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object* v_dir_1222_, lean_object* v_reader_1223_){
_start:
{
uint8_t v_dir_boxed_1224_; lean_object* v_res_1225_; 
v_dir_boxed_1224_ = lean_unbox(v_dir_1222_);
v_res_1225_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_1224_, v_reader_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object* v_reader_1226_){
_start:
{
lean_object* v_input_1227_; lean_object* v_state_1228_; uint8_t v_noMoreInput_1229_; lean_object* v_array_1230_; lean_object* v_idx_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_input_1227_ = lean_ctor_get(v_reader_1226_, 1);
v_state_1228_ = lean_ctor_get(v_reader_1226_, 0);
v_noMoreInput_1229_ = lean_ctor_get_uint8(v_reader_1226_, sizeof(void*)*6);
v_array_1230_ = lean_ctor_get(v_input_1227_, 0);
v_idx_1231_ = lean_ctor_get(v_input_1227_, 1);
v___x_1232_ = lean_byte_array_size(v_array_1230_);
v___x_1233_ = lean_nat_dec_le(v___x_1232_, v_idx_1231_);
if (v___x_1233_ == 0)
{
return v___x_1233_;
}
else
{
if (v_noMoreInput_1229_ == 0)
{
switch(lean_obj_tag(v_state_1228_))
{
case 5:
{
return v_noMoreInput_1229_;
}
case 6:
{
return v_noMoreInput_1229_;
}
case 7:
{
return v_noMoreInput_1229_;
}
case 3:
{
return v_noMoreInput_1229_;
}
default: 
{
return v___x_1233_;
}
}
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object* v_reader_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_1235_);
lean_dec_ref(v_reader_1235_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t v_dir_1238_, lean_object* v_reader_1239_){
_start:
{
lean_object* v_input_1240_; lean_object* v_state_1241_; uint8_t v_noMoreInput_1242_; lean_object* v_array_1243_; lean_object* v_idx_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_input_1240_ = lean_ctor_get(v_reader_1239_, 1);
v_state_1241_ = lean_ctor_get(v_reader_1239_, 0);
v_noMoreInput_1242_ = lean_ctor_get_uint8(v_reader_1239_, sizeof(void*)*6);
v_array_1243_ = lean_ctor_get(v_input_1240_, 0);
v_idx_1244_ = lean_ctor_get(v_input_1240_, 1);
v___x_1245_ = lean_byte_array_size(v_array_1243_);
v___x_1246_ = lean_nat_dec_le(v___x_1245_, v_idx_1244_);
if (v___x_1246_ == 0)
{
return v___x_1246_;
}
else
{
if (v_noMoreInput_1242_ == 0)
{
switch(lean_obj_tag(v_state_1241_))
{
case 5:
{
return v_noMoreInput_1242_;
}
case 6:
{
return v_noMoreInput_1242_;
}
case 7:
{
return v_noMoreInput_1242_;
}
case 3:
{
return v_noMoreInput_1242_;
}
default: 
{
return v___x_1246_;
}
}
}
else
{
uint8_t v___x_1247_; 
v___x_1247_ = 0;
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object* v_dir_1248_, lean_object* v_reader_1249_){
_start:
{
uint8_t v_dir_boxed_1250_; uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_dir_boxed_1250_ = lean_unbox(v_dir_1248_);
v_res_1251_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_1250_, v_reader_1249_);
lean_dec_ref(v_reader_1249_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___redArg(lean_object* v_reader_1253_){
_start:
{
lean_object* v_state_1254_; 
v_state_1254_ = lean_ctor_get(v_reader_1253_, 0);
lean_inc(v_state_1254_);
lean_dec_ref(v_reader_1253_);
if (lean_obj_tag(v_state_1254_) == 7)
{
lean_object* v_error_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_error_1255_ = lean_ctor_get(v_state_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_state_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v_state_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_error_1255_);
lean_dec(v_state_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_error_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v___x_1263_; 
lean_dec(v_state_1254_);
v___x_1263_ = lean_box(0);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError(uint8_t v_dir_1264_, lean_object* v_reader_1265_){
_start:
{
lean_object* v_state_1266_; 
v_state_1266_ = lean_ctor_get(v_reader_1265_, 0);
lean_inc(v_state_1266_);
lean_dec_ref(v_reader_1265_);
if (lean_obj_tag(v_state_1266_) == 7)
{
lean_object* v_error_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_error_1267_ = lean_ctor_get(v_state_1266_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_state_1266_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v_state_1266_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_error_1267_);
lean_dec(v_state_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 1);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_error_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_state_1266_);
v___x_1275_ = lean_box(0);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___boxed(lean_object* v_dir_1276_, lean_object* v_reader_1277_){
_start:
{
uint8_t v_dir_boxed_1278_; lean_object* v_res_1279_; 
v_dir_boxed_1278_ = lean_unbox(v_dir_1276_);
v_res_1279_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_boxed_1278_, v_reader_1277_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(lean_object* v_reader_1280_){
_start:
{
lean_object* v_input_1281_; lean_object* v_array_1282_; lean_object* v_idx_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_input_1281_ = lean_ctor_get(v_reader_1280_, 1);
v_array_1282_ = lean_ctor_get(v_input_1281_, 0);
v_idx_1283_ = lean_ctor_get(v_input_1281_, 1);
v___x_1284_ = lean_byte_array_size(v_array_1282_);
v___x_1285_ = lean_nat_sub(v___x_1284_, v_idx_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(lean_object* v_reader_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_1286_);
lean_dec_ref(v_reader_1286_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes(uint8_t v_dir_1288_, lean_object* v_reader_1289_){
_start:
{
lean_object* v_input_1290_; lean_object* v_array_1291_; lean_object* v_idx_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_input_1290_ = lean_ctor_get(v_reader_1289_, 1);
v_array_1291_ = lean_ctor_get(v_input_1290_, 0);
v_idx_1292_ = lean_ctor_get(v_input_1290_, 1);
v___x_1293_ = lean_byte_array_size(v_array_1291_);
v___x_1294_ = lean_nat_sub(v___x_1293_, v_idx_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(lean_object* v_dir_1295_, lean_object* v_reader_1296_){
_start:
{
uint8_t v_dir_boxed_1297_; lean_object* v_res_1298_; 
v_dir_boxed_1297_ = lean_unbox(v_dir_1295_);
v_res_1298_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_1297_, v_reader_1296_);
lean_dec_ref(v_reader_1296_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg(lean_object* v_n_1299_, lean_object* v_reader_1300_){
_start:
{
lean_object* v_input_1301_; lean_object* v_state_1302_; lean_object* v_messageHead_1303_; lean_object* v_messageCount_1304_; lean_object* v_bodyBytesRead_1305_; lean_object* v_headerBytesRead_1306_; uint8_t v_noMoreInput_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1324_; 
v_input_1301_ = lean_ctor_get(v_reader_1300_, 1);
v_state_1302_ = lean_ctor_get(v_reader_1300_, 0);
v_messageHead_1303_ = lean_ctor_get(v_reader_1300_, 2);
v_messageCount_1304_ = lean_ctor_get(v_reader_1300_, 3);
v_bodyBytesRead_1305_ = lean_ctor_get(v_reader_1300_, 4);
v_headerBytesRead_1306_ = lean_ctor_get(v_reader_1300_, 5);
v_noMoreInput_1307_ = lean_ctor_get_uint8(v_reader_1300_, sizeof(void*)*6);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_reader_1300_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1309_ = v_reader_1300_;
v_isShared_1310_ = v_isSharedCheck_1324_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_headerBytesRead_1306_);
lean_inc(v_bodyBytesRead_1305_);
lean_inc(v_messageCount_1304_);
lean_inc(v_messageHead_1303_);
lean_inc(v_input_1301_);
lean_inc(v_state_1302_);
lean_dec(v_reader_1300_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1324_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_array_1311_; lean_object* v_idx_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1323_; 
v_array_1311_ = lean_ctor_get(v_input_1301_, 0);
v_idx_1312_ = lean_ctor_get(v_input_1301_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_input_1301_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1314_ = v_input_1301_;
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_idx_1312_);
lean_inc(v_array_1311_);
lean_dec(v_input_1301_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_nat_add(v_idx_1312_, v_n_1299_);
lean_dec(v_idx_1312_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 1, v___x_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_array_1311_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1320_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v___x_1318_);
v___x_1320_ = v___x_1309_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_state_1302_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_messageHead_1303_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_messageCount_1304_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_bodyBytesRead_1305_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_headerBytesRead_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1321_, sizeof(void*)*6, v_noMoreInput_1307_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(lean_object* v_n_1325_, lean_object* v_reader_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_1325_, v_reader_1326_);
lean_dec(v_n_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance(uint8_t v_dir_1328_, lean_object* v_n_1329_, lean_object* v_reader_1330_){
_start:
{
lean_object* v_input_1331_; lean_object* v_state_1332_; lean_object* v_messageHead_1333_; lean_object* v_messageCount_1334_; lean_object* v_bodyBytesRead_1335_; lean_object* v_headerBytesRead_1336_; uint8_t v_noMoreInput_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1354_; 
v_input_1331_ = lean_ctor_get(v_reader_1330_, 1);
v_state_1332_ = lean_ctor_get(v_reader_1330_, 0);
v_messageHead_1333_ = lean_ctor_get(v_reader_1330_, 2);
v_messageCount_1334_ = lean_ctor_get(v_reader_1330_, 3);
v_bodyBytesRead_1335_ = lean_ctor_get(v_reader_1330_, 4);
v_headerBytesRead_1336_ = lean_ctor_get(v_reader_1330_, 5);
v_noMoreInput_1337_ = lean_ctor_get_uint8(v_reader_1330_, sizeof(void*)*6);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_reader_1330_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1339_ = v_reader_1330_;
v_isShared_1340_ = v_isSharedCheck_1354_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_headerBytesRead_1336_);
lean_inc(v_bodyBytesRead_1335_);
lean_inc(v_messageCount_1334_);
lean_inc(v_messageHead_1333_);
lean_inc(v_input_1331_);
lean_inc(v_state_1332_);
lean_dec(v_reader_1330_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1354_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_array_1341_; lean_object* v_idx_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1353_; 
v_array_1341_ = lean_ctor_get(v_input_1331_, 0);
v_idx_1342_ = lean_ctor_get(v_input_1331_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_input_1331_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1344_ = v_input_1331_;
v_isShared_1345_ = v_isSharedCheck_1353_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_idx_1342_);
lean_inc(v_array_1341_);
lean_dec(v_input_1331_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1353_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_nat_add(v_idx_1342_, v_n_1329_);
lean_dec(v_idx_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_array_1341_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1348_);
v___x_1350_ = v___x_1339_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_state_1332_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_messageHead_1333_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_messageCount_1334_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_bodyBytesRead_1335_);
lean_ctor_set(v_reuseFailAlloc_1351_, 5, v_headerBytesRead_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*6, v_noMoreInput_1337_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___boxed(lean_object* v_dir_1355_, lean_object* v_n_1356_, lean_object* v_reader_1357_){
_start:
{
uint8_t v_dir_boxed_1358_; lean_object* v_res_1359_; 
v_dir_boxed_1358_ = lean_unbox(v_dir_1355_);
v_res_1359_ = l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_1358_, v_n_1356_, v_reader_1357_);
lean_dec(v_n_1356_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(lean_object* v_reader_1362_){
_start:
{
lean_object* v_input_1363_; lean_object* v_messageHead_1364_; lean_object* v_messageCount_1365_; uint8_t v_noMoreInput_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1375_; 
v_input_1363_ = lean_ctor_get(v_reader_1362_, 1);
v_messageHead_1364_ = lean_ctor_get(v_reader_1362_, 2);
v_messageCount_1365_ = lean_ctor_get(v_reader_1362_, 3);
v_noMoreInput_1366_ = lean_ctor_get_uint8(v_reader_1362_, sizeof(void*)*6);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_reader_1362_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; 
v_unused_1376_ = lean_ctor_get(v_reader_1362_, 5);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_reader_1362_, 4);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_reader_1362_, 0);
lean_dec(v_unused_1378_);
v___x_1368_ = v_reader_1362_;
v_isShared_1369_ = v_isSharedCheck_1375_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_messageCount_1365_);
lean_inc(v_messageHead_1364_);
lean_inc(v_input_1363_);
lean_dec(v_reader_1362_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1375_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 5, v___x_1370_);
lean_ctor_set(v___x_1368_, 4, v___x_1370_);
lean_ctor_set(v___x_1368_, 0, v___x_1371_);
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_input_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_messageHead_1364_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_messageCount_1365_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1374_, 5, v___x_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*6, v_noMoreInput_1366_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders(uint8_t v_dir_1379_, lean_object* v_reader_1380_){
_start:
{
lean_object* v_input_1381_; lean_object* v_messageHead_1382_; lean_object* v_messageCount_1383_; uint8_t v_noMoreInput_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1393_; 
v_input_1381_ = lean_ctor_get(v_reader_1380_, 1);
v_messageHead_1382_ = lean_ctor_get(v_reader_1380_, 2);
v_messageCount_1383_ = lean_ctor_get(v_reader_1380_, 3);
v_noMoreInput_1384_ = lean_ctor_get_uint8(v_reader_1380_, sizeof(void*)*6);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_reader_1380_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; lean_object* v_unused_1395_; lean_object* v_unused_1396_; 
v_unused_1394_ = lean_ctor_get(v_reader_1380_, 5);
lean_dec(v_unused_1394_);
v_unused_1395_ = lean_ctor_get(v_reader_1380_, 4);
lean_dec(v_unused_1395_);
v_unused_1396_ = lean_ctor_get(v_reader_1380_, 0);
lean_dec(v_unused_1396_);
v___x_1386_ = v_reader_1380_;
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_messageCount_1383_);
lean_inc(v_messageHead_1382_);
lean_inc(v_input_1381_);
lean_dec(v_reader_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 5, v___x_1388_);
lean_ctor_set(v___x_1386_, 4, v___x_1388_);
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_input_1381_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_messageHead_1382_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_messageCount_1383_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1392_, 5, v___x_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1392_, sizeof(void*)*6, v_noMoreInput_1384_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(lean_object* v_dir_1397_, lean_object* v_reader_1398_){
_start:
{
uint8_t v_dir_boxed_1399_; lean_object* v_res_1400_; 
v_dir_boxed_1399_ = lean_unbox(v_dir_1397_);
v_res_1400_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_1399_, v_reader_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(lean_object* v_n_1401_, lean_object* v_reader_1402_){
_start:
{
lean_object* v_state_1403_; lean_object* v_input_1404_; lean_object* v_messageHead_1405_; lean_object* v_messageCount_1406_; lean_object* v_bodyBytesRead_1407_; lean_object* v_headerBytesRead_1408_; uint8_t v_noMoreInput_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1417_; 
v_state_1403_ = lean_ctor_get(v_reader_1402_, 0);
v_input_1404_ = lean_ctor_get(v_reader_1402_, 1);
v_messageHead_1405_ = lean_ctor_get(v_reader_1402_, 2);
v_messageCount_1406_ = lean_ctor_get(v_reader_1402_, 3);
v_bodyBytesRead_1407_ = lean_ctor_get(v_reader_1402_, 4);
v_headerBytesRead_1408_ = lean_ctor_get(v_reader_1402_, 5);
v_noMoreInput_1409_ = lean_ctor_get_uint8(v_reader_1402_, sizeof(void*)*6);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_reader_1402_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1411_ = v_reader_1402_;
v_isShared_1412_ = v_isSharedCheck_1417_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_headerBytesRead_1408_);
lean_inc(v_bodyBytesRead_1407_);
lean_inc(v_messageCount_1406_);
lean_inc(v_messageHead_1405_);
lean_inc(v_input_1404_);
lean_inc(v_state_1403_);
lean_dec(v_reader_1402_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1417_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = lean_nat_add(v_bodyBytesRead_1407_, v_n_1401_);
lean_dec(v_bodyBytesRead_1407_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 4, v___x_1413_);
v___x_1415_ = v___x_1411_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_state_1403_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_input_1404_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_messageHead_1405_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_messageCount_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1416_, 5, v_headerBytesRead_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1416_, sizeof(void*)*6, v_noMoreInput_1409_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(lean_object* v_n_1418_, lean_object* v_reader_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_1418_, v_reader_1419_);
lean_dec(v_n_1418_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes(uint8_t v_dir_1421_, lean_object* v_n_1422_, lean_object* v_reader_1423_){
_start:
{
lean_object* v_state_1424_; lean_object* v_input_1425_; lean_object* v_messageHead_1426_; lean_object* v_messageCount_1427_; lean_object* v_bodyBytesRead_1428_; lean_object* v_headerBytesRead_1429_; uint8_t v_noMoreInput_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1438_; 
v_state_1424_ = lean_ctor_get(v_reader_1423_, 0);
v_input_1425_ = lean_ctor_get(v_reader_1423_, 1);
v_messageHead_1426_ = lean_ctor_get(v_reader_1423_, 2);
v_messageCount_1427_ = lean_ctor_get(v_reader_1423_, 3);
v_bodyBytesRead_1428_ = lean_ctor_get(v_reader_1423_, 4);
v_headerBytesRead_1429_ = lean_ctor_get(v_reader_1423_, 5);
v_noMoreInput_1430_ = lean_ctor_get_uint8(v_reader_1423_, sizeof(void*)*6);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_reader_1423_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1432_ = v_reader_1423_;
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_headerBytesRead_1429_);
lean_inc(v_bodyBytesRead_1428_);
lean_inc(v_messageCount_1427_);
lean_inc(v_messageHead_1426_);
lean_inc(v_input_1425_);
lean_inc(v_state_1424_);
lean_dec(v_reader_1423_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_nat_add(v_bodyBytesRead_1428_, v_n_1422_);
lean_dec(v_bodyBytesRead_1428_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_state_1424_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_input_1425_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_messageHead_1426_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_messageCount_1427_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1437_, 5, v_headerBytesRead_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1437_, sizeof(void*)*6, v_noMoreInput_1430_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(lean_object* v_dir_1439_, lean_object* v_n_1440_, lean_object* v_reader_1441_){
_start:
{
uint8_t v_dir_boxed_1442_; lean_object* v_res_1443_; 
v_dir_boxed_1442_ = lean_unbox(v_dir_1439_);
v_res_1443_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_1442_, v_n_1440_, v_reader_1441_);
lean_dec(v_n_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(lean_object* v_n_1444_, lean_object* v_reader_1445_){
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
v___x_1456_ = lean_nat_add(v_headerBytesRead_1451_, v_n_1444_);
lean_dec(v_headerBytesRead_1451_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 5, v___x_1456_);
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
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_bodyBytesRead_1450_);
lean_ctor_set(v_reuseFailAlloc_1459_, 5, v___x_1456_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(lean_object* v_n_1461_, lean_object* v_reader_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_1461_, v_reader_1462_);
lean_dec(v_n_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes(uint8_t v_dir_1464_, lean_object* v_n_1465_, lean_object* v_reader_1466_){
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
v___x_1477_ = lean_nat_add(v_headerBytesRead_1472_, v_n_1465_);
lean_dec(v_headerBytesRead_1472_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 5, v___x_1477_);
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
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_bodyBytesRead_1471_);
lean_ctor_set(v_reuseFailAlloc_1480_, 5, v___x_1477_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(lean_object* v_dir_1482_, lean_object* v_n_1483_, lean_object* v_reader_1484_){
_start:
{
uint8_t v_dir_boxed_1485_; lean_object* v_res_1486_; 
v_dir_boxed_1485_ = lean_unbox(v_dir_1482_);
v_res_1486_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_1485_, v_n_1483_, v_reader_1484_);
lean_dec(v_n_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(lean_object* v_size_1487_, lean_object* v_reader_1488_){
_start:
{
lean_object* v_input_1489_; lean_object* v_messageHead_1490_; lean_object* v_messageCount_1491_; lean_object* v_bodyBytesRead_1492_; lean_object* v_headerBytesRead_1493_; uint8_t v_noMoreInput_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1503_; 
v_input_1489_ = lean_ctor_get(v_reader_1488_, 1);
v_messageHead_1490_ = lean_ctor_get(v_reader_1488_, 2);
v_messageCount_1491_ = lean_ctor_get(v_reader_1488_, 3);
v_bodyBytesRead_1492_ = lean_ctor_get(v_reader_1488_, 4);
v_headerBytesRead_1493_ = lean_ctor_get(v_reader_1488_, 5);
v_noMoreInput_1494_ = lean_ctor_get_uint8(v_reader_1488_, sizeof(void*)*6);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_reader_1488_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_reader_1488_, 0);
lean_dec(v_unused_1504_);
v___x_1496_ = v_reader_1488_;
v_isShared_1497_ = v_isSharedCheck_1503_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_headerBytesRead_1493_);
lean_inc(v_bodyBytesRead_1492_);
lean_inc(v_messageCount_1491_);
lean_inc(v_messageHead_1490_);
lean_inc(v_input_1489_);
lean_dec(v_reader_1488_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1503_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_size_1487_);
v___x_1499_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1499_);
v___x_1501_ = v___x_1496_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_input_1489_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_messageHead_1490_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_messageCount_1491_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_bodyBytesRead_1492_);
lean_ctor_set(v_reuseFailAlloc_1502_, 5, v_headerBytesRead_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*6, v_noMoreInput_1494_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody(uint8_t v_dir_1505_, lean_object* v_size_1506_, lean_object* v_reader_1507_){
_start:
{
lean_object* v_input_1508_; lean_object* v_messageHead_1509_; lean_object* v_messageCount_1510_; lean_object* v_bodyBytesRead_1511_; lean_object* v_headerBytesRead_1512_; uint8_t v_noMoreInput_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1522_; 
v_input_1508_ = lean_ctor_get(v_reader_1507_, 1);
v_messageHead_1509_ = lean_ctor_get(v_reader_1507_, 2);
v_messageCount_1510_ = lean_ctor_get(v_reader_1507_, 3);
v_bodyBytesRead_1511_ = lean_ctor_get(v_reader_1507_, 4);
v_headerBytesRead_1512_ = lean_ctor_get(v_reader_1507_, 5);
v_noMoreInput_1513_ = lean_ctor_get_uint8(v_reader_1507_, sizeof(void*)*6);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_reader_1507_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_reader_1507_, 0);
lean_dec(v_unused_1523_);
v___x_1515_ = v_reader_1507_;
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_headerBytesRead_1512_);
lean_inc(v_bodyBytesRead_1511_);
lean_inc(v_messageCount_1510_);
lean_inc(v_messageHead_1509_);
lean_inc(v_input_1508_);
lean_dec(v_reader_1507_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_size_1506_);
v___x_1518_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1518_);
v___x_1520_ = v___x_1515_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_input_1508_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_messageHead_1509_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_messageCount_1510_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_bodyBytesRead_1511_);
lean_ctor_set(v_reuseFailAlloc_1521_, 5, v_headerBytesRead_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*6, v_noMoreInput_1513_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(lean_object* v_dir_1524_, lean_object* v_size_1525_, lean_object* v_reader_1526_){
_start:
{
uint8_t v_dir_boxed_1527_; lean_object* v_res_1528_; 
v_dir_boxed_1527_ = lean_unbox(v_dir_1524_);
v_res_1528_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(v_dir_boxed_1527_, v_size_1525_, v_reader_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(lean_object* v_reader_1531_){
_start:
{
lean_object* v_input_1532_; lean_object* v_messageHead_1533_; lean_object* v_messageCount_1534_; lean_object* v_bodyBytesRead_1535_; lean_object* v_headerBytesRead_1536_; uint8_t v_noMoreInput_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
v_input_1532_ = lean_ctor_get(v_reader_1531_, 1);
v_messageHead_1533_ = lean_ctor_get(v_reader_1531_, 2);
v_messageCount_1534_ = lean_ctor_get(v_reader_1531_, 3);
v_bodyBytesRead_1535_ = lean_ctor_get(v_reader_1531_, 4);
v_headerBytesRead_1536_ = lean_ctor_get(v_reader_1531_, 5);
v_noMoreInput_1537_ = lean_ctor_get_uint8(v_reader_1531_, sizeof(void*)*6);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_reader_1531_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v_reader_1531_, 0);
lean_dec(v_unused_1546_);
v___x_1539_ = v_reader_1531_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_headerBytesRead_1536_);
lean_inc(v_bodyBytesRead_1535_);
lean_inc(v_messageCount_1534_);
lean_inc(v_messageHead_1533_);
lean_inc(v_input_1532_);
lean_dec(v_reader_1531_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_input_1532_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_messageHead_1533_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_messageCount_1534_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_bodyBytesRead_1535_);
lean_ctor_set(v_reuseFailAlloc_1544_, 5, v_headerBytesRead_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1544_, sizeof(void*)*6, v_noMoreInput_1537_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody(uint8_t v_dir_1547_, lean_object* v_reader_1548_){
_start:
{
lean_object* v_input_1549_; lean_object* v_messageHead_1550_; lean_object* v_messageCount_1551_; lean_object* v_bodyBytesRead_1552_; lean_object* v_headerBytesRead_1553_; uint8_t v_noMoreInput_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1562_; 
v_input_1549_ = lean_ctor_get(v_reader_1548_, 1);
v_messageHead_1550_ = lean_ctor_get(v_reader_1548_, 2);
v_messageCount_1551_ = lean_ctor_get(v_reader_1548_, 3);
v_bodyBytesRead_1552_ = lean_ctor_get(v_reader_1548_, 4);
v_headerBytesRead_1553_ = lean_ctor_get(v_reader_1548_, 5);
v_noMoreInput_1554_ = lean_ctor_get_uint8(v_reader_1548_, sizeof(void*)*6);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_reader_1548_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v_reader_1548_, 0);
lean_dec(v_unused_1563_);
v___x_1556_ = v_reader_1548_;
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_headerBytesRead_1553_);
lean_inc(v_bodyBytesRead_1552_);
lean_inc(v_messageCount_1551_);
lean_inc(v_messageHead_1550_);
lean_inc(v_input_1549_);
lean_dec(v_reader_1548_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1558_);
v___x_1560_ = v___x_1556_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_input_1549_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_messageHead_1550_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_messageCount_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_bodyBytesRead_1552_);
lean_ctor_set(v_reuseFailAlloc_1561_, 5, v_headerBytesRead_1553_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*6, v_noMoreInput_1554_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(lean_object* v_dir_1564_, lean_object* v_reader_1565_){
_start:
{
uint8_t v_dir_boxed_1566_; lean_object* v_res_1567_; 
v_dir_boxed_1566_ = lean_unbox(v_dir_1564_);
v_res_1567_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_1566_, v_reader_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(lean_object* v_reader_1568_){
_start:
{
lean_object* v_state_1569_; lean_object* v_input_1570_; lean_object* v_messageHead_1571_; lean_object* v_messageCount_1572_; lean_object* v_bodyBytesRead_1573_; lean_object* v_headerBytesRead_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1582_; 
v_state_1569_ = lean_ctor_get(v_reader_1568_, 0);
v_input_1570_ = lean_ctor_get(v_reader_1568_, 1);
v_messageHead_1571_ = lean_ctor_get(v_reader_1568_, 2);
v_messageCount_1572_ = lean_ctor_get(v_reader_1568_, 3);
v_bodyBytesRead_1573_ = lean_ctor_get(v_reader_1568_, 4);
v_headerBytesRead_1574_ = lean_ctor_get(v_reader_1568_, 5);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_reader_1568_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1576_ = v_reader_1568_;
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_headerBytesRead_1574_);
lean_inc(v_bodyBytesRead_1573_);
lean_inc(v_messageCount_1572_);
lean_inc(v_messageHead_1571_);
lean_inc(v_input_1570_);
lean_inc(v_state_1569_);
lean_dec(v_reader_1568_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
uint8_t v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = 1;
if (v_isShared_1577_ == 0)
{
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_state_1569_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_input_1570_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_messageHead_1571_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_messageCount_1572_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v_bodyBytesRead_1573_);
lean_ctor_set(v_reuseFailAlloc_1581_, 5, v_headerBytesRead_1574_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*6, v___x_1578_);
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput(uint8_t v_dir_1583_, lean_object* v_reader_1584_){
_start:
{
lean_object* v_state_1585_; lean_object* v_input_1586_; lean_object* v_messageHead_1587_; lean_object* v_messageCount_1588_; lean_object* v_bodyBytesRead_1589_; lean_object* v_headerBytesRead_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1598_; 
v_state_1585_ = lean_ctor_get(v_reader_1584_, 0);
v_input_1586_ = lean_ctor_get(v_reader_1584_, 1);
v_messageHead_1587_ = lean_ctor_get(v_reader_1584_, 2);
v_messageCount_1588_ = lean_ctor_get(v_reader_1584_, 3);
v_bodyBytesRead_1589_ = lean_ctor_get(v_reader_1584_, 4);
v_headerBytesRead_1590_ = lean_ctor_get(v_reader_1584_, 5);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_reader_1584_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1592_ = v_reader_1584_;
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_headerBytesRead_1590_);
lean_inc(v_bodyBytesRead_1589_);
lean_inc(v_messageCount_1588_);
lean_inc(v_messageHead_1587_);
lean_inc(v_input_1586_);
lean_inc(v_state_1585_);
lean_dec(v_reader_1584_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
uint8_t v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = 1;
if (v_isShared_1593_ == 0)
{
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_state_1585_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_input_1586_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_messageHead_1587_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_messageCount_1588_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v_bodyBytesRead_1589_);
lean_ctor_set(v_reuseFailAlloc_1597_, 5, v_headerBytesRead_1590_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*6, v___x_1594_);
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(lean_object* v_dir_1599_, lean_object* v_reader_1600_){
_start:
{
uint8_t v_dir_boxed_1601_; lean_object* v_res_1602_; 
v_dir_boxed_1601_ = lean_unbox(v_dir_1599_);
v_res_1602_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_boxed_1601_, v_reader_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(uint8_t v_dir_1603_, lean_object* v_reader_1604_){
_start:
{
lean_object* v_messageHead_1605_; uint8_t v___x_1606_; 
v_messageHead_1605_ = lean_ctor_get(v_reader_1604_, 2);
v___x_1606_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_1603_, v_messageHead_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(lean_object* v_dir_1607_, lean_object* v_reader_1608_){
_start:
{
uint8_t v_dir_boxed_1609_; uint8_t v_res_1610_; lean_object* v_r_1611_; 
v_dir_boxed_1609_ = lean_unbox(v_dir_1607_);
v_res_1610_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_1609_, v_reader_1608_);
lean_dec_ref(v_reader_1608_);
v_r_1611_ = lean_box(v_res_1610_);
return v_r_1611_;
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
