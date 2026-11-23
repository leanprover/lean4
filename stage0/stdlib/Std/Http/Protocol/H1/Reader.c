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
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Std.Http.Protocol.H1.Reader.State.needStartLine"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Std.Http.Protocol.H1.Reader.State.pending"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Http.Protocol.H1.Reader.State.complete"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Http.Protocol.H1.Reader.State.closed"};
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
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_noMoreInput___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_noMoreInput___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_noMoreInput(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_noMoreInput___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Protocol_H1_Reader_replaceLastHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Reader_replaceLastHeader___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_replaceLastHeader___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_replaceLastHeader(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_replaceLastHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object*, lean_object*);
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
default: 
{
lean_dec(v_t_449_);
return v_k_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim(uint8_t v_dir_457_, lean_object* v_motive_458_, lean_object* v_ctorIdx_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_k_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_460_, v_k_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(lean_object* v_dir_464_, lean_object* v_motive_465_, lean_object* v_ctorIdx_466_, lean_object* v_t_467_, lean_object* v_h_468_, lean_object* v_k_469_){
_start:
{
uint8_t v_dir_boxed_470_; lean_object* v_res_471_; 
v_dir_boxed_470_ = lean_unbox(v_dir_464_);
v_res_471_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(v_dir_boxed_470_, v_motive_465_, v_ctorIdx_466_, v_t_467_, v_h_468_, v_k_469_);
lean_dec(v_ctorIdx_466_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(lean_object* v_t_472_, lean_object* v_needStartLine_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_472_, v_needStartLine_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(uint8_t v_dir_475_, lean_object* v_motive_476_, lean_object* v_t_477_, lean_object* v_h_478_, lean_object* v_needStartLine_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_477_, v_needStartLine_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(lean_object* v_dir_481_, lean_object* v_motive_482_, lean_object* v_t_483_, lean_object* v_h_484_, lean_object* v_needStartLine_485_){
_start:
{
uint8_t v_dir_boxed_486_; lean_object* v_res_487_; 
v_dir_boxed_486_ = lean_unbox(v_dir_481_);
v_res_487_ = l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(v_dir_boxed_486_, v_motive_482_, v_t_483_, v_h_484_, v_needStartLine_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___redArg(lean_object* v_t_488_, lean_object* v_needHeader_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_488_, v_needHeader_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(uint8_t v_dir_491_, lean_object* v_motive_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_needHeader_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_493_, v_needHeader_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(lean_object* v_dir_497_, lean_object* v_motive_498_, lean_object* v_t_499_, lean_object* v_h_500_, lean_object* v_needHeader_501_){
_start:
{
uint8_t v_dir_boxed_502_; lean_object* v_res_503_; 
v_dir_boxed_502_ = lean_unbox(v_dir_497_);
v_res_503_ = l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(v_dir_boxed_502_, v_motive_498_, v_t_499_, v_h_500_, v_needHeader_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___redArg(lean_object* v_t_504_, lean_object* v_readBody_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_504_, v_readBody_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim(uint8_t v_dir_507_, lean_object* v_motive_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_readBody_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_509_, v_readBody_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(lean_object* v_dir_513_, lean_object* v_motive_514_, lean_object* v_t_515_, lean_object* v_h_516_, lean_object* v_readBody_517_){
_start:
{
uint8_t v_dir_boxed_518_; lean_object* v_res_519_; 
v_dir_boxed_518_ = lean_unbox(v_dir_513_);
v_res_519_ = l_Std_Http_Protocol_H1_Reader_State_readBody_elim(v_dir_boxed_518_, v_motive_514_, v_t_515_, v_h_516_, v_readBody_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___redArg(lean_object* v_t_520_, lean_object* v_continue_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_520_, v_continue_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim(uint8_t v_dir_523_, lean_object* v_motive_524_, lean_object* v_t_525_, lean_object* v_h_526_, lean_object* v_continue_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_525_, v_continue_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___boxed(lean_object* v_dir_529_, lean_object* v_motive_530_, lean_object* v_t_531_, lean_object* v_h_532_, lean_object* v_continue_533_){
_start:
{
uint8_t v_dir_boxed_534_; lean_object* v_res_535_; 
v_dir_boxed_534_ = lean_unbox(v_dir_529_);
v_res_535_ = l_Std_Http_Protocol_H1_Reader_State_continue_elim(v_dir_boxed_534_, v_motive_530_, v_t_531_, v_h_532_, v_continue_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___redArg(lean_object* v_t_536_, lean_object* v_pending_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_536_, v_pending_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim(uint8_t v_dir_539_, lean_object* v_motive_540_, lean_object* v_t_541_, lean_object* v_h_542_, lean_object* v_pending_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_541_, v_pending_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(lean_object* v_dir_545_, lean_object* v_motive_546_, lean_object* v_t_547_, lean_object* v_h_548_, lean_object* v_pending_549_){
_start:
{
uint8_t v_dir_boxed_550_; lean_object* v_res_551_; 
v_dir_boxed_550_ = lean_unbox(v_dir_545_);
v_res_551_ = l_Std_Http_Protocol_H1_Reader_State_pending_elim(v_dir_boxed_550_, v_motive_546_, v_t_547_, v_h_548_, v_pending_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___redArg(lean_object* v_t_552_, lean_object* v_complete_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_552_, v_complete_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim(uint8_t v_dir_555_, lean_object* v_motive_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_complete_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_557_, v_complete_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(lean_object* v_dir_561_, lean_object* v_motive_562_, lean_object* v_t_563_, lean_object* v_h_564_, lean_object* v_complete_565_){
_start:
{
uint8_t v_dir_boxed_566_; lean_object* v_res_567_; 
v_dir_boxed_566_ = lean_unbox(v_dir_561_);
v_res_567_ = l_Std_Http_Protocol_H1_Reader_State_complete_elim(v_dir_boxed_566_, v_motive_562_, v_t_563_, v_h_564_, v_complete_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___redArg(lean_object* v_t_568_, lean_object* v_closed_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_568_, v_closed_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim(uint8_t v_dir_571_, lean_object* v_motive_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_closed_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_573_, v_closed_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(lean_object* v_dir_577_, lean_object* v_motive_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_closed_581_){
_start:
{
uint8_t v_dir_boxed_582_; lean_object* v_res_583_; 
v_dir_boxed_582_ = lean_unbox(v_dir_577_);
v_res_583_ = l_Std_Http_Protocol_H1_Reader_State_closed_elim(v_dir_boxed_582_, v_motive_578_, v_t_579_, v_h_580_, v_closed_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg(){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_box(0);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg___boxed(lean_object* v___dummy_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t v_dir_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_box(0);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object* v_dir_590_){
_start:
{
uint8_t v_dir_boxed_591_; lean_object* v_res_592_; 
v_dir_boxed_591_ = lean_unbox(v_dir_590_);
v_res_592_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_591_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg(){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_box(0);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg___boxed(lean_object* v___dummy_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t v_a_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lean_box(0);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object* v_a_599_){
_start:
{
uint8_t v_a_11__boxed_600_; lean_object* v_res_601_; 
v_a_11__boxed_600_ = lean_unbox(v_a_599_);
v_res_601_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_11__boxed_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(lean_object* v_x_632_, lean_object* v_prec_633_){
_start:
{
lean_object* v___y_635_; lean_object* v___y_642_; lean_object* v___y_649_; lean_object* v___y_656_; 
switch(lean_obj_tag(v_x_632_))
{
case 0:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(1024u);
v___x_663_ = lean_nat_dec_le(v___x_662_, v_prec_633_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_635_ = v___x_664_;
goto v___jp_634_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_635_ = v___x_665_;
goto v___jp_634_;
}
}
case 1:
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_686_; 
v_a_666_ = lean_ctor_get(v_x_632_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_686_ == 0)
{
v___x_668_ = v_x_632_;
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v_x_632_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___y_671_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(1024u);
v___x_683_ = lean_nat_dec_le(v___x_682_, v_prec_633_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
v___x_684_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_671_ = v___x_684_;
goto v___jp_670_;
}
else
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_671_ = v___x_685_;
goto v___jp_670_;
}
v___jp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10));
v___x_673_ = l_Nat_reprFast(v_a_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 3);
lean_ctor_set(v___x_668_, 0, v___x_673_);
v___x_675_ = v___x_668_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_681_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_672_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
lean_inc(v___y_671_);
v___x_677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_677_, 0, v___y_671_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = 0;
v___x_679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*1, v___x_678_);
v___x_680_ = l_Repr_addAppParen(v___x_679_, v_prec_633_);
return v___x_680_;
}
}
}
}
case 2:
{
lean_object* v_a_687_; lean_object* v___y_689_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_a_687_ = lean_ctor_get(v_x_632_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v_x_632_, 1);
v___x_698_ = lean_unsigned_to_nat(1024u);
v___x_699_ = lean_nat_dec_le(v___x_698_, v_prec_633_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_689_ = v___x_700_;
goto v___jp_688_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_689_ = v___x_701_;
goto v___jp_688_;
}
v___jp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_690_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13));
v___x_691_ = lean_unsigned_to_nat(1024u);
v___x_692_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_687_, v___x_691_);
v___x_693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_690_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
lean_inc(v___y_689_);
v___x_694_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_694_, 0, v___y_689_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = 0;
v___x_696_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*1, v___x_695_);
v___x_697_ = l_Repr_addAppParen(v___x_696_, v_prec_633_);
return v___x_697_;
}
}
case 3:
{
lean_object* v_a_702_; lean_object* v___x_703_; lean_object* v___y_705_; uint8_t v___x_713_; 
v_a_702_ = lean_ctor_get(v_x_632_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v_x_632_, 1);
v___x_703_ = lean_unsigned_to_nat(1024u);
v___x_713_ = lean_nat_dec_le(v___x_703_, v_prec_633_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_705_ = v___x_714_;
goto v___jp_704_;
}
else
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_705_ = v___x_715_;
goto v___jp_704_;
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_706_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16));
v___x_707_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_a_702_, v___x_703_);
v___x_708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
lean_inc(v___y_705_);
v___x_709_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_709_, 0, v___y_705_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = 0;
v___x_711_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*1, v___x_710_);
v___x_712_ = l_Repr_addAppParen(v___x_711_, v_prec_633_);
return v___x_712_;
}
}
case 4:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(1024u);
v___x_717_ = lean_nat_dec_le(v___x_716_, v_prec_633_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
v___x_718_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_642_ = v___x_718_;
goto v___jp_641_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_642_ = v___x_719_;
goto v___jp_641_;
}
}
case 5:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_unsigned_to_nat(1024u);
v___x_721_ = lean_nat_dec_le(v___x_720_, v_prec_633_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_649_ = v___x_722_;
goto v___jp_648_;
}
else
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_649_ = v___x_723_;
goto v___jp_648_;
}
}
default: 
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(1024u);
v___x_725_ = lean_nat_dec_le(v___x_724_, v_prec_633_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
v___x_726_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_656_ = v___x_726_;
goto v___jp_655_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_656_ = v___x_727_;
goto v___jp_655_;
}
}
}
v___jp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_636_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1));
lean_inc(v___y_635_);
v___x_637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_637_, 0, v___y_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = 0;
v___x_639_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*1, v___x_638_);
v___x_640_ = l_Repr_addAppParen(v___x_639_, v_prec_633_);
return v___x_640_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_643_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3));
lean_inc(v___y_642_);
v___x_644_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_644_, 0, v___y_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = 0;
v___x_646_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_645_);
v___x_647_ = l_Repr_addAppParen(v___x_646_, v_prec_633_);
return v___x_647_;
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_650_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5));
lean_inc(v___y_649_);
v___x_651_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_651_, 0, v___y_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = 0;
v___x_653_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*1, v___x_652_);
v___x_654_ = l_Repr_addAppParen(v___x_653_, v_prec_633_);
return v___x_654_;
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_657_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7));
lean_inc(v___y_656_);
v___x_658_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_658_, 0, v___y_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = 0;
v___x_660_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*1, v___x_659_);
v___x_661_ = l_Repr_addAppParen(v___x_660_, v_prec_633_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(lean_object* v_x_728_, lean_object* v_prec_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_728_, v_prec_729_);
lean_dec(v_prec_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr(uint8_t v_dir_731_, lean_object* v_x_732_, lean_object* v_prec_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_732_, v_prec_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(lean_object* v_dir_735_, lean_object* v_x_736_, lean_object* v_prec_737_){
_start:
{
uint8_t v_dir_742__boxed_738_; lean_object* v_res_739_; 
v_dir_742__boxed_738_ = lean_unbox(v_dir_735_);
v_res_739_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(v_dir_742__boxed_738_, v_x_736_, v_prec_737_);
lean_dec(v_prec_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState(uint8_t v_dir_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_box(v_dir_740_);
v___x_742_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed), 3, 1);
lean_closure_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState___boxed(lean_object* v_dir_743_){
_start:
{
uint8_t v_dir_5__boxed_744_; lean_object* v_res_745_; 
v_dir_5__boxed_744_ = lean_unbox(v_dir_743_);
v_res_745_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_744_);
return v_res_745_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
switch(lean_obj_tag(v_x_746_))
{
case 0:
{
if (lean_obj_tag(v_x_747_) == 0)
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
case 1:
{
if (lean_obj_tag(v_x_747_) == 1)
{
lean_object* v_a_750_; lean_object* v_a_751_; uint8_t v___x_752_; 
v_a_750_ = lean_ctor_get(v_x_746_, 0);
v_a_751_ = lean_ctor_get(v_x_747_, 0);
v___x_752_ = lean_nat_dec_eq(v_a_750_, v_a_751_);
return v___x_752_;
}
else
{
uint8_t v___x_753_; 
v___x_753_ = 0;
return v___x_753_;
}
}
case 2:
{
if (lean_obj_tag(v_x_747_) == 2)
{
lean_object* v_a_754_; lean_object* v_a_755_; uint8_t v___x_756_; 
v_a_754_ = lean_ctor_get(v_x_746_, 0);
v_a_755_ = lean_ctor_get(v_x_747_, 0);
v___x_756_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_a_754_, v_a_755_);
return v___x_756_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
return v___x_757_;
}
}
case 3:
{
if (lean_obj_tag(v_x_747_) == 3)
{
lean_object* v_a_758_; lean_object* v_a_759_; 
v_a_758_ = lean_ctor_get(v_x_746_, 0);
v_a_759_ = lean_ctor_get(v_x_747_, 0);
v_x_746_ = v_a_758_;
v_x_747_ = v_a_759_;
goto _start;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
case 4:
{
if (lean_obj_tag(v_x_747_) == 4)
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
case 5:
{
if (lean_obj_tag(v_x_747_) == 5)
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
if (lean_obj_tag(v_x_747_) == 6)
{
uint8_t v___x_766_; 
v___x_766_ = 1;
return v___x_766_;
}
else
{
uint8_t v___x_767_; 
v___x_767_ = 0;
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_768_, v_x_769_);
lean_dec(v_x_769_);
lean_dec(v_x_768_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq(uint8_t v_dir_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_773_, v_x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(lean_object* v_dir_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
uint8_t v_dir_158__boxed_779_; uint8_t v_res_780_; lean_object* v_r_781_; 
v_dir_158__boxed_779_ = lean_unbox(v_dir_776_);
v_res_780_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(v_dir_158__boxed_779_, v_x_777_, v_x_778_);
lean_dec(v_x_778_);
lean_dec(v_x_777_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState(uint8_t v_dir_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_box(v_dir_782_);
v___x_784_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed), 3, 1);
lean_closure_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(lean_object* v_dir_785_){
_start:
{
uint8_t v_dir_5__boxed_786_; lean_object* v_res_787_; 
v_dir_5__boxed_786_ = lean_unbox(v_dir_785_);
v_res_787_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_786_);
return v_res_787_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_noMoreInput___redArg(lean_object* v_reader_788_){
_start:
{
uint8_t v_peerClosed_789_; 
v_peerClosed_789_ = lean_ctor_get_uint8(v_reader_788_, sizeof(void*)*6);
if (v_peerClosed_789_ == 0)
{
uint8_t v_inputStopped_790_; 
v_inputStopped_790_ = lean_ctor_get_uint8(v_reader_788_, sizeof(void*)*6 + 1);
return v_inputStopped_790_;
}
else
{
return v_peerClosed_789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_noMoreInput___redArg___boxed(lean_object* v_reader_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_Std_Http_Protocol_H1_Reader_noMoreInput___redArg(v_reader_791_);
lean_dec_ref(v_reader_791_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_noMoreInput(uint8_t v_dir_794_, lean_object* v_reader_795_){
_start:
{
uint8_t v_peerClosed_796_; 
v_peerClosed_796_ = lean_ctor_get_uint8(v_reader_795_, sizeof(void*)*6);
if (v_peerClosed_796_ == 0)
{
uint8_t v_inputStopped_797_; 
v_inputStopped_797_ = lean_ctor_get_uint8(v_reader_795_, sizeof(void*)*6 + 1);
return v_inputStopped_797_;
}
else
{
return v_peerClosed_796_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_noMoreInput___boxed(lean_object* v_dir_798_, lean_object* v_reader_799_){
_start:
{
uint8_t v_dir_boxed_800_; uint8_t v_res_801_; lean_object* v_r_802_; 
v_dir_boxed_800_ = lean_unbox(v_dir_798_);
v_res_801_ = l_Std_Http_Protocol_H1_Reader_noMoreInput(v_dir_boxed_800_, v_reader_799_);
lean_dec_ref(v_reader_799_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object* v_reader_803_){
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object* v_reader_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_807_);
lean_dec_ref(v_reader_807_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t v_dir_810_, lean_object* v_reader_811_){
_start:
{
lean_object* v_state_812_; 
v_state_812_ = lean_ctor_get(v_reader_811_, 0);
if (lean_obj_tag(v_state_812_) == 6)
{
uint8_t v___x_813_; 
v___x_813_ = 1;
return v___x_813_;
}
else
{
uint8_t v___x_814_; 
v___x_814_ = 0;
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object* v_dir_815_, lean_object* v_reader_816_){
_start:
{
uint8_t v_dir_boxed_817_; uint8_t v_res_818_; lean_object* v_r_819_; 
v_dir_boxed_817_ = lean_unbox(v_dir_815_);
v_res_818_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_817_, v_reader_816_);
lean_dec_ref(v_reader_816_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object* v_reader_820_){
_start:
{
lean_object* v_state_821_; 
v_state_821_ = lean_ctor_get(v_reader_820_, 0);
if (lean_obj_tag(v_state_821_) == 5)
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object* v_reader_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_824_);
lean_dec_ref(v_reader_824_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t v_dir_827_, lean_object* v_reader_828_){
_start:
{
lean_object* v_state_829_; 
v_state_829_ = lean_ctor_get(v_reader_828_, 0);
if (lean_obj_tag(v_state_829_) == 5)
{
uint8_t v___x_830_; 
v___x_830_ = 1;
return v___x_830_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = 0;
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object* v_dir_832_, lean_object* v_reader_833_){
_start:
{
uint8_t v_dir_boxed_834_; uint8_t v_res_835_; lean_object* v_r_836_; 
v_dir_boxed_834_ = lean_unbox(v_dir_832_);
v_res_835_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_834_, v_reader_833_);
lean_dec_ref(v_reader_833_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___redArg(lean_object* v_data_837_, lean_object* v_reader_838_){
_start:
{
lean_object* v_input_839_; lean_object* v_state_840_; lean_object* v_messageHead_841_; lean_object* v_messageCount_842_; lean_object* v_bodyBytesRead_843_; lean_object* v_headerBytesRead_844_; uint8_t v_peerClosed_845_; uint8_t v_inputStopped_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_867_; 
v_input_839_ = lean_ctor_get(v_reader_838_, 1);
v_state_840_ = lean_ctor_get(v_reader_838_, 0);
v_messageHead_841_ = lean_ctor_get(v_reader_838_, 2);
v_messageCount_842_ = lean_ctor_get(v_reader_838_, 3);
v_bodyBytesRead_843_ = lean_ctor_get(v_reader_838_, 4);
v_headerBytesRead_844_ = lean_ctor_get(v_reader_838_, 5);
v_peerClosed_845_ = lean_ctor_get_uint8(v_reader_838_, sizeof(void*)*6);
v_inputStopped_846_ = lean_ctor_get_uint8(v_reader_838_, sizeof(void*)*6 + 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v_reader_838_);
if (v_isSharedCheck_867_ == 0)
{
v___x_848_ = v_reader_838_;
v_isShared_849_ = v_isSharedCheck_867_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_headerBytesRead_844_);
lean_inc(v_bodyBytesRead_843_);
lean_inc(v_messageCount_842_);
lean_inc(v_messageHead_841_);
lean_inc(v_input_839_);
lean_inc(v_state_840_);
lean_dec(v_reader_838_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_867_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_array_850_; lean_object* v_idx_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_array_850_ = lean_ctor_get(v_input_839_, 0);
lean_inc_ref(v_array_850_);
v_idx_851_ = lean_ctor_get(v_input_839_, 1);
lean_inc(v_idx_851_);
lean_dec_ref(v_input_839_);
v___x_852_ = lean_byte_array_size(v_array_850_);
v___x_853_ = lean_nat_dec_le(v___x_852_, v_idx_851_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_854_ = l_ByteArray_extract(v_array_850_, v_idx_851_, v___x_852_);
lean_dec_ref(v_array_850_);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_byte_array_size(v___x_854_);
v___x_857_ = lean_byte_array_size(v_data_837_);
v___x_858_ = lean_byte_array_copy_slice(v_data_837_, v___x_855_, v___x_854_, v___x_856_, v___x_857_, v___x_853_);
lean_dec_ref(v_data_837_);
v___x_859_ = l_ByteArray_mkIterator(v___x_858_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v___x_859_);
v___x_861_ = v___x_848_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_state_840_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_messageHead_841_);
lean_ctor_set(v_reuseFailAlloc_862_, 3, v_messageCount_842_);
lean_ctor_set(v_reuseFailAlloc_862_, 4, v_bodyBytesRead_843_);
lean_ctor_set(v_reuseFailAlloc_862_, 5, v_headerBytesRead_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_862_, sizeof(void*)*6, v_peerClosed_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_862_, sizeof(void*)*6 + 1, v_inputStopped_846_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_865_; 
lean_dec(v_idx_851_);
lean_dec_ref(v_array_850_);
v___x_863_ = l_ByteArray_mkIterator(v_data_837_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v___x_863_);
v___x_865_ = v___x_848_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_state_840_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_messageHead_841_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_messageCount_842_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_bodyBytesRead_843_);
lean_ctor_set(v_reuseFailAlloc_866_, 5, v_headerBytesRead_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_866_, sizeof(void*)*6, v_peerClosed_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_866_, sizeof(void*)*6 + 1, v_inputStopped_846_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed(uint8_t v_dir_868_, lean_object* v_data_869_, lean_object* v_reader_870_){
_start:
{
lean_object* v_input_871_; lean_object* v_state_872_; lean_object* v_messageHead_873_; lean_object* v_messageCount_874_; lean_object* v_bodyBytesRead_875_; lean_object* v_headerBytesRead_876_; uint8_t v_peerClosed_877_; uint8_t v_inputStopped_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_899_; 
v_input_871_ = lean_ctor_get(v_reader_870_, 1);
v_state_872_ = lean_ctor_get(v_reader_870_, 0);
v_messageHead_873_ = lean_ctor_get(v_reader_870_, 2);
v_messageCount_874_ = lean_ctor_get(v_reader_870_, 3);
v_bodyBytesRead_875_ = lean_ctor_get(v_reader_870_, 4);
v_headerBytesRead_876_ = lean_ctor_get(v_reader_870_, 5);
v_peerClosed_877_ = lean_ctor_get_uint8(v_reader_870_, sizeof(void*)*6);
v_inputStopped_878_ = lean_ctor_get_uint8(v_reader_870_, sizeof(void*)*6 + 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_reader_870_);
if (v_isSharedCheck_899_ == 0)
{
v___x_880_ = v_reader_870_;
v_isShared_881_ = v_isSharedCheck_899_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_headerBytesRead_876_);
lean_inc(v_bodyBytesRead_875_);
lean_inc(v_messageCount_874_);
lean_inc(v_messageHead_873_);
lean_inc(v_input_871_);
lean_inc(v_state_872_);
lean_dec(v_reader_870_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_899_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_array_882_; lean_object* v_idx_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_array_882_ = lean_ctor_get(v_input_871_, 0);
lean_inc_ref(v_array_882_);
v_idx_883_ = lean_ctor_get(v_input_871_, 1);
lean_inc(v_idx_883_);
lean_dec_ref(v_input_871_);
v___x_884_ = lean_byte_array_size(v_array_882_);
v___x_885_ = lean_nat_dec_le(v___x_884_, v_idx_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_886_ = l_ByteArray_extract(v_array_882_, v_idx_883_, v___x_884_);
lean_dec_ref(v_array_882_);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_byte_array_size(v___x_886_);
v___x_889_ = lean_byte_array_size(v_data_869_);
v___x_890_ = lean_byte_array_copy_slice(v_data_869_, v___x_887_, v___x_886_, v___x_888_, v___x_889_, v___x_885_);
lean_dec_ref(v_data_869_);
v___x_891_ = l_ByteArray_mkIterator(v___x_890_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_891_);
v___x_893_ = v___x_880_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_state_872_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_messageHead_873_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_messageCount_874_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_bodyBytesRead_875_);
lean_ctor_set(v_reuseFailAlloc_894_, 5, v_headerBytesRead_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_894_, sizeof(void*)*6, v_peerClosed_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_894_, sizeof(void*)*6 + 1, v_inputStopped_878_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_897_; 
lean_dec(v_idx_883_);
lean_dec_ref(v_array_882_);
v___x_895_ = l_ByteArray_mkIterator(v_data_869_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_895_);
v___x_897_ = v___x_880_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_state_872_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_messageHead_873_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_messageCount_874_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v_bodyBytesRead_875_);
lean_ctor_set(v_reuseFailAlloc_898_, 5, v_headerBytesRead_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*6, v_peerClosed_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*6 + 1, v_inputStopped_878_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___boxed(lean_object* v_dir_900_, lean_object* v_data_901_, lean_object* v_reader_902_){
_start:
{
uint8_t v_dir_boxed_903_; lean_object* v_res_904_; 
v_dir_boxed_903_ = lean_unbox(v_dir_900_);
v_res_904_ = l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_903_, v_data_901_, v_reader_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___redArg(lean_object* v_input_905_, lean_object* v_reader_906_){
_start:
{
lean_object* v_state_907_; lean_object* v_messageHead_908_; lean_object* v_messageCount_909_; lean_object* v_bodyBytesRead_910_; lean_object* v_headerBytesRead_911_; uint8_t v_peerClosed_912_; uint8_t v_inputStopped_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_state_907_ = lean_ctor_get(v_reader_906_, 0);
v_messageHead_908_ = lean_ctor_get(v_reader_906_, 2);
v_messageCount_909_ = lean_ctor_get(v_reader_906_, 3);
v_bodyBytesRead_910_ = lean_ctor_get(v_reader_906_, 4);
v_headerBytesRead_911_ = lean_ctor_get(v_reader_906_, 5);
v_peerClosed_912_ = lean_ctor_get_uint8(v_reader_906_, sizeof(void*)*6);
v_inputStopped_913_ = lean_ctor_get_uint8(v_reader_906_, sizeof(void*)*6 + 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_reader_906_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v_reader_906_, 1);
lean_dec(v_unused_921_);
v___x_915_ = v_reader_906_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_headerBytesRead_911_);
lean_inc(v_bodyBytesRead_910_);
lean_inc(v_messageCount_909_);
lean_inc(v_messageHead_908_);
lean_inc(v_state_907_);
lean_dec(v_reader_906_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v_input_905_);
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_state_907_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_input_905_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_messageHead_908_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_messageCount_909_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_bodyBytesRead_910_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_headerBytesRead_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*6, v_peerClosed_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*6 + 1, v_inputStopped_913_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput(uint8_t v_dir_922_, lean_object* v_input_923_, lean_object* v_reader_924_){
_start:
{
lean_object* v_state_925_; lean_object* v_messageHead_926_; lean_object* v_messageCount_927_; lean_object* v_bodyBytesRead_928_; lean_object* v_headerBytesRead_929_; uint8_t v_peerClosed_930_; uint8_t v_inputStopped_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_state_925_ = lean_ctor_get(v_reader_924_, 0);
v_messageHead_926_ = lean_ctor_get(v_reader_924_, 2);
v_messageCount_927_ = lean_ctor_get(v_reader_924_, 3);
v_bodyBytesRead_928_ = lean_ctor_get(v_reader_924_, 4);
v_headerBytesRead_929_ = lean_ctor_get(v_reader_924_, 5);
v_peerClosed_930_ = lean_ctor_get_uint8(v_reader_924_, sizeof(void*)*6);
v_inputStopped_931_ = lean_ctor_get_uint8(v_reader_924_, sizeof(void*)*6 + 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_reader_924_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v_reader_924_, 1);
lean_dec(v_unused_939_);
v___x_933_ = v_reader_924_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_headerBytesRead_929_);
lean_inc(v_bodyBytesRead_928_);
lean_inc(v_messageCount_927_);
lean_inc(v_messageHead_926_);
lean_inc(v_state_925_);
lean_dec(v_reader_924_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_input_923_);
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_state_925_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_input_923_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_messageHead_926_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_messageCount_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v_bodyBytesRead_928_);
lean_ctor_set(v_reuseFailAlloc_937_, 5, v_headerBytesRead_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_937_, sizeof(void*)*6, v_peerClosed_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_937_, sizeof(void*)*6 + 1, v_inputStopped_931_);
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
lean_object* v_state_947_; lean_object* v_input_948_; lean_object* v_messageCount_949_; lean_object* v_bodyBytesRead_950_; lean_object* v_headerBytesRead_951_; uint8_t v_peerClosed_952_; uint8_t v_inputStopped_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_state_947_ = lean_ctor_get(v_reader_946_, 0);
v_input_948_ = lean_ctor_get(v_reader_946_, 1);
v_messageCount_949_ = lean_ctor_get(v_reader_946_, 3);
v_bodyBytesRead_950_ = lean_ctor_get(v_reader_946_, 4);
v_headerBytesRead_951_ = lean_ctor_get(v_reader_946_, 5);
v_peerClosed_952_ = lean_ctor_get_uint8(v_reader_946_, sizeof(void*)*6);
v_inputStopped_953_ = lean_ctor_get_uint8(v_reader_946_, sizeof(void*)*6 + 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_reader_946_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v_reader_946_, 2);
lean_dec(v_unused_961_);
v___x_955_ = v_reader_946_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_headerBytesRead_951_);
lean_inc(v_bodyBytesRead_950_);
lean_inc(v_messageCount_949_);
lean_inc(v_input_948_);
lean_inc(v_state_947_);
lean_dec(v_reader_946_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 2, v_messageHead_945_);
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_state_947_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_input_948_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_messageHead_945_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_messageCount_949_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_bodyBytesRead_950_);
lean_ctor_set(v_reuseFailAlloc_959_, 5, v_headerBytesRead_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*6, v_peerClosed_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*6 + 1, v_inputStopped_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead(uint8_t v_dir_962_, lean_object* v_messageHead_963_, lean_object* v_reader_964_){
_start:
{
lean_object* v_state_965_; lean_object* v_input_966_; lean_object* v_messageCount_967_; lean_object* v_bodyBytesRead_968_; lean_object* v_headerBytesRead_969_; uint8_t v_peerClosed_970_; uint8_t v_inputStopped_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_state_965_ = lean_ctor_get(v_reader_964_, 0);
v_input_966_ = lean_ctor_get(v_reader_964_, 1);
v_messageCount_967_ = lean_ctor_get(v_reader_964_, 3);
v_bodyBytesRead_968_ = lean_ctor_get(v_reader_964_, 4);
v_headerBytesRead_969_ = lean_ctor_get(v_reader_964_, 5);
v_peerClosed_970_ = lean_ctor_get_uint8(v_reader_964_, sizeof(void*)*6);
v_inputStopped_971_ = lean_ctor_get_uint8(v_reader_964_, sizeof(void*)*6 + 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_reader_964_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v_reader_964_, 2);
lean_dec(v_unused_979_);
v___x_973_ = v_reader_964_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_headerBytesRead_969_);
lean_inc(v_bodyBytesRead_968_);
lean_inc(v_messageCount_967_);
lean_inc(v_input_966_);
lean_inc(v_state_965_);
lean_dec(v_reader_964_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v_messageHead_963_);
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_state_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_input_966_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_messageHead_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_messageCount_967_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_bodyBytesRead_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 5, v_headerBytesRead_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*6, v_peerClosed_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*6 + 1, v_inputStopped_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(lean_object* v_dir_980_, lean_object* v_messageHead_981_, lean_object* v_reader_982_){
_start:
{
uint8_t v_dir_boxed_983_; lean_object* v_res_984_; 
v_dir_boxed_983_ = lean_unbox(v_dir_980_);
v_res_984_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(v_dir_boxed_983_, v_messageHead_981_, v_reader_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader(uint8_t v_dir_985_, lean_object* v_name_986_, lean_object* v_value_987_, lean_object* v_reader_988_){
_start:
{
if (v_dir_985_ == 0)
{
lean_object* v_messageHead_989_; lean_object* v_state_990_; lean_object* v_input_991_; lean_object* v_messageCount_992_; lean_object* v_bodyBytesRead_993_; lean_object* v_headerBytesRead_994_; uint8_t v_peerClosed_995_; uint8_t v_inputStopped_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1018_; 
v_messageHead_989_ = lean_ctor_get(v_reader_988_, 2);
v_state_990_ = lean_ctor_get(v_reader_988_, 0);
v_input_991_ = lean_ctor_get(v_reader_988_, 1);
v_messageCount_992_ = lean_ctor_get(v_reader_988_, 3);
v_bodyBytesRead_993_ = lean_ctor_get(v_reader_988_, 4);
v_headerBytesRead_994_ = lean_ctor_get(v_reader_988_, 5);
v_peerClosed_995_ = lean_ctor_get_uint8(v_reader_988_, sizeof(void*)*6);
v_inputStopped_996_ = lean_ctor_get_uint8(v_reader_988_, sizeof(void*)*6 + 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_reader_988_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_998_ = v_reader_988_;
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_headerBytesRead_994_);
lean_inc(v_bodyBytesRead_993_);
lean_inc(v_messageCount_992_);
lean_inc(v_messageHead_989_);
lean_inc(v_input_991_);
lean_inc(v_state_990_);
lean_dec(v_reader_988_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
uint8_t v_method_1000_; uint8_t v_version_1001_; lean_object* v_uri_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1015_; 
v_method_1000_ = lean_ctor_get_uint8(v_messageHead_989_, sizeof(void*)*2);
v_version_1001_ = lean_ctor_get_uint8(v_messageHead_989_, sizeof(void*)*2 + 1);
v_uri_1002_ = lean_ctor_get(v_messageHead_989_, 0);
lean_inc(v_uri_1002_);
v___x_1003_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_985_, v_messageHead_989_);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_messageHead_989_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; lean_object* v_unused_1017_; 
v_unused_1016_ = lean_ctor_get(v_messageHead_989_, 1);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_messageHead_989_, 0);
lean_dec(v_unused_1017_);
v___x_1005_ = v_messageHead_989_;
v_isShared_1006_ = v_isSharedCheck_1015_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_messageHead_989_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1015_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_name_986_);
lean_ctor_set(v___x_1007_, 1, v_value_987_);
v___x_1008_ = lean_array_push(v___x_1003_, v___x_1007_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v___x_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_uri_1002_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1014_, sizeof(void*)*2, v_method_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1014_, sizeof(void*)*2 + 1, v_version_1001_);
v___x_1010_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 2, v___x_1010_);
v___x_1012_ = v___x_998_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_state_990_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_input_991_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_messageCount_992_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_bodyBytesRead_993_);
lean_ctor_set(v_reuseFailAlloc_1013_, 5, v_headerBytesRead_994_);
lean_ctor_set_uint8(v_reuseFailAlloc_1013_, sizeof(void*)*6, v_peerClosed_995_);
lean_ctor_set_uint8(v_reuseFailAlloc_1013_, sizeof(void*)*6 + 1, v_inputStopped_996_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
else
{
lean_object* v_messageHead_1019_; lean_object* v_state_1020_; lean_object* v_input_1021_; lean_object* v_messageCount_1022_; lean_object* v_bodyBytesRead_1023_; lean_object* v_headerBytesRead_1024_; uint8_t v_peerClosed_1025_; uint8_t v_inputStopped_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1047_; 
v_messageHead_1019_ = lean_ctor_get(v_reader_988_, 2);
v_state_1020_ = lean_ctor_get(v_reader_988_, 0);
v_input_1021_ = lean_ctor_get(v_reader_988_, 1);
v_messageCount_1022_ = lean_ctor_get(v_reader_988_, 3);
v_bodyBytesRead_1023_ = lean_ctor_get(v_reader_988_, 4);
v_headerBytesRead_1024_ = lean_ctor_get(v_reader_988_, 5);
v_peerClosed_1025_ = lean_ctor_get_uint8(v_reader_988_, sizeof(void*)*6);
v_inputStopped_1026_ = lean_ctor_get_uint8(v_reader_988_, sizeof(void*)*6 + 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_reader_988_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1028_ = v_reader_988_;
v_isShared_1029_ = v_isSharedCheck_1047_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_headerBytesRead_1024_);
lean_inc(v_bodyBytesRead_1023_);
lean_inc(v_messageCount_1022_);
lean_inc(v_messageHead_1019_);
lean_inc(v_input_1021_);
lean_inc(v_state_1020_);
lean_dec(v_reader_988_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1047_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_status_1030_; uint8_t v_version_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1044_; 
v_status_1030_ = lean_ctor_get(v_messageHead_1019_, 0);
lean_inc(v_status_1030_);
v_version_1031_ = lean_ctor_get_uint8(v_messageHead_1019_, sizeof(void*)*2);
v___x_1032_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_985_, v_messageHead_1019_);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_messageHead_1019_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; lean_object* v_unused_1046_; 
v_unused_1045_ = lean_ctor_get(v_messageHead_1019_, 1);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v_messageHead_1019_, 0);
lean_dec(v_unused_1046_);
v___x_1034_ = v_messageHead_1019_;
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v_messageHead_1019_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_name_986_);
lean_ctor_set(v___x_1036_, 1, v_value_987_);
v___x_1037_ = lean_array_push(v___x_1032_, v___x_1036_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1037_);
v___x_1039_ = v___x_1034_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_status_1030_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*2, v_version_1031_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 2, v___x_1039_);
v___x_1041_ = v___x_1028_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_state_1020_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_input_1021_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_messageCount_1022_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_bodyBytesRead_1023_);
lean_ctor_set(v_reuseFailAlloc_1042_, 5, v_headerBytesRead_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*6, v_peerClosed_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*6 + 1, v_inputStopped_1026_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___boxed(lean_object* v_dir_1048_, lean_object* v_name_1049_, lean_object* v_value_1050_, lean_object* v_reader_1051_){
_start:
{
uint8_t v_dir_boxed_1052_; lean_object* v_res_1053_; 
v_dir_boxed_1052_ = lean_unbox(v_dir_1048_);
v_res_1053_ = l_Std_Http_Protocol_H1_Reader_addHeader(v_dir_boxed_1052_, v_name_1049_, v_value_1050_, v_reader_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_replaceLastHeader(uint8_t v_dir_1055_, lean_object* v_name_1056_, lean_object* v_value_1057_, lean_object* v_reader_1058_){
_start:
{
if (v_dir_1055_ == 0)
{
lean_object* v_messageHead_1059_; lean_object* v_state_1060_; lean_object* v_input_1061_; lean_object* v_messageCount_1062_; lean_object* v_bodyBytesRead_1063_; lean_object* v_headerBytesRead_1064_; uint8_t v_peerClosed_1065_; uint8_t v_inputStopped_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1086_; 
v_messageHead_1059_ = lean_ctor_get(v_reader_1058_, 2);
v_state_1060_ = lean_ctor_get(v_reader_1058_, 0);
v_input_1061_ = lean_ctor_get(v_reader_1058_, 1);
v_messageCount_1062_ = lean_ctor_get(v_reader_1058_, 3);
v_bodyBytesRead_1063_ = lean_ctor_get(v_reader_1058_, 4);
v_headerBytesRead_1064_ = lean_ctor_get(v_reader_1058_, 5);
v_peerClosed_1065_ = lean_ctor_get_uint8(v_reader_1058_, sizeof(void*)*6);
v_inputStopped_1066_ = lean_ctor_get_uint8(v_reader_1058_, sizeof(void*)*6 + 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_reader_1058_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1068_ = v_reader_1058_;
v_isShared_1069_ = v_isSharedCheck_1086_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_headerBytesRead_1064_);
lean_inc(v_bodyBytesRead_1063_);
lean_inc(v_messageCount_1062_);
lean_inc(v_messageHead_1059_);
lean_inc(v_input_1061_);
lean_inc(v_state_1060_);
lean_dec(v_reader_1058_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1086_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
uint8_t v_method_1070_; uint8_t v_version_1071_; lean_object* v_uri_1072_; lean_object* v___y_1074_; lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v_i_1082_; uint8_t v___x_1083_; 
v_method_1070_ = lean_ctor_get_uint8(v_messageHead_1059_, sizeof(void*)*2);
v_version_1071_ = lean_ctor_get_uint8(v_messageHead_1059_, sizeof(void*)*2 + 1);
v_uri_1072_ = lean_ctor_get(v_messageHead_1059_, 0);
lean_inc(v_uri_1072_);
v___x_1079_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1055_, v_messageHead_1059_);
lean_dec(v_messageHead_1059_);
v___f_1080_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_replaceLastHeader___closed__0));
v___x_1081_ = lean_array_get_size(v___x_1079_);
lean_inc_ref(v_name_1056_);
v_i_1082_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v___f_1080_, v___x_1079_, v_name_1056_, v___x_1081_);
v___x_1083_ = lean_nat_dec_lt(v_i_1082_, v___x_1081_);
if (v___x_1083_ == 0)
{
lean_dec(v_i_1082_);
lean_dec_ref(v_value_1057_);
lean_dec_ref(v_name_1056_);
v___y_1074_ = v___x_1079_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_name_1056_);
lean_ctor_set(v___x_1084_, 1, v_value_1057_);
v___x_1085_ = lean_array_fset(v___x_1079_, v_i_1082_, v___x_1084_);
lean_dec(v_i_1082_);
v___y_1074_ = v___x_1085_;
goto v___jp_1073_;
}
v___jp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1075_, 0, v_uri_1072_);
lean_ctor_set(v___x_1075_, 1, v___y_1074_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*2, v_method_1070_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*2 + 1, v_version_1071_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 2, v___x_1075_);
v___x_1077_ = v___x_1068_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_state_1060_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_input_1061_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_messageCount_1062_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v_bodyBytesRead_1063_);
lean_ctor_set(v_reuseFailAlloc_1078_, 5, v_headerBytesRead_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*6, v_peerClosed_1065_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*6 + 1, v_inputStopped_1066_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_messageHead_1087_; lean_object* v_state_1088_; lean_object* v_input_1089_; lean_object* v_messageCount_1090_; lean_object* v_bodyBytesRead_1091_; lean_object* v_headerBytesRead_1092_; uint8_t v_peerClosed_1093_; uint8_t v_inputStopped_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1113_; 
v_messageHead_1087_ = lean_ctor_get(v_reader_1058_, 2);
v_state_1088_ = lean_ctor_get(v_reader_1058_, 0);
v_input_1089_ = lean_ctor_get(v_reader_1058_, 1);
v_messageCount_1090_ = lean_ctor_get(v_reader_1058_, 3);
v_bodyBytesRead_1091_ = lean_ctor_get(v_reader_1058_, 4);
v_headerBytesRead_1092_ = lean_ctor_get(v_reader_1058_, 5);
v_peerClosed_1093_ = lean_ctor_get_uint8(v_reader_1058_, sizeof(void*)*6);
v_inputStopped_1094_ = lean_ctor_get_uint8(v_reader_1058_, sizeof(void*)*6 + 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_reader_1058_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1096_ = v_reader_1058_;
v_isShared_1097_ = v_isSharedCheck_1113_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_headerBytesRead_1092_);
lean_inc(v_bodyBytesRead_1091_);
lean_inc(v_messageCount_1090_);
lean_inc(v_messageHead_1087_);
lean_inc(v_input_1089_);
lean_inc(v_state_1088_);
lean_dec(v_reader_1058_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1113_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_status_1098_; uint8_t v_version_1099_; lean_object* v___y_1101_; lean_object* v___x_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v_i_1109_; uint8_t v___x_1110_; 
v_status_1098_ = lean_ctor_get(v_messageHead_1087_, 0);
lean_inc(v_status_1098_);
v_version_1099_ = lean_ctor_get_uint8(v_messageHead_1087_, sizeof(void*)*2);
v___x_1106_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1055_, v_messageHead_1087_);
lean_dec(v_messageHead_1087_);
v___f_1107_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_replaceLastHeader___closed__0));
v___x_1108_ = lean_array_get_size(v___x_1106_);
lean_inc_ref(v_name_1056_);
v_i_1109_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v___f_1107_, v___x_1106_, v_name_1056_, v___x_1108_);
v___x_1110_ = lean_nat_dec_lt(v_i_1109_, v___x_1108_);
if (v___x_1110_ == 0)
{
lean_dec(v_i_1109_);
lean_dec_ref(v_value_1057_);
lean_dec_ref(v_name_1056_);
v___y_1101_ = v___x_1106_;
goto v___jp_1100_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v_name_1056_);
lean_ctor_set(v___x_1111_, 1, v_value_1057_);
v___x_1112_ = lean_array_fset(v___x_1106_, v_i_1109_, v___x_1111_);
lean_dec(v_i_1109_);
v___y_1101_ = v___x_1112_;
goto v___jp_1100_;
}
v___jp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1102_, 0, v_status_1098_);
lean_ctor_set(v___x_1102_, 1, v___y_1101_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*2, v_version_1099_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 2, v___x_1102_);
v___x_1104_ = v___x_1096_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_state_1088_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_input_1089_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_messageCount_1090_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_bodyBytesRead_1091_);
lean_ctor_set(v_reuseFailAlloc_1105_, 5, v_headerBytesRead_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*6, v_peerClosed_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*6 + 1, v_inputStopped_1094_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_replaceLastHeader___boxed(lean_object* v_dir_1114_, lean_object* v_name_1115_, lean_object* v_value_1116_, lean_object* v_reader_1117_){
_start:
{
uint8_t v_dir_boxed_1118_; lean_object* v_res_1119_; 
v_dir_boxed_1118_ = lean_unbox(v_dir_1114_);
v_res_1119_ = l_Std_Http_Protocol_H1_Reader_replaceLastHeader(v_dir_boxed_1118_, v_name_1115_, v_value_1116_, v_reader_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object* v_reader_1120_){
_start:
{
lean_object* v_input_1121_; lean_object* v_messageHead_1122_; lean_object* v_messageCount_1123_; lean_object* v_bodyBytesRead_1124_; lean_object* v_headerBytesRead_1125_; uint8_t v_peerClosed_1126_; uint8_t v_inputStopped_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1137_; 
v_input_1121_ = lean_ctor_get(v_reader_1120_, 1);
v_messageHead_1122_ = lean_ctor_get(v_reader_1120_, 2);
v_messageCount_1123_ = lean_ctor_get(v_reader_1120_, 3);
v_bodyBytesRead_1124_ = lean_ctor_get(v_reader_1120_, 4);
v_headerBytesRead_1125_ = lean_ctor_get(v_reader_1120_, 5);
v_peerClosed_1126_ = lean_ctor_get_uint8(v_reader_1120_, sizeof(void*)*6);
v_inputStopped_1127_ = lean_ctor_get_uint8(v_reader_1120_, sizeof(void*)*6 + 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_reader_1120_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v_reader_1120_, 0);
lean_dec(v_unused_1138_);
v___x_1129_ = v_reader_1120_;
v_isShared_1130_ = v_isSharedCheck_1137_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_headerBytesRead_1125_);
lean_inc(v_bodyBytesRead_1124_);
lean_inc(v_messageCount_1123_);
lean_inc(v_messageHead_1122_);
lean_inc(v_input_1121_);
lean_dec(v_reader_1120_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1137_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1131_ = lean_box(5);
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_add(v_messageCount_1123_, v___x_1132_);
lean_dec(v_messageCount_1123_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 3, v___x_1133_);
lean_ctor_set(v___x_1129_, 0, v___x_1131_);
v___x_1135_ = v___x_1129_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_input_1121_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_messageHead_1122_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_bodyBytesRead_1124_);
lean_ctor_set(v_reuseFailAlloc_1136_, 5, v_headerBytesRead_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1136_, sizeof(void*)*6, v_peerClosed_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1136_, sizeof(void*)*6 + 1, v_inputStopped_1127_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t v_dir_1139_, lean_object* v_reader_1140_){
_start:
{
lean_object* v_input_1141_; lean_object* v_messageHead_1142_; lean_object* v_messageCount_1143_; lean_object* v_bodyBytesRead_1144_; lean_object* v_headerBytesRead_1145_; uint8_t v_peerClosed_1146_; uint8_t v_inputStopped_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1157_; 
v_input_1141_ = lean_ctor_get(v_reader_1140_, 1);
v_messageHead_1142_ = lean_ctor_get(v_reader_1140_, 2);
v_messageCount_1143_ = lean_ctor_get(v_reader_1140_, 3);
v_bodyBytesRead_1144_ = lean_ctor_get(v_reader_1140_, 4);
v_headerBytesRead_1145_ = lean_ctor_get(v_reader_1140_, 5);
v_peerClosed_1146_ = lean_ctor_get_uint8(v_reader_1140_, sizeof(void*)*6);
v_inputStopped_1147_ = lean_ctor_get_uint8(v_reader_1140_, sizeof(void*)*6 + 1);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_reader_1140_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_reader_1140_, 0);
lean_dec(v_unused_1158_);
v___x_1149_ = v_reader_1140_;
v_isShared_1150_ = v_isSharedCheck_1157_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_headerBytesRead_1145_);
lean_inc(v_bodyBytesRead_1144_);
lean_inc(v_messageCount_1143_);
lean_inc(v_messageHead_1142_);
lean_inc(v_input_1141_);
lean_dec(v_reader_1140_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1157_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1151_ = lean_box(5);
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_nat_add(v_messageCount_1143_, v___x_1152_);
lean_dec(v_messageCount_1143_);
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
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_input_1141_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_messageHead_1142_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_bodyBytesRead_1144_);
lean_ctor_set(v_reuseFailAlloc_1156_, 5, v_headerBytesRead_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1156_, sizeof(void*)*6, v_peerClosed_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1156_, sizeof(void*)*6 + 1, v_inputStopped_1147_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t v_dir_1163_, lean_object* v_reader_1164_){
_start:
{
lean_object* v_input_1165_; lean_object* v_messageCount_1166_; uint8_t v_peerClosed_1167_; uint8_t v_inputStopped_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1178_; 
v_input_1165_ = lean_ctor_get(v_reader_1164_, 1);
v_messageCount_1166_ = lean_ctor_get(v_reader_1164_, 3);
v_peerClosed_1167_ = lean_ctor_get_uint8(v_reader_1164_, sizeof(void*)*6);
v_inputStopped_1168_ = lean_ctor_get_uint8(v_reader_1164_, sizeof(void*)*6 + 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_reader_1164_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; 
v_unused_1179_ = lean_ctor_get(v_reader_1164_, 5);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_reader_1164_, 4);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_reader_1164_, 2);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_reader_1164_, 0);
lean_dec(v_unused_1182_);
v___x_1170_ = v_reader_1164_;
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_messageCount_1166_);
lean_inc(v_input_1165_);
lean_dec(v_reader_1164_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_1163_);
v___x_1174_ = lean_unsigned_to_nat(0u);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 5, v___x_1174_);
lean_ctor_set(v___x_1170_, 4, v___x_1174_);
lean_ctor_set(v___x_1170_, 2, v___x_1173_);
lean_ctor_set(v___x_1170_, 0, v___x_1172_);
v___x_1176_ = v___x_1170_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_input_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_messageCount_1166_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v___x_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1177_, sizeof(void*)*6, v_peerClosed_1167_);
lean_ctor_set_uint8(v_reuseFailAlloc_1177_, sizeof(void*)*6 + 1, v_inputStopped_1168_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object* v_dir_1183_, lean_object* v_reader_1184_){
_start:
{
uint8_t v_dir_boxed_1185_; lean_object* v_res_1186_; 
v_dir_boxed_1185_ = lean_unbox(v_dir_1183_);
v_res_1186_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_1185_, v_reader_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object* v_reader_1187_){
_start:
{
lean_object* v_input_1188_; lean_object* v_state_1189_; uint8_t v_peerClosed_1190_; uint8_t v_inputStopped_1191_; lean_object* v_array_1192_; lean_object* v_idx_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v_input_1188_ = lean_ctor_get(v_reader_1187_, 1);
v_state_1189_ = lean_ctor_get(v_reader_1187_, 0);
v_peerClosed_1190_ = lean_ctor_get_uint8(v_reader_1187_, sizeof(void*)*6);
v_inputStopped_1191_ = lean_ctor_get_uint8(v_reader_1187_, sizeof(void*)*6 + 1);
v_array_1192_ = lean_ctor_get(v_input_1188_, 0);
v_idx_1193_ = lean_ctor_get(v_input_1188_, 1);
v___x_1194_ = lean_byte_array_size(v_array_1192_);
v___x_1195_ = lean_nat_dec_le(v___x_1194_, v_idx_1193_);
if (v___x_1195_ == 0)
{
return v___x_1195_;
}
else
{
if (v_peerClosed_1190_ == 0)
{
if (v_inputStopped_1191_ == 0)
{
switch(lean_obj_tag(v_state_1189_))
{
case 5:
{
return v_inputStopped_1191_;
}
case 6:
{
return v_inputStopped_1191_;
}
case 3:
{
return v_inputStopped_1191_;
}
default: 
{
return v___x_1195_;
}
}
}
else
{
return v_peerClosed_1190_;
}
}
else
{
uint8_t v___x_1196_; 
v___x_1196_ = 0;
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object* v_reader_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_1197_);
lean_dec_ref(v_reader_1197_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t v_dir_1200_, lean_object* v_reader_1201_){
_start:
{
lean_object* v_input_1202_; lean_object* v_state_1203_; uint8_t v_peerClosed_1204_; uint8_t v_inputStopped_1205_; lean_object* v_array_1206_; lean_object* v_idx_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_input_1202_ = lean_ctor_get(v_reader_1201_, 1);
v_state_1203_ = lean_ctor_get(v_reader_1201_, 0);
v_peerClosed_1204_ = lean_ctor_get_uint8(v_reader_1201_, sizeof(void*)*6);
v_inputStopped_1205_ = lean_ctor_get_uint8(v_reader_1201_, sizeof(void*)*6 + 1);
v_array_1206_ = lean_ctor_get(v_input_1202_, 0);
v_idx_1207_ = lean_ctor_get(v_input_1202_, 1);
v___x_1208_ = lean_byte_array_size(v_array_1206_);
v___x_1209_ = lean_nat_dec_le(v___x_1208_, v_idx_1207_);
if (v___x_1209_ == 0)
{
return v___x_1209_;
}
else
{
if (v_peerClosed_1204_ == 0)
{
if (v_inputStopped_1205_ == 0)
{
switch(lean_obj_tag(v_state_1203_))
{
case 5:
{
return v_inputStopped_1205_;
}
case 6:
{
return v_inputStopped_1205_;
}
case 3:
{
return v_inputStopped_1205_;
}
default: 
{
return v___x_1209_;
}
}
}
else
{
return v_peerClosed_1204_;
}
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object* v_dir_1211_, lean_object* v_reader_1212_){
_start:
{
uint8_t v_dir_boxed_1213_; uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_dir_boxed_1213_ = lean_unbox(v_dir_1211_);
v_res_1214_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_1213_, v_reader_1212_);
lean_dec_ref(v_reader_1212_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(lean_object* v_reader_1216_){
_start:
{
lean_object* v_input_1217_; lean_object* v_array_1218_; lean_object* v_idx_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_input_1217_ = lean_ctor_get(v_reader_1216_, 1);
v_array_1218_ = lean_ctor_get(v_input_1217_, 0);
v_idx_1219_ = lean_ctor_get(v_input_1217_, 1);
v___x_1220_ = lean_byte_array_size(v_array_1218_);
v___x_1221_ = lean_nat_sub(v___x_1220_, v_idx_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(lean_object* v_reader_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_1222_);
lean_dec_ref(v_reader_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes(uint8_t v_dir_1224_, lean_object* v_reader_1225_){
_start:
{
lean_object* v_input_1226_; lean_object* v_array_1227_; lean_object* v_idx_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_input_1226_ = lean_ctor_get(v_reader_1225_, 1);
v_array_1227_ = lean_ctor_get(v_input_1226_, 0);
v_idx_1228_ = lean_ctor_get(v_input_1226_, 1);
v___x_1229_ = lean_byte_array_size(v_array_1227_);
v___x_1230_ = lean_nat_sub(v___x_1229_, v_idx_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(lean_object* v_dir_1231_, lean_object* v_reader_1232_){
_start:
{
uint8_t v_dir_boxed_1233_; lean_object* v_res_1234_; 
v_dir_boxed_1233_ = lean_unbox(v_dir_1231_);
v_res_1234_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_1233_, v_reader_1232_);
lean_dec_ref(v_reader_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg(lean_object* v_n_1235_, lean_object* v_reader_1236_){
_start:
{
lean_object* v_input_1237_; lean_object* v_state_1238_; lean_object* v_messageHead_1239_; lean_object* v_messageCount_1240_; lean_object* v_bodyBytesRead_1241_; lean_object* v_headerBytesRead_1242_; uint8_t v_peerClosed_1243_; uint8_t v_inputStopped_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1261_; 
v_input_1237_ = lean_ctor_get(v_reader_1236_, 1);
v_state_1238_ = lean_ctor_get(v_reader_1236_, 0);
v_messageHead_1239_ = lean_ctor_get(v_reader_1236_, 2);
v_messageCount_1240_ = lean_ctor_get(v_reader_1236_, 3);
v_bodyBytesRead_1241_ = lean_ctor_get(v_reader_1236_, 4);
v_headerBytesRead_1242_ = lean_ctor_get(v_reader_1236_, 5);
v_peerClosed_1243_ = lean_ctor_get_uint8(v_reader_1236_, sizeof(void*)*6);
v_inputStopped_1244_ = lean_ctor_get_uint8(v_reader_1236_, sizeof(void*)*6 + 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_reader_1236_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1246_ = v_reader_1236_;
v_isShared_1247_ = v_isSharedCheck_1261_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_headerBytesRead_1242_);
lean_inc(v_bodyBytesRead_1241_);
lean_inc(v_messageCount_1240_);
lean_inc(v_messageHead_1239_);
lean_inc(v_input_1237_);
lean_inc(v_state_1238_);
lean_dec(v_reader_1236_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1261_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_array_1248_; lean_object* v_idx_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1260_; 
v_array_1248_ = lean_ctor_get(v_input_1237_, 0);
v_idx_1249_ = lean_ctor_get(v_input_1237_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_input_1237_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1251_ = v_input_1237_;
v_isShared_1252_ = v_isSharedCheck_1260_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_idx_1249_);
lean_inc(v_array_1248_);
lean_dec(v_input_1237_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1260_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_nat_add(v_idx_1249_, v_n_1235_);
lean_dec(v_idx_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_array_1248_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1257_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1255_);
v___x_1257_ = v___x_1246_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_state_1238_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_messageHead_1239_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_messageCount_1240_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_bodyBytesRead_1241_);
lean_ctor_set(v_reuseFailAlloc_1258_, 5, v_headerBytesRead_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1258_, sizeof(void*)*6, v_peerClosed_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1258_, sizeof(void*)*6 + 1, v_inputStopped_1244_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(lean_object* v_n_1262_, lean_object* v_reader_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_1262_, v_reader_1263_);
lean_dec(v_n_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance(uint8_t v_dir_1265_, lean_object* v_n_1266_, lean_object* v_reader_1267_){
_start:
{
lean_object* v_input_1268_; lean_object* v_state_1269_; lean_object* v_messageHead_1270_; lean_object* v_messageCount_1271_; lean_object* v_bodyBytesRead_1272_; lean_object* v_headerBytesRead_1273_; uint8_t v_peerClosed_1274_; uint8_t v_inputStopped_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1292_; 
v_input_1268_ = lean_ctor_get(v_reader_1267_, 1);
v_state_1269_ = lean_ctor_get(v_reader_1267_, 0);
v_messageHead_1270_ = lean_ctor_get(v_reader_1267_, 2);
v_messageCount_1271_ = lean_ctor_get(v_reader_1267_, 3);
v_bodyBytesRead_1272_ = lean_ctor_get(v_reader_1267_, 4);
v_headerBytesRead_1273_ = lean_ctor_get(v_reader_1267_, 5);
v_peerClosed_1274_ = lean_ctor_get_uint8(v_reader_1267_, sizeof(void*)*6);
v_inputStopped_1275_ = lean_ctor_get_uint8(v_reader_1267_, sizeof(void*)*6 + 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_reader_1267_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1277_ = v_reader_1267_;
v_isShared_1278_ = v_isSharedCheck_1292_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_headerBytesRead_1273_);
lean_inc(v_bodyBytesRead_1272_);
lean_inc(v_messageCount_1271_);
lean_inc(v_messageHead_1270_);
lean_inc(v_input_1268_);
lean_inc(v_state_1269_);
lean_dec(v_reader_1267_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1292_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_array_1279_; lean_object* v_idx_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1291_; 
v_array_1279_ = lean_ctor_get(v_input_1268_, 0);
v_idx_1280_ = lean_ctor_get(v_input_1268_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_input_1268_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1282_ = v_input_1268_;
v_isShared_1283_ = v_isSharedCheck_1291_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_idx_1280_);
lean_inc(v_array_1279_);
lean_dec(v_input_1268_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1291_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = lean_nat_add(v_idx_1280_, v_n_1266_);
lean_dec(v_idx_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_array_1279_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1286_);
v___x_1288_ = v___x_1277_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_state_1269_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_messageHead_1270_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_messageCount_1271_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_bodyBytesRead_1272_);
lean_ctor_set(v_reuseFailAlloc_1289_, 5, v_headerBytesRead_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*6, v_peerClosed_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*6 + 1, v_inputStopped_1275_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___boxed(lean_object* v_dir_1293_, lean_object* v_n_1294_, lean_object* v_reader_1295_){
_start:
{
uint8_t v_dir_boxed_1296_; lean_object* v_res_1297_; 
v_dir_boxed_1296_ = lean_unbox(v_dir_1293_);
v_res_1297_ = l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_1296_, v_n_1294_, v_reader_1295_);
lean_dec(v_n_1294_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(lean_object* v_reader_1300_){
_start:
{
lean_object* v_input_1301_; lean_object* v_messageHead_1302_; lean_object* v_messageCount_1303_; uint8_t v_peerClosed_1304_; uint8_t v_inputStopped_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1314_; 
v_input_1301_ = lean_ctor_get(v_reader_1300_, 1);
v_messageHead_1302_ = lean_ctor_get(v_reader_1300_, 2);
v_messageCount_1303_ = lean_ctor_get(v_reader_1300_, 3);
v_peerClosed_1304_ = lean_ctor_get_uint8(v_reader_1300_, sizeof(void*)*6);
v_inputStopped_1305_ = lean_ctor_get_uint8(v_reader_1300_, sizeof(void*)*6 + 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_reader_1300_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; lean_object* v_unused_1316_; lean_object* v_unused_1317_; 
v_unused_1315_ = lean_ctor_get(v_reader_1300_, 5);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_reader_1300_, 4);
lean_dec(v_unused_1316_);
v_unused_1317_ = lean_ctor_get(v_reader_1300_, 0);
lean_dec(v_unused_1317_);
v___x_1307_ = v_reader_1300_;
v_isShared_1308_ = v_isSharedCheck_1314_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_messageCount_1303_);
lean_inc(v_messageHead_1302_);
lean_inc(v_input_1301_);
lean_dec(v_reader_1300_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1314_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 5, v___x_1309_);
lean_ctor_set(v___x_1307_, 4, v___x_1309_);
lean_ctor_set(v___x_1307_, 0, v___x_1310_);
v___x_1312_ = v___x_1307_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_input_1301_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_messageHead_1302_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_messageCount_1303_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1313_, 5, v___x_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1313_, sizeof(void*)*6, v_peerClosed_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1313_, sizeof(void*)*6 + 1, v_inputStopped_1305_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders(uint8_t v_dir_1318_, lean_object* v_reader_1319_){
_start:
{
lean_object* v_input_1320_; lean_object* v_messageHead_1321_; lean_object* v_messageCount_1322_; uint8_t v_peerClosed_1323_; uint8_t v_inputStopped_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1333_; 
v_input_1320_ = lean_ctor_get(v_reader_1319_, 1);
v_messageHead_1321_ = lean_ctor_get(v_reader_1319_, 2);
v_messageCount_1322_ = lean_ctor_get(v_reader_1319_, 3);
v_peerClosed_1323_ = lean_ctor_get_uint8(v_reader_1319_, sizeof(void*)*6);
v_inputStopped_1324_ = lean_ctor_get_uint8(v_reader_1319_, sizeof(void*)*6 + 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_reader_1319_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; lean_object* v_unused_1335_; lean_object* v_unused_1336_; 
v_unused_1334_ = lean_ctor_get(v_reader_1319_, 5);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_reader_1319_, 4);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v_reader_1319_, 0);
lean_dec(v_unused_1336_);
v___x_1326_ = v_reader_1319_;
v_isShared_1327_ = v_isSharedCheck_1333_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_messageCount_1322_);
lean_inc(v_messageHead_1321_);
lean_inc(v_input_1320_);
lean_dec(v_reader_1319_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1333_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 5, v___x_1328_);
lean_ctor_set(v___x_1326_, 4, v___x_1328_);
lean_ctor_set(v___x_1326_, 0, v___x_1329_);
v___x_1331_ = v___x_1326_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_input_1320_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_messageHead_1321_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_messageCount_1322_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1332_, 5, v___x_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*6, v_peerClosed_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*6 + 1, v_inputStopped_1324_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(lean_object* v_dir_1337_, lean_object* v_reader_1338_){
_start:
{
uint8_t v_dir_boxed_1339_; lean_object* v_res_1340_; 
v_dir_boxed_1339_ = lean_unbox(v_dir_1337_);
v_res_1340_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_1339_, v_reader_1338_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(lean_object* v_n_1341_, lean_object* v_reader_1342_){
_start:
{
lean_object* v_state_1343_; lean_object* v_input_1344_; lean_object* v_messageHead_1345_; lean_object* v_messageCount_1346_; lean_object* v_bodyBytesRead_1347_; lean_object* v_headerBytesRead_1348_; uint8_t v_peerClosed_1349_; uint8_t v_inputStopped_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1358_; 
v_state_1343_ = lean_ctor_get(v_reader_1342_, 0);
v_input_1344_ = lean_ctor_get(v_reader_1342_, 1);
v_messageHead_1345_ = lean_ctor_get(v_reader_1342_, 2);
v_messageCount_1346_ = lean_ctor_get(v_reader_1342_, 3);
v_bodyBytesRead_1347_ = lean_ctor_get(v_reader_1342_, 4);
v_headerBytesRead_1348_ = lean_ctor_get(v_reader_1342_, 5);
v_peerClosed_1349_ = lean_ctor_get_uint8(v_reader_1342_, sizeof(void*)*6);
v_inputStopped_1350_ = lean_ctor_get_uint8(v_reader_1342_, sizeof(void*)*6 + 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_reader_1342_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1352_ = v_reader_1342_;
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_headerBytesRead_1348_);
lean_inc(v_bodyBytesRead_1347_);
lean_inc(v_messageCount_1346_);
lean_inc(v_messageHead_1345_);
lean_inc(v_input_1344_);
lean_inc(v_state_1343_);
lean_dec(v_reader_1342_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_nat_add(v_bodyBytesRead_1347_, v_n_1341_);
lean_dec(v_bodyBytesRead_1347_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 4, v___x_1354_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_state_1343_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_input_1344_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_messageHead_1345_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_messageCount_1346_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_headerBytesRead_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1357_, sizeof(void*)*6, v_peerClosed_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1357_, sizeof(void*)*6 + 1, v_inputStopped_1350_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(lean_object* v_n_1359_, lean_object* v_reader_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_1359_, v_reader_1360_);
lean_dec(v_n_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes(uint8_t v_dir_1362_, lean_object* v_n_1363_, lean_object* v_reader_1364_){
_start:
{
lean_object* v_state_1365_; lean_object* v_input_1366_; lean_object* v_messageHead_1367_; lean_object* v_messageCount_1368_; lean_object* v_bodyBytesRead_1369_; lean_object* v_headerBytesRead_1370_; uint8_t v_peerClosed_1371_; uint8_t v_inputStopped_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1380_; 
v_state_1365_ = lean_ctor_get(v_reader_1364_, 0);
v_input_1366_ = lean_ctor_get(v_reader_1364_, 1);
v_messageHead_1367_ = lean_ctor_get(v_reader_1364_, 2);
v_messageCount_1368_ = lean_ctor_get(v_reader_1364_, 3);
v_bodyBytesRead_1369_ = lean_ctor_get(v_reader_1364_, 4);
v_headerBytesRead_1370_ = lean_ctor_get(v_reader_1364_, 5);
v_peerClosed_1371_ = lean_ctor_get_uint8(v_reader_1364_, sizeof(void*)*6);
v_inputStopped_1372_ = lean_ctor_get_uint8(v_reader_1364_, sizeof(void*)*6 + 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_reader_1364_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1374_ = v_reader_1364_;
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_headerBytesRead_1370_);
lean_inc(v_bodyBytesRead_1369_);
lean_inc(v_messageCount_1368_);
lean_inc(v_messageHead_1367_);
lean_inc(v_input_1366_);
lean_inc(v_state_1365_);
lean_dec(v_reader_1364_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = lean_nat_add(v_bodyBytesRead_1369_, v_n_1363_);
lean_dec(v_bodyBytesRead_1369_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 4, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_state_1365_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_input_1366_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_messageHead_1367_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_messageCount_1368_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1379_, 5, v_headerBytesRead_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, sizeof(void*)*6, v_peerClosed_1371_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, sizeof(void*)*6 + 1, v_inputStopped_1372_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(lean_object* v_dir_1381_, lean_object* v_n_1382_, lean_object* v_reader_1383_){
_start:
{
uint8_t v_dir_boxed_1384_; lean_object* v_res_1385_; 
v_dir_boxed_1384_ = lean_unbox(v_dir_1381_);
v_res_1385_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_1384_, v_n_1382_, v_reader_1383_);
lean_dec(v_n_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(lean_object* v_n_1386_, lean_object* v_reader_1387_){
_start:
{
lean_object* v_state_1388_; lean_object* v_input_1389_; lean_object* v_messageHead_1390_; lean_object* v_messageCount_1391_; lean_object* v_bodyBytesRead_1392_; lean_object* v_headerBytesRead_1393_; uint8_t v_peerClosed_1394_; uint8_t v_inputStopped_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1403_; 
v_state_1388_ = lean_ctor_get(v_reader_1387_, 0);
v_input_1389_ = lean_ctor_get(v_reader_1387_, 1);
v_messageHead_1390_ = lean_ctor_get(v_reader_1387_, 2);
v_messageCount_1391_ = lean_ctor_get(v_reader_1387_, 3);
v_bodyBytesRead_1392_ = lean_ctor_get(v_reader_1387_, 4);
v_headerBytesRead_1393_ = lean_ctor_get(v_reader_1387_, 5);
v_peerClosed_1394_ = lean_ctor_get_uint8(v_reader_1387_, sizeof(void*)*6);
v_inputStopped_1395_ = lean_ctor_get_uint8(v_reader_1387_, sizeof(void*)*6 + 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_reader_1387_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1397_ = v_reader_1387_;
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_headerBytesRead_1393_);
lean_inc(v_bodyBytesRead_1392_);
lean_inc(v_messageCount_1391_);
lean_inc(v_messageHead_1390_);
lean_inc(v_input_1389_);
lean_inc(v_state_1388_);
lean_dec(v_reader_1387_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = lean_nat_add(v_headerBytesRead_1393_, v_n_1386_);
lean_dec(v_headerBytesRead_1393_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 5, v___x_1399_);
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_state_1388_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_input_1389_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_messageHead_1390_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_messageCount_1391_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_bodyBytesRead_1392_);
lean_ctor_set(v_reuseFailAlloc_1402_, 5, v___x_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*6, v_peerClosed_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*6 + 1, v_inputStopped_1395_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(lean_object* v_n_1404_, lean_object* v_reader_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_1404_, v_reader_1405_);
lean_dec(v_n_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes(uint8_t v_dir_1407_, lean_object* v_n_1408_, lean_object* v_reader_1409_){
_start:
{
lean_object* v_state_1410_; lean_object* v_input_1411_; lean_object* v_messageHead_1412_; lean_object* v_messageCount_1413_; lean_object* v_bodyBytesRead_1414_; lean_object* v_headerBytesRead_1415_; uint8_t v_peerClosed_1416_; uint8_t v_inputStopped_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
v_state_1410_ = lean_ctor_get(v_reader_1409_, 0);
v_input_1411_ = lean_ctor_get(v_reader_1409_, 1);
v_messageHead_1412_ = lean_ctor_get(v_reader_1409_, 2);
v_messageCount_1413_ = lean_ctor_get(v_reader_1409_, 3);
v_bodyBytesRead_1414_ = lean_ctor_get(v_reader_1409_, 4);
v_headerBytesRead_1415_ = lean_ctor_get(v_reader_1409_, 5);
v_peerClosed_1416_ = lean_ctor_get_uint8(v_reader_1409_, sizeof(void*)*6);
v_inputStopped_1417_ = lean_ctor_get_uint8(v_reader_1409_, sizeof(void*)*6 + 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_reader_1409_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1419_ = v_reader_1409_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_headerBytesRead_1415_);
lean_inc(v_bodyBytesRead_1414_);
lean_inc(v_messageCount_1413_);
lean_inc(v_messageHead_1412_);
lean_inc(v_input_1411_);
lean_inc(v_state_1410_);
lean_dec(v_reader_1409_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_nat_add(v_headerBytesRead_1415_, v_n_1408_);
lean_dec(v_headerBytesRead_1415_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 5, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_state_1410_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_input_1411_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_messageHead_1412_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_messageCount_1413_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_bodyBytesRead_1414_);
lean_ctor_set(v_reuseFailAlloc_1424_, 5, v___x_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1424_, sizeof(void*)*6, v_peerClosed_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1424_, sizeof(void*)*6 + 1, v_inputStopped_1417_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(lean_object* v_dir_1426_, lean_object* v_n_1427_, lean_object* v_reader_1428_){
_start:
{
uint8_t v_dir_boxed_1429_; lean_object* v_res_1430_; 
v_dir_boxed_1429_ = lean_unbox(v_dir_1426_);
v_res_1430_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_1429_, v_n_1427_, v_reader_1428_);
lean_dec(v_n_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(lean_object* v_size_1431_, lean_object* v_reader_1432_){
_start:
{
lean_object* v_input_1433_; lean_object* v_messageHead_1434_; lean_object* v_messageCount_1435_; lean_object* v_bodyBytesRead_1436_; lean_object* v_headerBytesRead_1437_; uint8_t v_peerClosed_1438_; uint8_t v_inputStopped_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1448_; 
v_input_1433_ = lean_ctor_get(v_reader_1432_, 1);
v_messageHead_1434_ = lean_ctor_get(v_reader_1432_, 2);
v_messageCount_1435_ = lean_ctor_get(v_reader_1432_, 3);
v_bodyBytesRead_1436_ = lean_ctor_get(v_reader_1432_, 4);
v_headerBytesRead_1437_ = lean_ctor_get(v_reader_1432_, 5);
v_peerClosed_1438_ = lean_ctor_get_uint8(v_reader_1432_, sizeof(void*)*6);
v_inputStopped_1439_ = lean_ctor_get_uint8(v_reader_1432_, sizeof(void*)*6 + 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_reader_1432_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v_reader_1432_, 0);
lean_dec(v_unused_1449_);
v___x_1441_ = v_reader_1432_;
v_isShared_1442_ = v_isSharedCheck_1448_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_headerBytesRead_1437_);
lean_inc(v_bodyBytesRead_1436_);
lean_inc(v_messageCount_1435_);
lean_inc(v_messageHead_1434_);
lean_inc(v_input_1433_);
lean_dec(v_reader_1432_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1448_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_size_1431_);
v___x_1444_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1444_);
v___x_1446_ = v___x_1441_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_input_1433_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_messageHead_1434_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_messageCount_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_bodyBytesRead_1436_);
lean_ctor_set(v_reuseFailAlloc_1447_, 5, v_headerBytesRead_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*6, v_peerClosed_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*6 + 1, v_inputStopped_1439_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody(uint8_t v_dir_1450_, lean_object* v_size_1451_, lean_object* v_reader_1452_){
_start:
{
lean_object* v_input_1453_; lean_object* v_messageHead_1454_; lean_object* v_messageCount_1455_; lean_object* v_bodyBytesRead_1456_; lean_object* v_headerBytesRead_1457_; uint8_t v_peerClosed_1458_; uint8_t v_inputStopped_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1468_; 
v_input_1453_ = lean_ctor_get(v_reader_1452_, 1);
v_messageHead_1454_ = lean_ctor_get(v_reader_1452_, 2);
v_messageCount_1455_ = lean_ctor_get(v_reader_1452_, 3);
v_bodyBytesRead_1456_ = lean_ctor_get(v_reader_1452_, 4);
v_headerBytesRead_1457_ = lean_ctor_get(v_reader_1452_, 5);
v_peerClosed_1458_ = lean_ctor_get_uint8(v_reader_1452_, sizeof(void*)*6);
v_inputStopped_1459_ = lean_ctor_get_uint8(v_reader_1452_, sizeof(void*)*6 + 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_reader_1452_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v_reader_1452_, 0);
lean_dec(v_unused_1469_);
v___x_1461_ = v_reader_1452_;
v_isShared_1462_ = v_isSharedCheck_1468_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_headerBytesRead_1457_);
lean_inc(v_bodyBytesRead_1456_);
lean_inc(v_messageCount_1455_);
lean_inc(v_messageHead_1454_);
lean_inc(v_input_1453_);
lean_dec(v_reader_1452_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1468_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_size_1451_);
v___x_1464_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1464_);
v___x_1466_ = v___x_1461_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_input_1453_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_messageHead_1454_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v_messageCount_1455_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_bodyBytesRead_1456_);
lean_ctor_set(v_reuseFailAlloc_1467_, 5, v_headerBytesRead_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*6, v_peerClosed_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*6 + 1, v_inputStopped_1459_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(lean_object* v_dir_1470_, lean_object* v_size_1471_, lean_object* v_reader_1472_){
_start:
{
uint8_t v_dir_boxed_1473_; lean_object* v_res_1474_; 
v_dir_boxed_1473_ = lean_unbox(v_dir_1470_);
v_res_1474_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(v_dir_boxed_1473_, v_size_1471_, v_reader_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(lean_object* v_reader_1477_){
_start:
{
lean_object* v_input_1478_; lean_object* v_messageHead_1479_; lean_object* v_messageCount_1480_; lean_object* v_bodyBytesRead_1481_; lean_object* v_headerBytesRead_1482_; uint8_t v_peerClosed_1483_; uint8_t v_inputStopped_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1492_; 
v_input_1478_ = lean_ctor_get(v_reader_1477_, 1);
v_messageHead_1479_ = lean_ctor_get(v_reader_1477_, 2);
v_messageCount_1480_ = lean_ctor_get(v_reader_1477_, 3);
v_bodyBytesRead_1481_ = lean_ctor_get(v_reader_1477_, 4);
v_headerBytesRead_1482_ = lean_ctor_get(v_reader_1477_, 5);
v_peerClosed_1483_ = lean_ctor_get_uint8(v_reader_1477_, sizeof(void*)*6);
v_inputStopped_1484_ = lean_ctor_get_uint8(v_reader_1477_, sizeof(void*)*6 + 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_reader_1477_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v_reader_1477_, 0);
lean_dec(v_unused_1493_);
v___x_1486_ = v_reader_1477_;
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_headerBytesRead_1482_);
lean_inc(v_bodyBytesRead_1481_);
lean_inc(v_messageCount_1480_);
lean_inc(v_messageHead_1479_);
lean_inc(v_input_1478_);
lean_dec(v_reader_1477_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1488_);
v___x_1490_ = v___x_1486_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_input_1478_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_messageHead_1479_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_messageCount_1480_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_bodyBytesRead_1481_);
lean_ctor_set(v_reuseFailAlloc_1491_, 5, v_headerBytesRead_1482_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*6, v_peerClosed_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*6 + 1, v_inputStopped_1484_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody(uint8_t v_dir_1494_, lean_object* v_reader_1495_){
_start:
{
lean_object* v_input_1496_; lean_object* v_messageHead_1497_; lean_object* v_messageCount_1498_; lean_object* v_bodyBytesRead_1499_; lean_object* v_headerBytesRead_1500_; uint8_t v_peerClosed_1501_; uint8_t v_inputStopped_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1510_; 
v_input_1496_ = lean_ctor_get(v_reader_1495_, 1);
v_messageHead_1497_ = lean_ctor_get(v_reader_1495_, 2);
v_messageCount_1498_ = lean_ctor_get(v_reader_1495_, 3);
v_bodyBytesRead_1499_ = lean_ctor_get(v_reader_1495_, 4);
v_headerBytesRead_1500_ = lean_ctor_get(v_reader_1495_, 5);
v_peerClosed_1501_ = lean_ctor_get_uint8(v_reader_1495_, sizeof(void*)*6);
v_inputStopped_1502_ = lean_ctor_get_uint8(v_reader_1495_, sizeof(void*)*6 + 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_reader_1495_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_reader_1495_, 0);
lean_dec(v_unused_1511_);
v___x_1504_ = v_reader_1495_;
v_isShared_1505_ = v_isSharedCheck_1510_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_headerBytesRead_1500_);
lean_inc(v_bodyBytesRead_1499_);
lean_inc(v_messageCount_1498_);
lean_inc(v_messageHead_1497_);
lean_inc(v_input_1496_);
lean_dec(v_reader_1495_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1510_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1506_);
v___x_1508_ = v___x_1504_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_input_1496_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_messageHead_1497_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_messageCount_1498_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_bodyBytesRead_1499_);
lean_ctor_set(v_reuseFailAlloc_1509_, 5, v_headerBytesRead_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*6, v_peerClosed_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*6 + 1, v_inputStopped_1502_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(lean_object* v_dir_1512_, lean_object* v_reader_1513_){
_start:
{
uint8_t v_dir_boxed_1514_; lean_object* v_res_1515_; 
v_dir_boxed_1514_ = lean_unbox(v_dir_1512_);
v_res_1515_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_1514_, v_reader_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(uint8_t v_dir_1516_, lean_object* v_reader_1517_){
_start:
{
lean_object* v_messageHead_1518_; uint8_t v___x_1519_; 
v_messageHead_1518_ = lean_ctor_get(v_reader_1517_, 2);
v___x_1519_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_1516_, v_messageHead_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(lean_object* v_dir_1520_, lean_object* v_reader_1521_){
_start:
{
uint8_t v_dir_boxed_1522_; uint8_t v_res_1523_; lean_object* v_r_1524_; 
v_dir_boxed_1522_ = lean_unbox(v_dir_1520_);
v_res_1523_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_1522_, v_reader_1521_);
lean_dec_ref(v_reader_1521_);
v_r_1524_ = lean_box(v_res_1523_);
return v_r_1524_;
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
