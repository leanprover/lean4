// Lean compiler output
// Module: Std.Http.Protocol.H1.Redirect
// Imports: public import Std.Http.Data.Request public import Std.Http.Data.Status public import Std.Http.Data.URI
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
lean_object* lean_string_length(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object*);
lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_host;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_proxyAuthorization;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_lastModified;
extern lean_object* l_Std_Http_Header_Name_contentLocation;
extern lean_object* l_Std_Http_Header_Name_contentLanguage;
extern lean_object* l_Std_Http_Header_Name_contentEncoding;
extern lean_object* l_Std_Http_Header_Name_contentLength;
extern lean_object* l_Std_Http_Header_Name_contentType;
uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_Http_Header_Connection_parse(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_Std_Http_Header_Name_ifModifiedSince;
extern lean_object* l_Std_Http_Header_Name_ifNoneMatch;
lean_object* l_Std_Http_RequestTarget_pathOrRoot(lean_object*);
lean_object* l_Std_Http_URI_Path_normalize(lean_object*);
uint8_t l_Std_Http_URI_Path_isEmpty(lean_object*);
lean_object* l_Std_Http_URI_Path_parent(lean_object*);
lean_object* l_Std_Http_URI_Path_join(lean_object*, lean_object*);
uint8_t l_Std_Http_instBEqMethod_beq(uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
extern lean_object* l_Std_Http_Header_Name_keepAlive;
extern lean_object* l_Std_Http_Header_Name_referer;
extern lean_object* l_Std_Http_Header_Name_cookie;
extern lean_object* l_Std_Http_Header_Name_authorization;
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_location;
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
uint8_t l_Std_Http_instBEqStatus_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_Method_isSafe(uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Std.Http.Protocol.H1.RedirectBodyAction.empty"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Std.Http.Protocol.H1.RedirectBodyAction.replay"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Protocol_H1_instReprRedirectPlan_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "target"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "headers"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__14_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bodyAction"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__17_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__17_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isCrossOrigin"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__20_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__20_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__23 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__23_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__23_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instReprRedirectPlan___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1_value;
static const lean_array_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
static const lean_array_object l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__4;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_decideRedirect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(128) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__1_value;
static const lean_closure_object l_Std_Http_Protocol_H1_decideRedirect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_decideRedirect___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__1_value)} };
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__2_value;
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(lean_object* v_empty_22_){
_start:
{
lean_inc(v_empty_22_);
return v_empty_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg___boxed(lean_object* v_empty_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(v_empty_23_);
lean_dec(v_empty_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_empty_28_){
_start:
{
lean_inc(v_empty_28_);
return v_empty_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_empty_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_empty_32_);
lean_dec(v_empty_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(lean_object* v_replay_35_){
_start:
{
lean_inc(v_replay_35_);
return v_replay_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg___boxed(lean_object* v_replay_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(v_replay_36_);
lean_dec(v_replay_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_replay_41_){
_start:
{
lean_inc(v_replay_41_);
return v_replay_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_replay_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_replay_45_);
lean_dec(v_replay_45_);
return v_res_47_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(lean_object* v_n_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_nat_dec_le(v_n_48_, v___x_49_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat___boxed(lean_object* v_n_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(v_n_53_);
lean_dec(v_n_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(uint8_t v_x_56_, uint8_t v_y_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_58_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_x_56_);
v___x_59_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_y_57_);
v___x_60_ = lean_nat_dec_eq(v___x_58_, v___x_59_);
lean_dec(v___x_59_);
lean_dec(v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction___boxed(lean_object* v_x_61_, lean_object* v_y_62_){
_start:
{
uint8_t v_x_13__boxed_63_; uint8_t v_y_14__boxed_64_; uint8_t v_res_65_; lean_object* v_r_66_; 
v_x_13__boxed_63_ = lean_unbox(v_x_61_);
v_y_14__boxed_64_ = lean_unbox(v_y_62_);
v_res_65_ = l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(v_x_13__boxed_63_, v_y_14__boxed_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(uint8_t v_x_77_, lean_object* v_prec_78_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_87_; 
if (v_x_77_ == 0)
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1024u);
v___x_94_ = lean_nat_dec_le(v___x_93_, v_prec_78_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_80_ = v___x_95_;
goto v___jp_79_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_80_ = v___x_96_;
goto v___jp_79_;
}
}
else
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = lean_nat_dec_le(v___x_97_, v_prec_78_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_87_ = v___x_99_;
goto v___jp_86_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_87_ = v___x_100_;
goto v___jp_86_;
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1));
lean_inc(v___y_80_);
v___x_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_82_, 0, v___y_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = l_Repr_addAppParen(v___x_84_, v_prec_78_);
return v___x_85_;
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_78_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed(lean_object* v_x_101_, lean_object* v_prec_102_){
_start:
{
uint8_t v_x_121__boxed_103_; lean_object* v_res_104_; 
v_x_121__boxed_103_ = lean_unbox(v_x_101_);
v_res_104_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_x_121__boxed_103_, v_prec_102_);
lean_dec(v_prec_102_);
return v_res_104_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default(void){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction(void){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Protocol_H1_instReprRedirectPlan_repr_spec__0(lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_nat_to_int(v_a_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(10u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(11u);
v___x_139_ = lean_nat_to_int(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(14u);
v___x_144_ = lean_nat_to_int(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(17u);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0));
v___x_152_ = lean_string_length(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(lean_object* v_x_159_){
_start:
{
lean_object* v_origin_160_; lean_object* v_target_161_; uint8_t v_method_162_; lean_object* v_headers_163_; uint8_t v_bodyAction_164_; uint8_t v_isCrossOrigin_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_origin_160_ = lean_ctor_get(v_x_159_, 0);
lean_inc_ref(v_origin_160_);
v_target_161_ = lean_ctor_get(v_x_159_, 1);
lean_inc(v_target_161_);
v_method_162_ = lean_ctor_get_uint8(v_x_159_, sizeof(void*)*3);
v_headers_163_ = lean_ctor_get(v_x_159_, 2);
lean_inc_ref(v_headers_163_);
v_bodyAction_164_ = lean_ctor_get_uint8(v_x_159_, sizeof(void*)*3 + 1);
v_isCrossOrigin_165_ = lean_ctor_get_uint8(v_x_159_, sizeof(void*)*3 + 2);
lean_dec_ref(v_x_159_);
v___x_166_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5));
v___x_167_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6));
v___x_168_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_origin_160_);
v___x_171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_168_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = 0;
v___x_173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*1, v___x_172_);
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_167_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9));
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = lean_box(1);
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11));
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_166_);
v___x_182_ = l_Std_Http_instReprRequestTarget_repr(v_target_161_, v___x_169_);
v___x_183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_168_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*1, v___x_172_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_181_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_175_);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_177_);
v___x_188_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13));
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_166_);
v___x_191_ = l_Std_Http_instReprMethod_repr(v_method_162_, v___x_169_);
v___x_192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_168_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_172_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_175_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_177_);
v___x_197_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15));
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_166_);
v___x_200_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16);
v___x_201_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_163_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_172_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_199_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_175_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_177_);
v___x_207_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18));
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_166_);
v___x_210_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19);
v___x_211_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_bodyAction_164_, v___x_169_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_172_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_209_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_175_);
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_177_);
v___x_217_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21));
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_166_);
v___x_220_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22);
v___x_221_ = l_Bool_repr___redArg(v_isCrossOrigin_165_);
v___x_222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v___x_172_);
v___x_224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_219_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25);
v___x_226_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26));
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_224_);
v___x_228_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_225_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_172_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(lean_object* v_x_232_, lean_object* v_prec_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(v_x_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed(lean_object* v_x_235_, lean_object* v_prec_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(v_x_235_, v_prec_236_);
lean_dec(v_prec_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(0u);
return v___x_241_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(1u);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___boxed(lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx(v_x_243_);
lean_dec(v_x_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(lean_object* v_t_245_, lean_object* v_k_246_){
_start:
{
if (lean_obj_tag(v_t_245_) == 0)
{
return v_k_246_;
}
else
{
lean_object* v_plan_247_; lean_object* v___x_248_; 
v_plan_247_ = lean_ctor_get(v_t_245_, 0);
lean_inc_ref(v_plan_247_);
lean_dec_ref_known(v_t_245_, 1);
v___x_248_ = lean_apply_1(v_k_246_, v_plan_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(lean_object* v_motive_249_, lean_object* v_ctorIdx_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_k_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_251_, v_k_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___boxed(lean_object* v_motive_255_, lean_object* v_ctorIdx_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_k_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(v_motive_255_, v_ctorIdx_256_, v_t_257_, v_h_258_, v_k_259_);
lean_dec(v_ctorIdx_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim___redArg(lean_object* v_t_261_, lean_object* v_done_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_261_, v_done_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_done_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_265_, v_done_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim___redArg(lean_object* v_t_269_, lean_object* v_follow_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_269_, v_follow_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim(lean_object* v_motive_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_follow_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_273_, v_follow_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(0);
return v___x_277_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(lean_object* v_current_279_, lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v_uri_281_; lean_object* v_authority_282_; 
lean_dec_ref(v_current_279_);
v_uri_281_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_uri_281_);
lean_dec_ref_known(v_x_280_, 1);
v_authority_282_ = lean_ctor_get(v_uri_281_, 1);
lean_inc(v_authority_282_);
if (lean_obj_tag(v_authority_282_) == 0)
{
lean_object* v___x_283_; 
lean_dec_ref(v_uri_281_);
v___x_283_ = lean_box(0);
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_299_; 
v_val_284_ = lean_ctor_get(v_authority_282_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_authority_282_);
if (v_isSharedCheck_299_ == 0)
{
v___x_286_ = v_authority_282_;
v_isShared_287_ = v_isSharedCheck_299_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_val_284_);
lean_dec(v_authority_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_299_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_scheme_288_; lean_object* v_host_289_; lean_object* v_port_290_; uint16_t v___y_292_; 
v_scheme_288_ = lean_ctor_get(v_uri_281_, 0);
lean_inc_ref(v_scheme_288_);
lean_dec_ref(v_uri_281_);
v_host_289_ = lean_ctor_get(v_val_284_, 1);
lean_inc_ref(v_host_289_);
v_port_290_ = lean_ctor_get(v_val_284_, 2);
lean_inc(v_port_290_);
lean_dec(v_val_284_);
if (lean_obj_tag(v_port_290_) == 2)
{
uint16_t v_port_297_; 
v_port_297_ = lean_ctor_get_uint16(v_port_290_, 0);
lean_dec_ref_known(v_port_290_, 0);
v___y_292_ = v_port_297_;
goto v___jp_291_;
}
else
{
uint16_t v___x_298_; 
lean_dec(v_port_290_);
v___x_298_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_288_);
v___y_292_ = v___x_298_;
goto v___jp_291_;
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_293_, 0, v_scheme_288_);
lean_ctor_set(v___x_293_, 1, v_host_289_);
lean_ctor_set_uint16(v___x_293_, sizeof(void*)*2, v___y_292_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_293_);
v___x_295_ = v___x_286_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
else
{
lean_object* v_ref_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_332_; 
v_ref_300_ = lean_ctor_get(v_x_280_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_332_ == 0)
{
v___x_302_ = v_x_280_;
v_isShared_303_ = v_isSharedCheck_332_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_ref_300_);
lean_dec(v_x_280_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_332_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_authority_304_; 
v_authority_304_ = lean_ctor_get(v_ref_300_, 0);
lean_inc(v_authority_304_);
lean_dec_ref(v_ref_300_);
if (lean_obj_tag(v_authority_304_) == 1)
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_328_; 
lean_del_object(v___x_302_);
v_val_305_ = lean_ctor_get(v_authority_304_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_authority_304_);
if (v_isSharedCheck_328_ == 0)
{
v___x_307_ = v_authority_304_;
v_isShared_308_ = v_isSharedCheck_328_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v_authority_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_328_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_host_309_; lean_object* v_port_310_; uint16_t v___y_312_; 
v_host_309_ = lean_ctor_get(v_val_305_, 1);
lean_inc_ref(v_host_309_);
v_port_310_ = lean_ctor_get(v_val_305_, 2);
lean_inc(v_port_310_);
lean_dec(v_val_305_);
if (lean_obj_tag(v_port_310_) == 2)
{
uint16_t v_port_325_; 
v_port_325_ = lean_ctor_get_uint16(v_port_310_, 0);
lean_dec_ref_known(v_port_310_, 0);
v___y_312_ = v_port_325_;
goto v___jp_311_;
}
else
{
lean_object* v_scheme_326_; uint16_t v___x_327_; 
lean_dec(v_port_310_);
v_scheme_326_ = lean_ctor_get(v_current_279_, 0);
v___x_327_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_326_);
v___y_312_ = v___x_327_;
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v_scheme_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_323_; 
v_scheme_313_ = lean_ctor_get(v_current_279_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_current_279_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v_current_279_, 1);
lean_dec(v_unused_324_);
v___x_315_ = v_current_279_;
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_scheme_313_);
lean_dec(v_current_279_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v_host_309_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_scheme_313_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_host_309_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
lean_ctor_set_uint16(v___x_318_, sizeof(void*)*2, v___y_312_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_318_);
v___x_320_ = v___x_307_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
else
{
lean_object* v___x_330_; 
lean_dec(v_authority_304_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v_current_279_);
v___x_330_ = v___x_302_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_current_279_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t v_originalMethod_333_, uint8_t v_responseVersion_334_, lean_object* v_x_335_){
_start:
{
uint8_t v___y_337_; 
switch(lean_obj_tag(v_x_335_))
{
case 17:
{
uint8_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 9;
v___x_345_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_333_, v___x_344_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 8;
return v___x_346_;
}
else
{
return v___x_344_;
}
}
case 15:
{
goto v___jp_339_;
}
case 16:
{
goto v___jp_339_;
}
default: 
{
return v_originalMethod_333_;
}
}
v___jp_336_:
{
if (v___y_337_ == 0)
{
return v_originalMethod_333_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 8;
return v___x_338_;
}
}
v___jp_339_:
{
uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 23;
v___x_341_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_333_, v___x_340_);
if (v___x_341_ == 0)
{
v___y_337_ = v___x_341_;
goto v___jp_336_;
}
else
{
uint8_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 0;
v___x_343_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_334_, v___x_342_);
if (v___x_343_ == 0)
{
v___y_337_ = v___x_341_;
goto v___jp_336_;
}
else
{
return v_originalMethod_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_347_, lean_object* v_responseVersion_348_, lean_object* v_x_349_){
_start:
{
uint8_t v_originalMethod_boxed_350_; uint8_t v_responseVersion_boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_originalMethod_boxed_350_ = lean_unbox(v_originalMethod_347_);
v_responseVersion_boxed_351_ = lean_unbox(v_responseVersion_348_);
v_res_352_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_350_, v_responseVersion_boxed_351_, v_x_349_);
lean_dec(v_x_349_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_354_ = l_Std_Http_Header_Name_transferEncoding;
v___x_355_ = l_Std_Http_Header_Name_keepAlive;
v___x_356_ = l_Std_Http_Header_Name_connection;
v___x_357_ = lean_unsigned_to_nat(3u);
v___x_358_ = lean_mk_empty_array_with_capacity(v___x_357_);
v___x_359_ = lean_array_push(v___x_358_, v___x_356_);
v___x_360_ = lean_array_push(v___x_359_, v___x_355_);
v___x_361_ = lean_array_push(v___x_360_, v___x_354_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object* v___x_363_, lean_object* v_val_364_, size_t v_sz_365_, size_t v_i_366_, lean_object* v_bs_367_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = lean_usize_dec_lt(v_i_366_, v_sz_365_);
if (v___x_368_ == 0)
{
return v_bs_367_;
}
else
{
lean_object* v_entries_369_; lean_object* v___x_370_; lean_object* v_bs_x27_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_snd_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v_entries_369_ = lean_ctor_get(v___x_363_, 0);
v___x_370_ = lean_unsigned_to_nat(0u);
v_bs_x27_371_ = lean_array_uset(v_bs_367_, v_i_366_, v___x_370_);
v___x_372_ = lean_usize_to_nat(v_i_366_);
v___x_373_ = lean_array_fget_borrowed(v_val_364_, v___x_372_);
lean_dec(v___x_372_);
v___x_374_ = lean_array_fget_borrowed(v_entries_369_, v___x_373_);
v_snd_375_ = lean_ctor_get(v___x_374_, 1);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_366_, v___x_376_);
lean_inc(v_snd_375_);
v___x_378_ = lean_array_uset(v_bs_x27_371_, v_i_366_, v_snd_375_);
v_i_366_ = v___x_377_;
v_bs_367_ = v___x_378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object* v___x_380_, lean_object* v_val_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_bs_384_){
_start:
{
size_t v_sz_boxed_385_; size_t v_i_boxed_386_; lean_object* v_res_387_; 
v_sz_boxed_385_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_386_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v___x_380_, v_val_381_, v_sz_boxed_385_, v_i_boxed_386_, v_bs_384_);
lean_dec_ref(v_val_381_);
lean_dec_ref(v___x_380_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_388_, size_t v_i_389_, size_t v_stop_390_, lean_object* v_b_391_){
_start:
{
lean_object* v___y_393_; uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_eq(v_i_389_, v_stop_390_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_array_uget_borrowed(v_as_388_, v_i_389_);
lean_inc(v___x_398_);
v___x_399_ = l_Std_Http_Header_Name_ofString_x3f(v___x_398_);
if (lean_obj_tag(v___x_399_) == 0)
{
v___y_393_ = v_b_391_;
goto v___jp_392_;
}
else
{
lean_object* v_val_400_; lean_object* v___x_401_; 
v_val_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v___x_399_, 1);
v___x_401_ = lean_array_push(v_b_391_, v_val_400_);
v___y_393_ = v___x_401_;
goto v___jp_392_;
}
}
else
{
return v_b_391_;
}
v___jp_392_:
{
size_t v___x_394_; size_t v___x_395_; 
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_add(v_i_389_, v___x_394_);
v_i_389_ = v___x_395_;
v_b_391_ = v___y_393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_, lean_object* v_b_405_){
_start:
{
size_t v_i_boxed_406_; size_t v_stop_boxed_407_; lean_object* v_res_408_; 
v_i_boxed_406_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_407_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_402_, v_i_boxed_406_, v_stop_boxed_407_, v_b_405_);
lean_dec_ref(v_as_402_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object* v_as_409_, size_t v_i_410_, size_t v_stop_411_, lean_object* v_b_412_){
_start:
{
lean_object* v___y_414_; uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_eq(v_i_410_, v_stop_411_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_array_uget_borrowed(v_as_409_, v_i_410_);
lean_inc(v___x_419_);
v___x_420_ = l_Std_Http_Header_Connection_parse(v___x_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
v___y_414_ = v_b_412_;
goto v___jp_413_;
}
else
{
lean_object* v_val_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v_val_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_array_get_size(v_val_421_);
v___x_424_ = lean_nat_dec_lt(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_dec(v_val_421_);
v___y_414_ = v_b_412_;
goto v___jp_413_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = lean_nat_dec_le(v___x_423_, v___x_423_);
if (v___x_425_ == 0)
{
if (v___x_424_ == 0)
{
lean_dec(v_val_421_);
v___y_414_ = v_b_412_;
goto v___jp_413_;
}
else
{
size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((size_t)0ULL);
v___x_427_ = lean_usize_of_nat(v___x_423_);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_421_, v___x_426_, v___x_427_, v_b_412_);
lean_dec(v_val_421_);
v___y_414_ = v___x_428_;
goto v___jp_413_;
}
}
else
{
size_t v___x_429_; size_t v___x_430_; lean_object* v___x_431_; 
v___x_429_ = ((size_t)0ULL);
v___x_430_ = lean_usize_of_nat(v___x_423_);
v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_421_, v___x_429_, v___x_430_, v_b_412_);
lean_dec(v_val_421_);
v___y_414_ = v___x_431_;
goto v___jp_413_;
}
}
}
}
else
{
return v_b_412_;
}
v___jp_413_:
{
size_t v___x_415_; size_t v___x_416_; 
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_add(v_i_410_, v___x_415_);
v_i_410_ = v___x_416_;
v_b_412_ = v___y_414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object* v_as_432_, lean_object* v_i_433_, lean_object* v_stop_434_, lean_object* v_b_435_){
_start:
{
size_t v_i_boxed_436_; size_t v_stop_boxed_437_; lean_object* v_res_438_; 
v_i_boxed_436_ = lean_unbox_usize(v_i_433_);
lean_dec(v_i_433_);
v_stop_boxed_437_ = lean_unbox_usize(v_stop_434_);
lean_dec(v_stop_434_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v_as_432_, v_i_boxed_436_, v_stop_boxed_437_, v_b_435_);
lean_dec_ref(v_as_432_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_m_439_, lean_object* v_query_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_zero_444_; uint8_t v_isZero_445_; 
v_zero_444_ = lean_unsigned_to_nat(0u);
v_isZero_445_ = lean_nat_dec_eq(v_x_442_, v_zero_444_);
if (v_isZero_445_ == 1)
{
lean_dec(v_x_443_);
lean_dec(v_x_442_);
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_box(2);
return v___x_446_;
}
else
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_val_447_ = lean_ctor_get(v_x_441_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v_x_441_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v_x_441_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_val_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_keyArray_455_; lean_object* v_valueArray_456_; lean_object* v___x_457_; uint8_t v_isSome_458_; 
v_keyArray_455_ = lean_ctor_get(v_m_439_, 1);
v_valueArray_456_ = lean_ctor_get(v_m_439_, 2);
v___x_457_ = lean_array_fget_borrowed(v_keyArray_455_, v_x_443_);
v_isSome_458_ = lean_noption_is_some(v___x_457_);
if (v_isSome_458_ == 0)
{
lean_dec(v_x_442_);
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_x_443_);
return v___x_459_;
}
else
{
lean_object* v_val_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_x_443_);
v_val_460_ = lean_ctor_get(v_x_441_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v_x_441_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_val_460_);
lean_dec(v_x_441_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_val_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_one_468_; lean_object* v_n_469_; lean_object* v___y_471_; 
v_one_468_ = lean_unsigned_to_nat(1u);
v_n_469_ = lean_nat_sub(v_x_442_, v_one_468_);
lean_dec(v_x_442_);
if (v_isSome_458_ == 0)
{
goto v___jp_477_;
}
else
{
lean_object* v___x_479_; uint8_t v_isSome_480_; 
v___x_479_ = lean_array_fget_borrowed(v_valueArray_456_, v_x_443_);
v_isSome_480_ = lean_noption_is_some(v___x_479_);
if (v_isSome_480_ == 0)
{
goto v___jp_477_;
}
else
{
lean_object* v_val_481_; uint8_t v___x_482_; 
lean_inc(v___x_457_);
v_val_481_ = lean_noption_get(v___x_457_);
v___x_482_ = lean_string_dec_eq(v_val_481_, v_query_440_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
lean_dec(v_val_481_);
v___x_483_ = lean_array_get_size(v_keyArray_455_);
v___x_484_ = lean_nat_add(v_x_443_, v_one_468_);
lean_dec(v_x_443_);
v___x_485_ = lean_nat_dec_lt(v___x_484_, v___x_483_);
if (v___x_485_ == 0)
{
lean_dec(v___x_484_);
v_x_442_ = v_n_469_;
v_x_443_ = v_zero_444_;
goto _start;
}
else
{
v_x_442_ = v_n_469_;
v_x_443_ = v___x_484_;
goto _start;
}
}
else
{
lean_object* v_val_488_; lean_object* v___x_489_; 
lean_dec(v_n_469_);
lean_dec(v_x_441_);
lean_inc(v___x_479_);
v_val_488_ = lean_noption_get(v___x_479_);
v___x_489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_489_, 0, v_x_443_);
lean_ctor_set(v___x_489_, 1, v_val_481_);
lean_ctor_set(v___x_489_, 2, v_val_488_);
return v___x_489_;
}
}
}
v___jp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = lean_array_get_size(v_keyArray_455_);
v___x_473_ = lean_nat_add(v_x_443_, v_one_468_);
lean_dec(v_x_443_);
v___x_474_ = lean_nat_dec_lt(v___x_473_, v___x_472_);
if (v___x_474_ == 0)
{
lean_dec(v___x_473_);
v_x_441_ = v___y_471_;
v_x_442_ = v_n_469_;
v_x_443_ = v_zero_444_;
goto _start;
}
else
{
v_x_441_ = v___y_471_;
v_x_442_ = v_n_469_;
v_x_443_ = v___x_473_;
goto _start;
}
}
v___jp_477_:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v___x_478_; 
lean_inc(v_x_443_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_x_443_);
v___y_471_ = v___x_478_;
goto v___jp_470_;
}
else
{
v___y_471_ = v_x_441_;
goto v___jp_470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_m_490_, lean_object* v_query_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___redArg(v_m_490_, v_query_491_, v_x_492_, v_x_493_, v_x_494_);
lean_dec_ref(v_query_491_);
lean_dec_ref(v_m_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(lean_object* v_m_496_, lean_object* v_query_497_){
_start:
{
lean_object* v_keyArray_498_; lean_object* v___x_499_; uint64_t v___x_500_; uint64_t v___x_501_; uint64_t v___x_502_; uint64_t v_fold_503_; uint64_t v___x_504_; uint64_t v___x_505_; uint64_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; size_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_keyArray_498_ = lean_ctor_get(v_m_496_, 1);
v___x_499_ = lean_array_get_size(v_keyArray_498_);
v___x_500_ = lean_string_hash(v_query_497_);
v___x_501_ = 32ULL;
v___x_502_ = lean_uint64_shift_right(v___x_500_, v___x_501_);
v_fold_503_ = lean_uint64_xor(v___x_500_, v___x_502_);
v___x_504_ = 16ULL;
v___x_505_ = lean_uint64_shift_right(v_fold_503_, v___x_504_);
v___x_506_ = lean_uint64_xor(v_fold_503_, v___x_505_);
v___x_507_ = lean_uint64_to_usize(v___x_506_);
v___x_508_ = lean_usize_of_nat(v___x_499_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_sub(v___x_508_, v___x_509_);
v___x_511_ = lean_usize_land(v___x_507_, v___x_510_);
v___x_512_ = lean_usize_to_nat(v___x_511_);
v___x_513_ = lean_box(0);
v___x_514_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___redArg(v_m_496_, v_query_497_, v___x_513_, v___x_499_, v___x_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_515_, lean_object* v_query_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(v_m_515_, v_query_516_);
lean_dec_ref(v_query_516_);
lean_dec_ref(v_m_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object* v_m_518_, lean_object* v_query_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(v_m_518_, v_query_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_index_521_; lean_object* v_key_522_; lean_object* v_value_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_index_521_ = lean_ctor_get(v___x_520_, 0);
v_key_522_ = lean_ctor_get(v___x_520_, 1);
v_value_523_ = lean_ctor_get(v___x_520_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_520_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_value_523_);
lean_inc(v_key_522_);
lean_inc(v_index_521_);
lean_dec(v___x_520_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_index_521_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_key_522_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_value_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
lean_object* v___x_531_; 
lean_dec(v___x_520_);
v___x_531_ = lean_box(1);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object* v_m_532_, lean_object* v_query_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_m_532_, v_query_533_);
lean_dec_ref(v_query_533_);
lean_dec_ref(v_m_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object* v_m_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_m_535_, v_a_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_value_538_; lean_object* v___x_539_; 
v_value_538_ = lean_ctor_get(v___x_537_, 2);
lean_inc(v_value_538_);
lean_dec_ref_known(v___x_537_, 3);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v_value_538_);
return v___x_539_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = lean_box(0);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object* v_m_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_541_, v_a_542_);
lean_dec_ref(v_a_542_);
lean_dec_ref(v_m_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___f_550_; lean_object* v___f_551_; uint8_t v___x_552_; 
v___x_549_ = l_Std_Http_Header_Name_connection;
v___f_550_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_551_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_552_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_550_, v___f_551_, v___x_549_, v_headers_548_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
v___x_553_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2));
return v___x_553_;
}
else
{
lean_object* v_indexes_554_; lean_object* v___x_555_; lean_object* v_val_556_; size_t v_sz_557_; size_t v___x_558_; lean_object* v_entries_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_indexes_554_ = lean_ctor_get(v_headers_548_, 1);
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_554_, v___x_549_);
v_val_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc_n(v_val_556_, 2);
lean_dec(v___x_555_);
v_sz_557_ = lean_array_size(v_val_556_);
v___x_558_ = ((size_t)0ULL);
v_entries_559_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_headers_548_, v_val_556_, v_sz_557_, v___x_558_, v_val_556_);
lean_dec(v_val_556_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2));
v___x_562_ = lean_array_get_size(v_entries_559_);
v___x_563_ = lean_nat_dec_lt(v___x_560_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec_ref(v_entries_559_);
return v___x_561_;
}
else
{
uint8_t v___x_564_; 
v___x_564_ = lean_nat_dec_le(v___x_562_, v___x_562_);
if (v___x_564_ == 0)
{
if (v___x_563_ == 0)
{
lean_dec_ref(v_entries_559_);
return v___x_561_;
}
else
{
size_t v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_usize_of_nat(v___x_562_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v_entries_559_, v___x_558_, v___x_565_, v___x_561_);
lean_dec_ref(v_entries_559_);
return v___x_566_;
}
}
else
{
size_t v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_usize_of_nat(v___x_562_);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v_entries_559_, v___x_558_, v___x_567_, v___x_561_);
lean_dec_ref(v_entries_559_);
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_569_);
lean_dec_ref(v_headers_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_00_u03b2_571_, lean_object* v_m_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_572_, v_a_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_00_u03b2_575_, lean_object* v_m_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_00_u03b2_575_, v_m_576_, v_a_577_);
lean_dec_ref(v_a_577_);
lean_dec_ref(v_m_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v___x_579_, lean_object* v_val_580_, lean_object* v_as_581_, size_t v_sz_582_, size_t v_i_583_, lean_object* v_bs_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v___x_579_, v_val_580_, v_sz_582_, v_i_583_, v_bs_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v___x_586_, lean_object* v_val_587_, lean_object* v_as_588_, lean_object* v_sz_589_, lean_object* v_i_590_, lean_object* v_bs_591_){
_start:
{
size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_sz_boxed_592_ = lean_unbox_usize(v_sz_589_);
lean_dec(v_sz_589_);
v_i_boxed_593_ = lean_unbox_usize(v_i_590_);
lean_dec(v_i_590_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v___x_586_, v_val_587_, v_as_588_, v_sz_boxed_592_, v_i_boxed_593_, v_bs_591_);
lean_dec_ref(v_as_588_);
lean_dec_ref(v_val_587_);
lean_dec_ref(v___x_586_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object* v_00_u03b2_595_, lean_object* v_m_596_, lean_object* v_query_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_m_596_, v_query_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object* v_00_u03b2_599_, lean_object* v_m_600_, lean_object* v_query_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(v_00_u03b2_599_, v_m_600_, v_query_601_);
lean_dec_ref(v_query_601_);
lean_dec_ref(v_m_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_603_, lean_object* v_m_604_, lean_object* v_query_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(v_m_604_, v_query_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_607_, lean_object* v_m_608_, lean_object* v_query_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2(v_00_u03b2_607_, v_m_608_, v_query_609_);
lean_dec_ref(v_query_609_);
lean_dec_ref(v_m_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_611_, lean_object* v_m_612_, lean_object* v_query_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___redArg(v_m_612_, v_query_613_, v_x_614_, v_x_615_, v_x_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_619_, lean_object* v_m_620_, lean_object* v_query_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_619_, v_m_620_, v_query_621_, v_x_622_, v_x_623_, v_x_624_, v_x_625_);
lean_dec_ref(v_query_621_);
lean_dec_ref(v_m_620_);
return v_res_626_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_mk_empty_array_with_capacity(v___x_628_);
v___x_630_ = lean_array_push(v___x_629_, v___x_627_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_631_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_632_ = l_Std_Http_Header_Name_referer;
v___x_633_ = l_Std_Http_Header_Name_cookie;
v___x_634_ = l_Std_Http_Header_Name_authorization;
v___x_635_ = lean_unsigned_to_nat(3u);
v___x_636_ = lean_mk_empty_array_with_capacity(v___x_635_);
v___x_637_ = lean_array_push(v___x_636_, v___x_634_);
v___x_638_ = lean_array_push(v___x_637_, v___x_633_);
v___x_639_ = lean_array_push(v___x_638_, v___x_632_);
return v___x_639_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_640_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_641_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_642_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_643_ = lean_unsigned_to_nat(2u);
v___x_644_ = lean_mk_empty_array_with_capacity(v___x_643_);
v___x_645_ = lean_array_push(v___x_644_, v___x_642_);
v___x_646_ = lean_array_push(v___x_645_, v___x_641_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_647_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_648_ = l_Std_Http_Header_Name_lastModified;
v___x_649_ = l_Std_Http_Header_Name_contentLocation;
v___x_650_ = l_Std_Http_Header_Name_contentLanguage;
v___x_651_ = l_Std_Http_Header_Name_contentEncoding;
v___x_652_ = l_Std_Http_Header_Name_contentLength;
v___x_653_ = l_Std_Http_Header_Name_contentType;
v___x_654_ = lean_unsigned_to_nat(6u);
v___x_655_ = lean_mk_empty_array_with_capacity(v___x_654_);
v___x_656_ = lean_array_push(v___x_655_, v___x_653_);
v___x_657_ = lean_array_push(v___x_656_, v___x_652_);
v___x_658_ = lean_array_push(v___x_657_, v___x_651_);
v___x_659_ = lean_array_push(v___x_658_, v___x_650_);
v___x_660_ = lean_array_push(v___x_659_, v___x_649_);
v___x_661_ = lean_array_push(v___x_660_, v___x_648_);
return v___x_661_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_662_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1(void){
_start:
{
lean_object* v_cellCount_665_; lean_object* v___x_666_; 
v_cellCount_665_ = lean_unsigned_to_nat(16u);
v___x_666_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2(void){
_start:
{
lean_object* v_cellCount_667_; lean_object* v___x_668_; 
v_cellCount_667_ = lean_unsigned_to_nat(16u);
v___x_668_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2);
v___x_670_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
lean_ctor_set(v___x_672_, 2, v___x_669_);
return v___x_672_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__4(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3);
v___x_674_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0));
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v_00_u03b2_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__4, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__4_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__4);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___redArg(lean_object* v_b_678_, lean_object* v_acc_679_, lean_object* v_i_680_){
_start:
{
lean_object* v___y_682_; lean_object* v_keyArray_690_; lean_object* v_valueArray_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_keyArray_690_ = lean_ctor_get(v_b_678_, 1);
v_valueArray_691_ = lean_ctor_get(v_b_678_, 2);
v___x_692_ = lean_array_get_size(v_keyArray_690_);
v___x_693_ = lean_nat_dec_lt(v_i_680_, v___x_692_);
if (v___x_693_ == 0)
{
lean_dec(v_i_680_);
return v_acc_679_;
}
else
{
lean_object* v___x_694_; uint8_t v_isSome_695_; 
v___x_694_ = lean_array_fget_borrowed(v_keyArray_690_, v_i_680_);
v_isSome_695_ = lean_noption_is_some(v___x_694_);
if (v_isSome_695_ == 0)
{
goto v___jp_686_;
}
else
{
lean_object* v___x_696_; uint8_t v_isSome_697_; 
v___x_696_ = lean_array_fget_borrowed(v_valueArray_691_, v_i_680_);
v_isSome_697_ = lean_noption_is_some(v___x_696_);
if (v_isSome_697_ == 0)
{
goto v___jp_686_;
}
else
{
lean_object* v_val_698_; lean_object* v_val_699_; lean_object* v_i_701_; lean_object* v___x_706_; 
lean_inc(v___x_694_);
v_val_698_ = lean_noption_get(v___x_694_);
lean_inc(v___x_696_);
v_val_699_ = lean_noption_get(v___x_696_);
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(v_acc_679_, v_val_698_);
switch(lean_obj_tag(v___x_706_))
{
case 0:
{
lean_object* v_index_707_; lean_object* v_size_708_; lean_object* v___x_709_; 
v_index_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_index_707_);
lean_dec_ref_known(v___x_706_, 3);
v_size_708_ = lean_ctor_get(v_acc_679_, 0);
lean_inc(v_size_708_);
v___x_709_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_679_, v_size_708_, v_index_707_, v_val_698_, v_val_699_);
lean_dec(v_index_707_);
v___y_682_ = v___x_709_;
goto v___jp_681_;
}
case 1:
{
lean_object* v_index_710_; 
v_index_710_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_index_710_);
lean_dec_ref_known(v___x_706_, 1);
v_i_701_ = v_index_710_;
goto v___jp_700_;
}
default: 
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_679_, v___x_711_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_index_713_; 
v_index_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_index_713_);
lean_dec_ref_known(v___x_712_, 1);
v_i_701_ = v_index_713_;
goto v___jp_700_;
}
else
{
lean_dec(v_val_699_);
lean_dec(v_val_698_);
v___y_682_ = v_acc_679_;
goto v___jp_681_;
}
}
}
v___jp_700_:
{
lean_object* v_size_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_size_702_ = lean_ctor_get(v_acc_679_, 0);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_add(v_size_702_, v___x_703_);
v___x_705_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_679_, v___x_704_, v_i_701_, v_val_698_, v_val_699_);
lean_dec(v_i_701_);
v___y_682_ = v___x_705_;
goto v___jp_681_;
}
}
}
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_add(v_i_680_, v___x_683_);
lean_dec(v_i_680_);
v_acc_679_ = v___y_682_;
v_i_680_ = v___x_684_;
goto _start;
}
v___jp_686_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_add(v_i_680_, v___x_687_);
lean_dec(v_i_680_);
v_i_680_ = v___x_688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_b_714_, lean_object* v_acc_715_, lean_object* v_i_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___redArg(v_b_714_, v_acc_715_, v_i_716_);
lean_dec_ref(v_b_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(lean_object* v_init_718_, lean_object* v_b_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___redArg(v_b_719_, v_init_718_, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg___boxed(lean_object* v_init_722_, lean_object* v_b_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_init_722_, v_b_723_);
lean_dec_ref(v_b_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg(lean_object* v_m_725_){
_start:
{
lean_object* v_keyArray_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_cellCount_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_target_733_; lean_object* v___x_734_; 
v_keyArray_726_ = lean_ctor_get(v_m_725_, 1);
v___x_727_ = lean_array_get_size(v_keyArray_726_);
v___x_728_ = lean_unsigned_to_nat(2u);
v_cellCount_729_ = lean_nat_mul(v___x_727_, v___x_728_);
v___x_730_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_729_);
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_729_);
v___x_732_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_729_);
v_target_733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_733_, 0, v___x_730_);
lean_ctor_set(v_target_733_, 1, v___x_731_);
lean_ctor_set(v_target_733_, 2, v___x_732_);
v___x_734_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_target_733_, v_m_725_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg___boxed(lean_object* v_m_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg(v_m_735_);
lean_dec_ref(v_m_735_);
return v_res_736_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(lean_object* v_a_737_, lean_object* v_as_738_, size_t v_i_739_, size_t v_stop_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = lean_usize_dec_eq(v_i_739_, v_stop_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_array_uget_borrowed(v_as_738_, v_i_739_);
v___x_743_ = lean_string_dec_eq(v_a_737_, v___x_742_);
if (v___x_743_ == 0)
{
size_t v___x_744_; size_t v___x_745_; 
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_add(v_i_739_, v___x_744_);
v_i_739_ = v___x_745_;
goto _start;
}
else
{
return v___x_743_;
}
}
else
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___boxed(lean_object* v_a_748_, lean_object* v_as_749_, lean_object* v_i_750_, lean_object* v_stop_751_){
_start:
{
size_t v_i_boxed_752_; size_t v_stop_boxed_753_; uint8_t v_res_754_; lean_object* v_r_755_; 
v_i_boxed_752_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_stop_boxed_753_ = lean_unbox_usize(v_stop_751_);
lean_dec(v_stop_751_);
v_res_754_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(v_a_748_, v_as_749_, v_i_boxed_752_, v_stop_boxed_753_);
lean_dec_ref(v_as_749_);
lean_dec_ref(v_a_748_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v_as_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = lean_array_get_size(v_as_756_);
v___x_760_ = lean_nat_dec_lt(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
return v___x_760_;
}
else
{
if (v___x_760_ == 0)
{
return v___x_760_;
}
else
{
size_t v___x_761_; size_t v___x_762_; uint8_t v___x_763_; 
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_759_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(v_a_757_, v_as_756_, v___x_761_, v___x_762_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object* v_as_764_, lean_object* v_a_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v_as_764_, v_a_765_);
lean_dec_ref(v_a_765_);
lean_dec_ref(v_as_764_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___lam__0(lean_object* v_i_768_, lean_object* v_x_769_){
_start:
{
if (lean_obj_tag(v_x_769_) == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = lean_mk_empty_array_with_capacity(v___x_770_);
v___x_772_ = lean_array_push(v___x_771_, v_i_768_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
else
{
lean_object* v_val_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_val_774_ = lean_ctor_get(v_x_769_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v_x_769_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v_x_769_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_val_774_);
lean_dec(v_x_769_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_array_push(v_val_774_, v_i_768_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object* v___y_783_, lean_object* v_as_784_, size_t v_i_785_, size_t v_stop_786_, lean_object* v_b_787_){
_start:
{
lean_object* v___y_789_; lean_object* v___y_794_; lean_object* v___y_795_; uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_eq(v_i_785_, v_stop_786_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v_fst_799_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v_i_804_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v_i_825_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___x_892_; 
v___x_798_ = lean_array_uget_borrowed(v_as_784_, v_i_785_);
v_fst_799_ = lean_ctor_get(v___x_798_, 0);
v___x_892_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_783_, v_fst_799_);
if (v___x_892_ == 0)
{
goto v___jp_843_;
}
else
{
if (v___x_797_ == 0)
{
v___y_789_ = v_b_787_;
goto v___jp_788_;
}
else
{
goto v___jp_843_;
}
}
v___jp_800_:
{
lean_object* v_size_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_size_805_ = lean_ctor_get(v___y_802_, 0);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_size_805_, v___x_806_);
lean_inc(v_fst_799_);
v___x_808_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_802_, v___x_807_, v_i_804_, v_fst_799_, v___y_803_);
lean_dec(v_i_804_);
v___y_794_ = v___y_801_;
v___y_795_ = v___x_808_;
goto v___jp_793_;
}
v___jp_809_:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(v___y_812_, v_fst_799_);
switch(lean_obj_tag(v___x_813_))
{
case 0:
{
lean_object* v_index_814_; lean_object* v_size_815_; lean_object* v___x_816_; 
v_index_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_index_814_);
lean_dec_ref_known(v___x_813_, 3);
v_size_815_ = lean_ctor_get(v___y_812_, 0);
lean_inc(v_size_815_);
lean_inc(v_fst_799_);
v___x_816_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_812_, v_size_815_, v_index_814_, v_fst_799_, v___y_811_);
lean_dec(v_index_814_);
v___y_794_ = v___y_810_;
v___y_795_ = v___x_816_;
goto v___jp_793_;
}
case 1:
{
lean_object* v_index_817_; 
v_index_817_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_index_817_);
lean_dec_ref_known(v___x_813_, 1);
v___y_801_ = v___y_810_;
v___y_802_ = v___y_812_;
v___y_803_ = v___y_811_;
v_i_804_ = v_index_817_;
goto v___jp_800_;
}
default: 
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_812_, v___x_818_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_index_820_; 
v_index_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_index_820_);
lean_dec_ref_known(v___x_819_, 1);
v___y_801_ = v___y_810_;
v___y_802_ = v___y_812_;
v___y_803_ = v___y_811_;
v_i_804_ = v_index_820_;
goto v___jp_800_;
}
else
{
lean_dec_ref(v___y_811_);
v___y_794_ = v___y_810_;
v___y_795_ = v___y_812_;
goto v___jp_793_;
}
}
}
}
v___jp_821_:
{
lean_object* v_size_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_size_826_ = lean_ctor_get(v___y_824_, 0);
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_add(v_size_826_, v___x_827_);
lean_inc(v_fst_799_);
v___x_829_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_824_, v___x_828_, v_i_825_, v_fst_799_, v___y_822_);
lean_dec(v_i_825_);
v___y_794_ = v___y_823_;
v___y_795_ = v___x_829_;
goto v___jp_793_;
}
v___jp_830_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg(v___y_833_);
lean_dec_ref(v___y_833_);
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(v___x_834_, v_fst_799_);
switch(lean_obj_tag(v___x_835_))
{
case 0:
{
lean_object* v_index_836_; lean_object* v_size_837_; lean_object* v___x_838_; 
v_index_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_index_836_);
lean_dec_ref_known(v___x_835_, 3);
v_size_837_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_size_837_);
lean_inc(v_fst_799_);
v___x_838_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_834_, v_size_837_, v_index_836_, v_fst_799_, v___y_831_);
lean_dec(v_index_836_);
v___y_794_ = v___y_832_;
v___y_795_ = v___x_838_;
goto v___jp_793_;
}
case 1:
{
lean_object* v_index_839_; 
v_index_839_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_index_839_);
lean_dec_ref_known(v___x_835_, 1);
v___y_822_ = v___y_831_;
v___y_823_ = v___y_832_;
v___y_824_ = v___x_834_;
v_i_825_ = v_index_839_;
goto v___jp_821_;
}
default: 
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_834_, v___x_840_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_index_842_; 
v_index_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_index_842_);
lean_dec_ref_known(v___x_841_, 1);
v___y_822_ = v___y_831_;
v___y_823_ = v___y_832_;
v___y_824_ = v___x_834_;
v_i_825_ = v_index_842_;
goto v___jp_821_;
}
else
{
lean_dec_ref(v___y_831_);
v___y_794_ = v___y_832_;
v___y_795_ = v___x_834_;
goto v___jp_793_;
}
}
}
}
v___jp_843_:
{
lean_object* v_entries_844_; lean_object* v_indexes_845_; lean_object* v_i_846_; lean_object* v_entries_847_; lean_object* v___x_848_; 
v_entries_844_ = lean_ctor_get(v_b_787_, 0);
lean_inc_ref(v_entries_844_);
v_indexes_845_ = lean_ctor_get(v_b_787_, 1);
lean_inc_ref(v_indexes_845_);
lean_dec_ref(v_b_787_);
v_i_846_ = lean_array_get_size(v_entries_844_);
lean_inc(v___x_798_);
v_entries_847_ = lean_array_push(v_entries_844_, v___x_798_);
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_spec__2___redArg(v_indexes_845_, v_fst_799_);
switch(lean_obj_tag(v___x_848_))
{
case 0:
{
lean_object* v_index_849_; lean_object* v_value_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_index_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_index_849_);
v_value_850_ = lean_ctor_get(v___x_848_, 2);
lean_inc(v_value_850_);
lean_dec_ref_known(v___x_848_, 3);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v_value_850_);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___lam__0(v_i_846_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_size_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_size_853_ = lean_ctor_get(v_indexes_845_, 0);
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_nat_sub(v_size_853_, v___x_854_);
v___x_856_ = l_Std_DHashMap_Raw_clearCell___redArg(v_indexes_845_, v___x_855_, v_index_849_);
lean_dec(v_index_849_);
v___y_794_ = v_entries_847_;
v___y_795_ = v___x_856_;
goto v___jp_793_;
}
else
{
lean_object* v_val_857_; lean_object* v_size_858_; lean_object* v___x_859_; 
v_val_857_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_852_, 1);
v_size_858_ = lean_ctor_get(v_indexes_845_, 0);
lean_inc(v_size_858_);
lean_inc(v_fst_799_);
v___x_859_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_845_, v_size_858_, v_index_849_, v_fst_799_, v_val_857_);
lean_dec(v_index_849_);
v___y_794_ = v_entries_847_;
v___y_795_ = v___x_859_;
goto v___jp_793_;
}
}
case 1:
{
lean_object* v_index_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_index_860_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_index_860_);
lean_dec_ref_known(v___x_848_, 1);
v___x_861_ = lean_box(0);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___lam__0(v_i_846_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_dec(v_index_860_);
v___y_794_ = v_entries_847_;
v___y_795_ = v_indexes_845_;
goto v___jp_793_;
}
else
{
lean_object* v_val_863_; lean_object* v_size_864_; lean_object* v_keyArray_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_val_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v___x_862_, 1);
v_size_864_ = lean_ctor_get(v_indexes_845_, 0);
v_keyArray_865_ = lean_ctor_get(v_indexes_845_, 1);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_add(v_size_864_, v___x_866_);
v___x_868_ = lean_array_get_size(v_keyArray_865_);
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_dec(v___x_867_);
lean_dec(v_index_860_);
v___y_831_ = v_val_863_;
v___y_832_ = v_entries_847_;
v___y_833_ = v_indexes_845_;
goto v___jp_830_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_870_ = lean_unsigned_to_nat(4u);
v___x_871_ = lean_nat_mul(v___x_867_, v___x_870_);
v___x_872_ = lean_unsigned_to_nat(3u);
v___x_873_ = lean_nat_mul(v___x_868_, v___x_872_);
v___x_874_ = lean_nat_dec_le(v___x_871_, v___x_873_);
lean_dec(v___x_873_);
lean_dec(v___x_871_);
if (v___x_874_ == 0)
{
lean_dec(v___x_867_);
lean_dec(v_index_860_);
v___y_831_ = v_val_863_;
v___y_832_ = v_entries_847_;
v___y_833_ = v_indexes_845_;
goto v___jp_830_;
}
else
{
lean_object* v___x_875_; 
lean_inc(v_fst_799_);
v___x_875_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_845_, v___x_867_, v_index_860_, v_fst_799_, v_val_863_);
lean_dec(v_index_860_);
v___y_794_ = v_entries_847_;
v___y_795_ = v___x_875_;
goto v___jp_793_;
}
}
}
}
default: 
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_box(0);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___lam__0(v_i_846_, v___x_876_);
if (lean_obj_tag(v___x_877_) == 0)
{
v___y_794_ = v_entries_847_;
v___y_795_ = v_indexes_845_;
goto v___jp_793_;
}
else
{
lean_object* v_val_878_; lean_object* v_size_879_; lean_object* v_keyArray_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_val_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v___x_877_, 1);
v_size_879_ = lean_ctor_get(v_indexes_845_, 0);
v_keyArray_880_ = lean_ctor_get(v_indexes_845_, 1);
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_add(v_size_879_, v___x_881_);
v___x_883_ = lean_array_get_size(v_keyArray_880_);
v___x_884_ = lean_nat_dec_lt(v___x_882_, v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
lean_dec(v___x_882_);
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg(v_indexes_845_);
lean_dec_ref(v_indexes_845_);
v___y_810_ = v_entries_847_;
v___y_811_ = v_val_878_;
v___y_812_ = v___x_885_;
goto v___jp_809_;
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_886_ = lean_unsigned_to_nat(4u);
v___x_887_ = lean_nat_mul(v___x_882_, v___x_886_);
lean_dec(v___x_882_);
v___x_888_ = lean_unsigned_to_nat(3u);
v___x_889_ = lean_nat_mul(v___x_883_, v___x_888_);
v___x_890_ = lean_nat_dec_le(v___x_887_, v___x_889_);
lean_dec(v___x_889_);
lean_dec(v___x_887_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg(v_indexes_845_);
lean_dec_ref(v_indexes_845_);
v___y_810_ = v_entries_847_;
v___y_811_ = v_val_878_;
v___y_812_ = v___x_891_;
goto v___jp_809_;
}
else
{
v___y_810_ = v_entries_847_;
v___y_811_ = v_val_878_;
v___y_812_ = v_indexes_845_;
goto v___jp_809_;
}
}
}
}
}
}
}
else
{
return v_b_787_;
}
v___jp_788_:
{
size_t v___x_790_; size_t v___x_791_; 
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_add(v_i_785_, v___x_790_);
v_i_785_ = v___x_791_;
v_b_787_ = v___y_789_;
goto _start;
}
v___jp_793_:
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___y_794_);
lean_ctor_set(v___x_796_, 1, v___y_795_);
v___y_789_ = v___x_796_;
goto v___jp_788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object* v___y_893_, lean_object* v_as_894_, lean_object* v_i_895_, lean_object* v_stop_896_, lean_object* v_b_897_){
_start:
{
size_t v_i_boxed_898_; size_t v_stop_boxed_899_; lean_object* v_res_900_; 
v_i_boxed_898_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_stop_boxed_899_ = lean_unbox_usize(v_stop_896_);
lean_dec(v_stop_896_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_893_, v_as_894_, v_i_boxed_898_, v_stop_boxed_899_, v_b_897_);
lean_dec_ref(v_as_894_);
lean_dec_ref(v___y_893_);
return v_res_900_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0(void){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_box(0));
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_902_, uint8_t v_isCrossOrigin_903_, uint8_t v_methodChanged_904_){
_start:
{
lean_object* v___y_906_; lean_object* v___y_920_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_afterConnection_927_; 
v___x_925_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_926_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_902_);
v_afterConnection_927_ = l_Array_append___redArg(v___x_925_, v___x_926_);
lean_dec_ref(v___x_926_);
if (v_isCrossOrigin_903_ == 0)
{
v___y_920_ = v_afterConnection_927_;
goto v___jp_919_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_928_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_929_ = l_Array_append___redArg(v_afterConnection_927_, v___x_928_);
v___x_930_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_931_ = l_Array_append___redArg(v___x_929_, v___x_930_);
v___x_932_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_933_ = l_Array_append___redArg(v___x_931_, v___x_932_);
v___y_920_ = v___x_933_;
goto v___jp_919_;
}
v___jp_905_:
{
lean_object* v_entries_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_entries_907_ = lean_ctor_get(v_headers_902_, 0);
v___x_908_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_array_get_size(v_entries_907_);
v___x_911_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v___y_906_);
return v___x_908_;
}
else
{
uint8_t v___x_912_; 
v___x_912_ = lean_nat_dec_le(v___x_910_, v___x_910_);
if (v___x_912_ == 0)
{
if (v___x_911_ == 0)
{
lean_dec_ref(v___y_906_);
return v___x_908_;
}
else
{
size_t v___x_913_; size_t v___x_914_; lean_object* v___x_915_; 
v___x_913_ = ((size_t)0ULL);
v___x_914_ = lean_usize_of_nat(v___x_910_);
v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_906_, v_entries_907_, v___x_913_, v___x_914_, v___x_908_);
lean_dec_ref(v___y_906_);
return v___x_915_;
}
}
else
{
size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; 
v___x_916_ = ((size_t)0ULL);
v___x_917_ = lean_usize_of_nat(v___x_910_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_906_, v_entries_907_, v___x_916_, v___x_917_, v___x_908_);
lean_dec_ref(v___y_906_);
return v___x_918_;
}
}
}
v___jp_919_:
{
if (v_methodChanged_904_ == 0)
{
v___y_906_ = v___y_920_;
goto v___jp_905_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_921_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_922_ = l_Array_append___redArg(v___y_920_, v___x_921_);
v___x_923_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_924_ = l_Array_append___redArg(v___x_922_, v___x_923_);
v___y_906_ = v___x_924_;
goto v___jp_905_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_934_, lean_object* v_isCrossOrigin_935_, lean_object* v_methodChanged_936_){
_start:
{
uint8_t v_isCrossOrigin_boxed_937_; uint8_t v_methodChanged_boxed_938_; lean_object* v_res_939_; 
v_isCrossOrigin_boxed_937_ = lean_unbox(v_isCrossOrigin_935_);
v_methodChanged_boxed_938_ = lean_unbox(v_methodChanged_936_);
v_res_939_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_934_, v_isCrossOrigin_boxed_937_, v_methodChanged_boxed_938_);
lean_dec_ref(v_headers_934_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_00_u03b2_940_, lean_object* v_m_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___redArg(v_m_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object* v_00_u03b2_943_, lean_object* v_m_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_00_u03b2_943_, v_m_944_);
lean_dec_ref(v_m_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_00_u03b2_946_, lean_object* v_init_947_, lean_object* v_b_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_init_947_, v_b_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_00_u03b2_950_, lean_object* v_init_951_, lean_object* v_b_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_00_u03b2_950_, v_init_951_, v_b_952_);
lean_dec_ref(v_b_952_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_954_, lean_object* v_b_955_, lean_object* v_acc_956_, lean_object* v_i_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___redArg(v_b_955_, v_acc_956_, v_i_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_959_, lean_object* v_b_960_, lean_object* v_acc_961_, lean_object* v_i_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_spec__2(v_00_u03b2_959_, v_b_960_, v_acc_961_, v_i_962_);
lean_dec_ref(v_b_960_);
return v_res_963_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(lean_object* v_m_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_m_964_, v_a_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
uint8_t v___x_967_; 
lean_dec_ref_known(v___x_966_, 3);
v___x_967_ = 1;
return v___x_967_;
}
else
{
uint8_t v___x_968_; 
v___x_968_ = 0;
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg___boxed(lean_object* v_m_969_, lean_object* v_a_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_m_969_, v_a_970_);
lean_dec_ref(v_a_970_);
lean_dec_ref(v_m_969_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_973_, lean_object* v_origin_974_){
_start:
{
lean_object* v_entries_975_; lean_object* v_indexes_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_entries_975_ = lean_ctor_get(v_headers_973_, 0);
v_indexes_976_ = lean_ctor_get(v_headers_973_, 1);
v___x_977_ = l_Std_Http_Header_Name_host;
v___x_978_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_indexes_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_dec_ref(v_origin_974_);
return v_headers_973_;
}
else
{
lean_object* v___f_979_; lean_object* v___f_980_; uint8_t v___x_981_; 
v___f_979_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_980_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_981_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_979_, v___f_980_, v___x_977_, v_headers_973_);
if (v___x_981_ == 0)
{
lean_dec_ref(v_origin_974_);
return v_headers_973_;
}
else
{
lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_998_; 
lean_inc_ref(v_indexes_976_);
lean_inc_ref(v_entries_975_);
v_isSharedCheck_998_ = !lean_is_exclusive(v_headers_973_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; lean_object* v_unused_1000_; 
v_unused_999_ = lean_ctor_get(v_headers_973_, 1);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_headers_973_, 0);
lean_dec(v_unused_1000_);
v___x_983_ = v_headers_973_;
v_isShared_984_ = v_isSharedCheck_998_;
goto v_resetjp_982_;
}
else
{
lean_dec(v_headers_973_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_998_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v_val_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_lastIdx_992_; lean_object* v___x_993_; lean_object* v_entries_994_; lean_object* v___x_996_; 
v___x_985_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_976_, v___x_977_);
v_val_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_val_986_);
lean_dec(v___x_985_);
v___x_987_ = l_Std_Http_URI_Origin_hostHeader(v_origin_974_);
v___x_988_ = l_Std_Http_Header_Value_ofString_x21(v___x_987_);
v___x_989_ = lean_array_get_size(v_val_986_);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_sub(v___x_989_, v___x_990_);
v_lastIdx_992_ = lean_array_fget(v_val_986_, v___x_991_);
lean_dec(v___x_991_);
lean_dec(v_val_986_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_977_);
lean_ctor_set(v___x_993_, 1, v___x_988_);
v_entries_994_ = lean_array_fset(v_entries_975_, v_lastIdx_992_, v___x_993_);
lean_dec(v_lastIdx_992_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v_entries_994_);
v___x_996_ = v___x_983_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_entries_994_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_indexes_976_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(lean_object* v_00_u03b2_1001_, lean_object* v_m_1002_, lean_object* v_a_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_m_1002_, v_a_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___boxed(lean_object* v_00_u03b2_1005_, lean_object* v_m_1006_, lean_object* v_a_1007_){
_start:
{
uint8_t v_res_1008_; lean_object* v_r_1009_; 
v_res_1008_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_00_u03b2_1005_, v_m_1006_, v_a_1007_);
lean_dec_ref(v_a_1007_);
lean_dec_ref(v_m_1006_);
v_r_1009_ = lean_box(v_res_1008_);
return v_r_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_1010_){
_start:
{
switch(lean_obj_tag(v_x_1010_))
{
case 0:
{
lean_object* v_query_1011_; 
v_query_1011_ = lean_ctor_get(v_x_1010_, 1);
lean_inc(v_query_1011_);
return v_query_1011_;
}
case 1:
{
lean_object* v_uri_1012_; lean_object* v_query_1013_; 
v_uri_1012_ = lean_ctor_get(v_x_1010_, 0);
v_query_1013_ = lean_ctor_get(v_uri_1012_, 3);
lean_inc(v_query_1013_);
return v_query_1013_;
}
default: 
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_box(0);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_1015_);
lean_dec(v_x_1015_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_1017_, uint8_t v_isCrossOrigin_1018_, lean_object* v_basePath_1019_, lean_object* v_baseQuery_1020_, lean_object* v_currentScheme_1021_){
_start:
{
lean_object* v___y_1023_; lean_object* v___y_1024_; 
if (lean_obj_tag(v_ref_1017_) == 0)
{
lean_object* v_uri_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_currentScheme_1021_);
lean_dec(v_baseQuery_1020_);
lean_dec_ref(v_basePath_1019_);
v_uri_1027_ = lean_ctor_get(v_ref_1017_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_ref_1017_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1029_ = v_ref_1017_;
v_isShared_1030_ = v_isSharedCheck_1069_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_uri_1027_);
lean_dec(v_ref_1017_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1069_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_scheme_1031_; lean_object* v_authority_1032_; lean_object* v_path_1033_; lean_object* v_query_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1067_; 
v_scheme_1031_ = lean_ctor_get(v_uri_1027_, 0);
v_authority_1032_ = lean_ctor_get(v_uri_1027_, 1);
v_path_1033_ = lean_ctor_get(v_uri_1027_, 2);
v_query_1034_ = lean_ctor_get(v_uri_1027_, 3);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_uri_1027_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_uri_1027_, 4);
lean_dec(v_unused_1068_);
v___x_1036_ = v_uri_1027_;
v_isShared_1037_ = v_isSharedCheck_1067_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_query_1034_);
lean_inc(v_path_1033_);
lean_inc(v_authority_1032_);
lean_inc(v_scheme_1031_);
lean_dec(v_uri_1027_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1067_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___y_1039_; 
if (lean_obj_tag(v_authority_1032_) == 0)
{
v___y_1039_ = v_authority_1032_;
goto v___jp_1038_;
}
else
{
lean_object* v_val_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1066_; 
v_val_1048_ = lean_ctor_get(v_authority_1032_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_authority_1032_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1050_ = v_authority_1032_;
v_isShared_1051_ = v_isSharedCheck_1066_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_val_1048_);
lean_dec(v_authority_1032_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1066_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_host_1052_; lean_object* v_port_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1064_; 
v_host_1052_ = lean_ctor_get(v_val_1048_, 1);
v_port_1053_ = lean_ctor_get(v_val_1048_, 2);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_val_1048_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_val_1048_, 0);
lean_dec(v_unused_1065_);
v___x_1055_ = v_val_1048_;
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_port_1053_);
lean_inc(v_host_1052_);
lean_dec(v_val_1048_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_box(0);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_host_1052_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_port_1053_);
v___x_1059_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1059_);
v___x_1061_ = v___x_1050_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
v___y_1039_ = v___x_1061_;
goto v___jp_1038_;
}
}
}
}
}
v___jp_1038_:
{
if (v_isCrossOrigin_1018_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v___y_1039_);
lean_del_object(v___x_1036_);
lean_dec_ref(v_scheme_1031_);
lean_del_object(v___x_1029_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_path_1033_);
lean_ctor_set(v___x_1040_, 1, v_query_1034_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; lean_object* v_stripped_1043_; 
v___x_1041_ = lean_box(0);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1041_);
lean_ctor_set(v___x_1036_, 1, v___y_1039_);
v_stripped_1043_ = v___x_1036_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_scheme_1031_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___y_1039_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_path_1033_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_query_1034_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v___x_1041_);
v_stripped_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 1);
lean_ctor_set(v___x_1029_, 0, v_stripped_1043_);
v___x_1045_ = v___x_1029_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_stripped_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
}
else
{
lean_object* v_ref_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1111_; 
v_ref_1070_ = lean_ctor_get(v_ref_1017_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_ref_1017_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1072_ = v_ref_1017_;
v_isShared_1073_ = v_isSharedCheck_1111_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_ref_1070_);
lean_dec(v_ref_1017_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1111_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_authority_1074_; lean_object* v_path_1075_; lean_object* v_query_1076_; lean_object* v___y_1078_; uint8_t v___y_1079_; 
v_authority_1074_ = lean_ctor_get(v_ref_1070_, 0);
lean_inc(v_authority_1074_);
v_path_1075_ = lean_ctor_get(v_ref_1070_, 1);
lean_inc_ref(v_path_1075_);
v_query_1076_ = lean_ctor_get(v_ref_1070_, 2);
lean_inc(v_query_1076_);
lean_dec_ref(v_ref_1070_);
if (lean_obj_tag(v_authority_1074_) == 0)
{
uint8_t v___x_1080_; lean_object* v___y_1082_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v_currentScheme_1021_);
v___x_1080_ = l_Std_Http_URI_Path_isEmpty(v_path_1075_);
if (v___x_1080_ == 0)
{
uint8_t v_absolute_1083_; 
v_absolute_1083_ = lean_ctor_get_uint8(v_path_1075_, sizeof(void*)*1);
if (v_absolute_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = l_Std_Http_URI_Path_parent(v_basePath_1019_);
v___x_1085_ = l_Std_Http_URI_Path_join(v___x_1084_, v_path_1075_);
lean_dec_ref(v_path_1075_);
v___y_1082_ = v___x_1085_;
goto v___jp_1081_;
}
else
{
lean_dec_ref(v_basePath_1019_);
v___y_1082_ = v_path_1075_;
goto v___jp_1081_;
}
}
else
{
lean_dec_ref(v_path_1075_);
v___y_1082_ = v_basePath_1019_;
goto v___jp_1081_;
}
v___jp_1081_:
{
if (v___x_1080_ == 0)
{
v___y_1078_ = v___y_1082_;
v___y_1079_ = v___x_1080_;
goto v___jp_1077_;
}
else
{
if (lean_obj_tag(v_query_1076_) == 0)
{
v___y_1078_ = v___y_1082_;
v___y_1079_ = v___x_1080_;
goto v___jp_1077_;
}
else
{
lean_dec(v_baseQuery_1020_);
v___y_1023_ = v___y_1082_;
v___y_1024_ = v_query_1076_;
goto v___jp_1022_;
}
}
}
}
else
{
lean_dec(v_baseQuery_1020_);
lean_dec_ref(v_basePath_1019_);
if (v_isCrossOrigin_1018_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec_ref_known(v_authority_1074_, 1);
lean_del_object(v___x_1072_);
lean_dec_ref(v_currentScheme_1021_);
v___x_1086_ = l_Std_Http_URI_Path_normalize(v_path_1075_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_query_1076_);
return v___x_1087_;
}
else
{
lean_object* v_val_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1110_; 
v_val_1088_ = lean_ctor_get(v_authority_1074_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_authority_1074_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1090_ = v_authority_1074_;
v_isShared_1091_ = v_isSharedCheck_1110_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_val_1088_);
lean_dec(v_authority_1074_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1110_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_host_1092_; lean_object* v_port_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1108_; 
v_host_1092_ = lean_ctor_get(v_val_1088_, 1);
v_port_1093_ = lean_ctor_get(v_val_1088_, 2);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_val_1088_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; 
v_unused_1109_ = lean_ctor_get(v_val_1088_, 0);
lean_dec(v_unused_1109_);
v___x_1095_ = v_val_1088_;
v_isShared_1096_ = v_isSharedCheck_1108_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_port_1093_);
lean_inc(v_host_1092_);
lean_dec(v_val_1088_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1108_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v_stripped_1099_; 
v___x_1097_ = lean_box(0);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1097_);
v_stripped_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_host_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_port_1093_);
v_stripped_1099_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_stripped_1099_);
v___x_1101_ = v___x_1090_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_stripped_1099_);
v___x_1101_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v_af_1102_; lean_object* v___x_1104_; 
v_af_1102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_1102_, 0, v_currentScheme_1021_);
lean_ctor_set(v_af_1102_, 1, v___x_1101_);
lean_ctor_set(v_af_1102_, 2, v_path_1075_);
lean_ctor_set(v_af_1102_, 3, v_query_1076_);
lean_ctor_set(v_af_1102_, 4, v___x_1097_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v_af_1102_);
v___x_1104_ = v___x_1072_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_af_1102_);
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
}
v___jp_1077_:
{
if (v___y_1079_ == 0)
{
lean_dec(v_baseQuery_1020_);
v___y_1023_ = v___y_1078_;
v___y_1024_ = v_query_1076_;
goto v___jp_1022_;
}
else
{
lean_dec(v_query_1076_);
v___y_1023_ = v___y_1078_;
v___y_1024_ = v_baseQuery_1020_;
goto v___jp_1022_;
}
}
}
}
v___jp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = l_Std_Http_URI_Path_normalize(v___y_1023_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___y_1024_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_1112_, lean_object* v_isCrossOrigin_1113_, lean_object* v_basePath_1114_, lean_object* v_baseQuery_1115_, lean_object* v_currentScheme_1116_){
_start:
{
uint8_t v_isCrossOrigin_boxed_1117_; lean_object* v_res_1118_; 
v_isCrossOrigin_boxed_1117_ = lean_unbox(v_isCrossOrigin_1113_);
v_res_1118_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_1112_, v_isCrossOrigin_boxed_1117_, v_basePath_1114_, v_baseQuery_1115_, v_currentScheme_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Std_Http_URI_Parser_parseURIReference(v___x_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_pos_1125_; lean_object* v_array_1126_; lean_object* v_idx_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_pos_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_pos_1125_);
v_array_1126_ = lean_ctor_get(v_pos_1125_, 0);
v_idx_1127_ = lean_ctor_get(v_pos_1125_, 1);
v___x_1128_ = lean_byte_array_size(v_array_1126_);
v___x_1129_ = lean_nat_dec_lt(v_idx_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_dec(v_pos_1125_);
return v___x_1124_;
}
else
{
lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; 
v_unused_1138_ = lean_ctor_get(v___x_1124_, 1);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v___x_1124_, 0);
lean_dec(v_unused_1139_);
v___x_1131_ = v___x_1124_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_dec(v___x_1124_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 1);
lean_ctor_set(v___x_1131_, 1, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_pos_1125_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1133_);
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
else
{
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_1152_, lean_object* v_request_1153_, uint8_t v_bodyReplayable_1154_, uint8_t v_onlySafeRedirects_1155_, uint8_t v_responseVersion_1156_, lean_object* v_status_1157_, lean_object* v_responseHeaders_1158_){
_start:
{
uint8_t v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v___y_1166_; uint8_t v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; uint8_t v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; uint8_t v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; uint8_t v___y_1185_; uint8_t v___y_1186_; uint8_t v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; uint8_t v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; uint8_t v___y_1198_; uint8_t v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; uint8_t v___y_1205_; uint8_t v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; uint8_t v___y_1209_; uint8_t v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1217_; uint8_t v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1221_; uint8_t v___y_1222_; uint8_t v___y_1223_; uint8_t v___y_1224_; lean_object* v___y_1225_; uint8_t v___y_1228_; uint8_t v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; uint8_t v___y_1234_; uint8_t v___y_1235_; lean_object* v___y_1236_; uint8_t v___y_1238_; uint8_t v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; uint8_t v___y_1243_; uint8_t v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; uint8_t v___y_1254_; uint8_t v___y_1255_; uint8_t v___y_1256_; uint8_t v___y_1257_; uint8_t v___y_1258_; lean_object* v___y_1259_; uint8_t v___y_1262_; lean_object* v___y_1263_; uint8_t v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; uint8_t v___y_1267_; uint8_t v___y_1268_; uint8_t v___y_1269_; lean_object* v___y_1270_; uint8_t v___y_1271_; uint8_t v___y_1272_; lean_object* v___y_1274_; uint8_t v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; uint8_t v___y_1278_; uint8_t v___y_1279_; uint8_t v___y_1280_; uint8_t v___y_1281_; lean_object* v___y_1282_; uint8_t v___y_1285_; lean_object* v___y_1286_; uint8_t v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; uint8_t v___y_1290_; uint8_t v___y_1291_; lean_object* v___y_1292_; uint8_t v___y_1293_; uint8_t v___y_1294_; uint8_t v___y_1296_; uint8_t v___y_1297_; lean_object* v___y_1298_; uint8_t v___y_1299_; lean_object* v___y_1300_; uint8_t v___y_1301_; lean_object* v___y_1302_; uint8_t v___y_1303_; uint8_t v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1306_; uint16_t v___x_1309_; uint16_t v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = 300;
v___x_1310_ = l_Std_Http_Status_toCode(v_status_1157_);
v___x_1311_ = lean_uint16_dec_le(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref(v_current_1152_);
v___x_1312_ = lean_box(0);
return v___x_1312_;
}
else
{
uint16_t v___x_1313_; uint8_t v___x_1314_; uint8_t v___y_1316_; lean_object* v___y_1317_; uint8_t v___y_1318_; lean_object* v___y_1319_; uint8_t v___y_1320_; uint8_t v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; uint8_t v___y_1324_; uint8_t v___y_1330_; lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; uint8_t v___y_1337_; uint8_t v___y_1340_; lean_object* v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; uint8_t v___y_1346_; uint8_t v___y_1349_; lean_object* v___y_1350_; lean_object* v_scheme_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; uint8_t v___y_1361_; uint8_t v___y_1407_; 
v___x_1313_ = 400;
v___x_1314_ = lean_uint16_dec_lt(v___x_1310_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v_current_1152_);
v___x_1411_ = lean_box(0);
return v___x_1411_;
}
else
{
uint8_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = 0;
v___x_1413_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_1156_, v___x_1412_);
if (v___x_1413_ == 0)
{
v___y_1407_ = v___x_1413_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_box(15);
v___x_1415_ = l_Std_Http_instBEqStatus_beq(v_status_1157_, v___x_1414_);
if (v___x_1415_ == 0)
{
v___y_1407_ = v___x_1413_;
goto v___jp_1406_;
}
else
{
goto v___jp_1390_;
}
}
}
v___jp_1315_:
{
uint8_t v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = 8;
v___x_1326_ = l_Std_Http_instBEqMethod_beq(v___y_1318_, v___x_1325_);
if (v___x_1326_ == 0)
{
uint8_t v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = 9;
v___x_1328_ = l_Std_Http_instBEqMethod_beq(v___y_1318_, v___x_1327_);
v___y_1296_ = v___x_1325_;
v___y_1297_ = v___y_1316_;
v___y_1298_ = v___y_1317_;
v___y_1299_ = v___y_1318_;
v___y_1300_ = v___y_1319_;
v___y_1301_ = v___y_1320_;
v___y_1302_ = v___y_1322_;
v___y_1303_ = v___y_1321_;
v___y_1304_ = v___y_1324_;
v___y_1305_ = v___y_1323_;
v___y_1306_ = v___x_1328_;
goto v___jp_1295_;
}
else
{
v___y_1296_ = v___x_1325_;
v___y_1297_ = v___y_1316_;
v___y_1298_ = v___y_1317_;
v___y_1299_ = v___y_1318_;
v___y_1300_ = v___y_1319_;
v___y_1301_ = v___y_1320_;
v___y_1302_ = v___y_1322_;
v___y_1303_ = v___y_1321_;
v___y_1304_ = v___y_1324_;
v___y_1305_ = v___y_1323_;
v___y_1306_ = v___x_1314_;
goto v___jp_1295_;
}
}
v___jp_1329_:
{
uint8_t v___x_1338_; 
v___x_1338_ = l_Std_Http_instBEqMethod_beq(v___y_1330_, v___y_1332_);
if (v___x_1338_ == 0)
{
v___y_1316_ = v___y_1330_;
v___y_1317_ = v___y_1331_;
v___y_1318_ = v___y_1332_;
v___y_1319_ = v___y_1333_;
v___y_1320_ = v___y_1334_;
v___y_1321_ = v___y_1337_;
v___y_1322_ = v___y_1335_;
v___y_1323_ = v___y_1336_;
v___y_1324_ = v___x_1314_;
goto v___jp_1315_;
}
else
{
v___y_1316_ = v___y_1330_;
v___y_1317_ = v___y_1331_;
v___y_1318_ = v___y_1332_;
v___y_1319_ = v___y_1333_;
v___y_1320_ = v___y_1334_;
v___y_1321_ = v___y_1337_;
v___y_1322_ = v___y_1335_;
v___y_1323_ = v___y_1336_;
v___y_1324_ = v___y_1334_;
goto v___jp_1315_;
}
}
v___jp_1339_:
{
uint8_t v___x_1347_; 
v___x_1347_ = l_Std_Http_URI_instBEqOrigin_beq(v___y_1341_, v_current_1152_);
if (v___x_1347_ == 0)
{
v___y_1330_ = v___y_1340_;
v___y_1331_ = v___y_1341_;
v___y_1332_ = v___y_1342_;
v___y_1333_ = v___y_1343_;
v___y_1334_ = v___y_1346_;
v___y_1335_ = v___y_1344_;
v___y_1336_ = v___y_1345_;
v___y_1337_ = v___x_1314_;
goto v___jp_1329_;
}
else
{
v___y_1330_ = v___y_1340_;
v___y_1331_ = v___y_1341_;
v___y_1332_ = v___y_1342_;
v___y_1333_ = v___y_1343_;
v___y_1334_ = v___y_1346_;
v___y_1335_ = v___y_1344_;
v___y_1336_ = v___y_1345_;
v___y_1337_ = v___y_1346_;
goto v___jp_1329_;
}
}
v___jp_1348_:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__0));
v___x_1358_ = lean_string_dec_eq(v_scheme_1351_, v___x_1357_);
lean_dec_ref(v_scheme_1351_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1350_);
lean_dec_ref(v_current_1152_);
v___x_1359_ = lean_box(0);
return v___x_1359_;
}
else
{
v___y_1340_ = v___y_1349_;
v___y_1341_ = v___y_1350_;
v___y_1342_ = v___y_1352_;
v___y_1343_ = v___y_1353_;
v___y_1344_ = v___y_1354_;
v___y_1345_ = v___y_1355_;
v___y_1346_ = v___y_1356_;
goto v___jp_1339_;
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; lean_object* v___f_1363_; lean_object* v___f_1364_; uint8_t v___x_1365_; 
v___x_1362_ = l_Std_Http_Header_Name_location;
v___f_1363_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_1364_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_1365_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1363_, v___f_1364_, v___x_1362_, v_responseHeaders_1158_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref(v_current_1152_);
v___x_1366_ = lean_box(0);
return v___x_1366_;
}
else
{
lean_object* v_entries_1367_; lean_object* v_indexes_1368_; lean_object* v___x_1369_; lean_object* v_val_1370_; lean_object* v___x_1371_; lean_object* v_entry_1372_; lean_object* v___x_1373_; lean_object* v_snd_1374_; lean_object* v___f_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_entries_1367_ = lean_ctor_get(v_responseHeaders_1158_, 0);
v_indexes_1368_ = lean_ctor_get(v_responseHeaders_1158_, 1);
v___x_1369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_1368_, v___x_1362_);
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec(v___x_1369_);
v___x_1371_ = lean_unsigned_to_nat(0u);
v_entry_1372_ = lean_array_fget(v_val_1370_, v___x_1371_);
lean_dec(v_val_1370_);
v___x_1373_ = lean_array_fget_borrowed(v_entries_1367_, v_entry_1372_);
lean_dec(v_entry_1372_);
v_snd_1374_ = lean_ctor_get(v___x_1373_, 1);
v___f_1375_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
v___x_1376_ = lean_string_to_utf8(v_snd_1374_);
v___x_1377_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1375_, v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; 
lean_dec_ref_known(v___x_1377_, 1);
lean_dec_ref(v_current_1152_);
v___x_1378_ = lean_box(0);
return v___x_1378_;
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1380_; 
v_a_1379_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_n(v_a_1379_, 2);
lean_dec_ref_known(v___x_1377_, 1);
lean_inc_ref(v_current_1152_);
v___x_1380_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_1152_, v_a_1379_);
if (lean_obj_tag(v___x_1380_) == 1)
{
lean_object* v_val_1381_; uint8_t v_method_1382_; lean_object* v_uri_1383_; lean_object* v_headers_1384_; lean_object* v_scheme_1385_; uint8_t v_newMethod_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_val_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_method_1382_ = lean_ctor_get_uint8(v_request_1153_, sizeof(void*)*2);
v_uri_1383_ = lean_ctor_get(v_request_1153_, 0);
v_headers_1384_ = lean_ctor_get(v_request_1153_, 1);
v_scheme_1385_ = lean_ctor_get(v_val_1381_, 0);
v_newMethod_1386_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_1382_, v_responseVersion_1156_, v_status_1157_);
v___x_1387_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_1388_ = lean_string_dec_eq(v_scheme_1385_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_inc_ref(v_scheme_1385_);
v___y_1349_ = v_newMethod_1386_;
v___y_1350_ = v_val_1381_;
v_scheme_1351_ = v_scheme_1385_;
v___y_1352_ = v_method_1382_;
v___y_1353_ = v_headers_1384_;
v___y_1354_ = v_uri_1383_;
v___y_1355_ = v_a_1379_;
v___y_1356_ = v___y_1361_;
goto v___jp_1348_;
}
else
{
if (v___y_1361_ == 0)
{
v___y_1340_ = v_newMethod_1386_;
v___y_1341_ = v_val_1381_;
v___y_1342_ = v_method_1382_;
v___y_1343_ = v_headers_1384_;
v___y_1344_ = v_uri_1383_;
v___y_1345_ = v_a_1379_;
v___y_1346_ = v___y_1361_;
goto v___jp_1339_;
}
else
{
lean_inc_ref(v_scheme_1385_);
v___y_1349_ = v_newMethod_1386_;
v___y_1350_ = v_val_1381_;
v_scheme_1351_ = v_scheme_1385_;
v___y_1352_ = v_method_1382_;
v___y_1353_ = v_headers_1384_;
v___y_1354_ = v_uri_1383_;
v___y_1355_ = v_a_1379_;
v___y_1356_ = v___y_1361_;
goto v___jp_1348_;
}
}
}
else
{
lean_object* v___x_1389_; 
lean_dec(v___x_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_current_1152_);
v___x_1389_ = lean_box(0);
return v___x_1389_;
}
}
}
}
v___jp_1390_:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = lean_box(19);
v___x_1392_ = l_Std_Http_instBEqStatus_beq(v_status_1157_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_box(20);
v___x_1394_ = l_Std_Http_instBEqStatus_beq(v_status_1157_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = lean_box(18);
v___x_1396_ = l_Std_Http_instBEqStatus_beq(v_status_1157_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = lean_box(14);
v___x_1398_ = l_Std_Http_instBEqStatus_beq(v_status_1157_, v___x_1397_);
if (v___x_1398_ == 0)
{
if (v_onlySafeRedirects_1155_ == 0)
{
v___y_1361_ = v_onlySafeRedirects_1155_;
goto v___jp_1360_;
}
else
{
uint8_t v_method_1399_; uint8_t v___x_1400_; 
v_method_1399_ = lean_ctor_get_uint8(v_request_1153_, sizeof(void*)*2);
v___x_1400_ = l_Std_Http_Method_isSafe(v_method_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec_ref(v_current_1152_);
v___x_1401_ = lean_box(0);
return v___x_1401_;
}
else
{
v___y_1361_ = v___x_1398_;
goto v___jp_1360_;
}
}
}
else
{
lean_object* v___x_1402_; 
lean_dec_ref(v_current_1152_);
v___x_1402_ = lean_box(0);
return v___x_1402_;
}
}
else
{
lean_object* v___x_1403_; 
lean_dec_ref(v_current_1152_);
v___x_1403_ = lean_box(0);
return v___x_1403_;
}
}
else
{
lean_object* v___x_1404_; 
lean_dec_ref(v_current_1152_);
v___x_1404_ = lean_box(0);
return v___x_1404_;
}
}
else
{
lean_object* v___x_1405_; 
lean_dec_ref(v_current_1152_);
v___x_1405_ = lean_box(0);
return v___x_1405_;
}
}
v___jp_1406_:
{
if (v___y_1407_ == 0)
{
goto v___jp_1390_;
}
else
{
lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = lean_box(16);
v___x_1409_ = l_Std_Http_instBEqStatus_beq(v_status_1157_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_dec_ref(v_current_1152_);
v___x_1410_ = lean_box(0);
return v___x_1410_;
}
else
{
goto v___jp_1390_;
}
}
}
}
v___jp_1159_:
{
lean_object* v_scheme_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_rewrittenTarget_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_scheme_1167_ = lean_ctor_get(v_current_1152_, 0);
lean_inc_ref(v_scheme_1167_);
lean_dec_ref(v_current_1152_);
v___x_1168_ = l_Std_Http_RequestTarget_pathOrRoot(v___y_1164_);
v___x_1169_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v___y_1164_);
v_rewrittenTarget_1170_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v___y_1165_, v___y_1163_, v___x_1168_, v___x_1169_, v_scheme_1167_);
v___x_1171_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1171_, 0, v___y_1161_);
lean_ctor_set(v___x_1171_, 1, v_rewrittenTarget_1170_);
lean_ctor_set(v___x_1171_, 2, v___y_1162_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*3, v___y_1160_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*3 + 1, v___y_1166_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*3 + 2, v___y_1163_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
v___jp_1173_:
{
uint8_t v___x_1180_; 
v___x_1180_ = 0;
v___y_1160_ = v___y_1174_;
v___y_1161_ = v___y_1175_;
v___y_1162_ = v___y_1176_;
v___y_1163_ = v___y_1177_;
v___y_1164_ = v___y_1178_;
v___y_1165_ = v___y_1179_;
v___y_1166_ = v___x_1180_;
goto v___jp_1159_;
}
v___jp_1181_:
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Std_Http_instBEqMethod_beq(v___y_1182_, v___y_1187_);
if (v___x_1190_ == 0)
{
uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 9;
v___x_1192_ = l_Std_Http_instBEqMethod_beq(v___y_1182_, v___x_1191_);
if (v___x_1192_ == 0)
{
if (v___y_1185_ == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = 1;
v___y_1160_ = v___y_1182_;
v___y_1161_ = v___y_1183_;
v___y_1162_ = v___y_1184_;
v___y_1163_ = v___y_1186_;
v___y_1164_ = v___y_1188_;
v___y_1165_ = v___y_1189_;
v___y_1166_ = v___x_1193_;
goto v___jp_1159_;
}
else
{
v___y_1174_ = v___y_1182_;
v___y_1175_ = v___y_1183_;
v___y_1176_ = v___y_1184_;
v___y_1177_ = v___y_1186_;
v___y_1178_ = v___y_1188_;
v___y_1179_ = v___y_1189_;
goto v___jp_1173_;
}
}
else
{
v___y_1174_ = v___y_1182_;
v___y_1175_ = v___y_1183_;
v___y_1176_ = v___y_1184_;
v___y_1177_ = v___y_1186_;
v___y_1178_ = v___y_1188_;
v___y_1179_ = v___y_1189_;
goto v___jp_1173_;
}
}
else
{
v___y_1174_ = v___y_1182_;
v___y_1175_ = v___y_1183_;
v___y_1176_ = v___y_1184_;
v___y_1177_ = v___y_1186_;
v___y_1178_ = v___y_1188_;
v___y_1179_ = v___y_1189_;
goto v___jp_1173_;
}
}
v___jp_1194_:
{
if (v_bodyReplayable_1154_ == 0)
{
lean_object* v___x_1203_; 
lean_dec_ref(v___y_1202_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_current_1152_);
v___x_1203_ = lean_box(0);
return v___x_1203_;
}
else
{
v___y_1182_ = v___y_1195_;
v___y_1183_ = v___y_1196_;
v___y_1184_ = v___y_1197_;
v___y_1185_ = v___y_1198_;
v___y_1186_ = v___y_1199_;
v___y_1187_ = v___y_1200_;
v___y_1188_ = v___y_1201_;
v___y_1189_ = v___y_1202_;
goto v___jp_1181_;
}
}
v___jp_1204_:
{
uint8_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 9;
v___x_1215_ = l_Std_Http_instBEqMethod_beq(v___y_1206_, v___x_1214_);
if (v___x_1215_ == 0)
{
v___y_1195_ = v___y_1206_;
v___y_1196_ = v___y_1207_;
v___y_1197_ = v___y_1208_;
v___y_1198_ = v___y_1209_;
v___y_1199_ = v___y_1210_;
v___y_1200_ = v___y_1211_;
v___y_1201_ = v___y_1212_;
v___y_1202_ = v___y_1213_;
goto v___jp_1194_;
}
else
{
if (v___y_1205_ == 0)
{
v___y_1182_ = v___y_1206_;
v___y_1183_ = v___y_1207_;
v___y_1184_ = v___y_1208_;
v___y_1185_ = v___y_1209_;
v___y_1186_ = v___y_1210_;
v___y_1187_ = v___y_1211_;
v___y_1188_ = v___y_1212_;
v___y_1189_ = v___y_1213_;
goto v___jp_1181_;
}
else
{
v___y_1195_ = v___y_1206_;
v___y_1196_ = v___y_1207_;
v___y_1197_ = v___y_1208_;
v___y_1198_ = v___y_1209_;
v___y_1199_ = v___y_1210_;
v___y_1200_ = v___y_1211_;
v___y_1201_ = v___y_1212_;
v___y_1202_ = v___y_1213_;
goto v___jp_1194_;
}
}
}
v___jp_1216_:
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Std_Http_instBEqMethod_beq(v___y_1218_, v___y_1223_);
if (v___x_1226_ == 0)
{
v___y_1205_ = v___y_1221_;
v___y_1206_ = v___y_1218_;
v___y_1207_ = v___y_1219_;
v___y_1208_ = v___y_1220_;
v___y_1209_ = v___y_1222_;
v___y_1210_ = v___y_1224_;
v___y_1211_ = v___y_1223_;
v___y_1212_ = v___y_1225_;
v___y_1213_ = v___y_1217_;
goto v___jp_1204_;
}
else
{
if (v___y_1221_ == 0)
{
v___y_1182_ = v___y_1218_;
v___y_1183_ = v___y_1219_;
v___y_1184_ = v___y_1220_;
v___y_1185_ = v___y_1222_;
v___y_1186_ = v___y_1224_;
v___y_1187_ = v___y_1223_;
v___y_1188_ = v___y_1225_;
v___y_1189_ = v___y_1217_;
goto v___jp_1181_;
}
else
{
v___y_1205_ = v___y_1221_;
v___y_1206_ = v___y_1218_;
v___y_1207_ = v___y_1219_;
v___y_1208_ = v___y_1220_;
v___y_1209_ = v___y_1222_;
v___y_1210_ = v___y_1224_;
v___y_1211_ = v___y_1223_;
v___y_1212_ = v___y_1225_;
v___y_1213_ = v___y_1217_;
goto v___jp_1204_;
}
}
}
v___jp_1227_:
{
if (v___y_1234_ == 0)
{
v___y_1217_ = v___y_1233_;
v___y_1218_ = v___y_1229_;
v___y_1219_ = v___y_1230_;
v___y_1220_ = v___y_1236_;
v___y_1221_ = v___y_1228_;
v___y_1222_ = v___y_1234_;
v___y_1223_ = v___y_1235_;
v___y_1224_ = v___y_1231_;
v___y_1225_ = v___y_1232_;
goto v___jp_1216_;
}
else
{
if (v___y_1228_ == 0)
{
v___y_1182_ = v___y_1229_;
v___y_1183_ = v___y_1230_;
v___y_1184_ = v___y_1236_;
v___y_1185_ = v___y_1234_;
v___y_1186_ = v___y_1231_;
v___y_1187_ = v___y_1235_;
v___y_1188_ = v___y_1232_;
v___y_1189_ = v___y_1233_;
goto v___jp_1181_;
}
else
{
v___y_1217_ = v___y_1233_;
v___y_1218_ = v___y_1229_;
v___y_1219_ = v___y_1230_;
v___y_1220_ = v___y_1236_;
v___y_1221_ = v___y_1228_;
v___y_1222_ = v___y_1234_;
v___y_1223_ = v___y_1235_;
v___y_1224_ = v___y_1231_;
v___y_1225_ = v___y_1232_;
goto v___jp_1216_;
}
}
}
v___jp_1237_:
{
lean_object* v_scrubbed_1247_; 
v_scrubbed_1247_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v___y_1241_, v___y_1242_, v___y_1243_);
if (v___y_1242_ == 0)
{
v___y_1228_ = v___y_1244_;
v___y_1229_ = v___y_1239_;
v___y_1230_ = v___y_1240_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1245_;
v___y_1233_ = v___y_1246_;
v___y_1234_ = v___y_1243_;
v___y_1235_ = v___y_1238_;
v___y_1236_ = v_scrubbed_1247_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1248_; 
lean_inc_ref(v___y_1240_);
v___x_1248_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_1247_, v___y_1240_);
v___y_1228_ = v___y_1244_;
v___y_1229_ = v___y_1239_;
v___y_1230_ = v___y_1240_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1245_;
v___y_1233_ = v___y_1246_;
v___y_1234_ = v___y_1243_;
v___y_1235_ = v___y_1238_;
v___y_1236_ = v___x_1248_;
goto v___jp_1227_;
}
}
v___jp_1249_:
{
if (v___y_1254_ == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref(v___y_1252_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v_current_1152_);
v___x_1260_ = lean_box(0);
return v___x_1260_;
}
else
{
v___y_1238_ = v___y_1257_;
v___y_1239_ = v___y_1251_;
v___y_1240_ = v___y_1252_;
v___y_1241_ = v___y_1253_;
v___y_1242_ = v___y_1255_;
v___y_1243_ = v___y_1256_;
v___y_1244_ = v___y_1258_;
v___y_1245_ = v___y_1259_;
v___y_1246_ = v___y_1250_;
goto v___jp_1237_;
}
}
v___jp_1261_:
{
if (v___y_1272_ == 0)
{
v___y_1250_ = v___y_1270_;
v___y_1251_ = v___y_1264_;
v___y_1252_ = v___y_1265_;
v___y_1253_ = v___y_1266_;
v___y_1254_ = v___y_1267_;
v___y_1255_ = v___y_1268_;
v___y_1256_ = v___y_1269_;
v___y_1257_ = v___y_1271_;
v___y_1258_ = v___y_1262_;
v___y_1259_ = v___y_1263_;
goto v___jp_1249_;
}
else
{
if (v___y_1262_ == 0)
{
v___y_1238_ = v___y_1271_;
v___y_1239_ = v___y_1264_;
v___y_1240_ = v___y_1265_;
v___y_1241_ = v___y_1266_;
v___y_1242_ = v___y_1268_;
v___y_1243_ = v___y_1269_;
v___y_1244_ = v___y_1262_;
v___y_1245_ = v___y_1263_;
v___y_1246_ = v___y_1270_;
goto v___jp_1237_;
}
else
{
v___y_1250_ = v___y_1270_;
v___y_1251_ = v___y_1264_;
v___y_1252_ = v___y_1265_;
v___y_1253_ = v___y_1266_;
v___y_1254_ = v___y_1267_;
v___y_1255_ = v___y_1268_;
v___y_1256_ = v___y_1269_;
v___y_1257_ = v___y_1271_;
v___y_1258_ = v___y_1262_;
v___y_1259_ = v___y_1263_;
goto v___jp_1249_;
}
}
}
v___jp_1273_:
{
if (v_bodyReplayable_1154_ == 0)
{
lean_object* v___x_1283_; 
lean_dec_ref(v___y_1276_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v_current_1152_);
v___x_1283_ = lean_box(0);
return v___x_1283_;
}
else
{
v___y_1238_ = v___y_1280_;
v___y_1239_ = v___y_1275_;
v___y_1240_ = v___y_1276_;
v___y_1241_ = v___y_1277_;
v___y_1242_ = v___y_1278_;
v___y_1243_ = v___y_1279_;
v___y_1244_ = v___y_1281_;
v___y_1245_ = v___y_1282_;
v___y_1246_ = v___y_1274_;
goto v___jp_1237_;
}
}
v___jp_1284_:
{
if (v___y_1294_ == 0)
{
v___y_1274_ = v___y_1292_;
v___y_1275_ = v___y_1287_;
v___y_1276_ = v___y_1288_;
v___y_1277_ = v___y_1289_;
v___y_1278_ = v___y_1290_;
v___y_1279_ = v___y_1291_;
v___y_1280_ = v___y_1293_;
v___y_1281_ = v___y_1285_;
v___y_1282_ = v___y_1286_;
goto v___jp_1273_;
}
else
{
if (v___y_1285_ == 0)
{
v___y_1238_ = v___y_1293_;
v___y_1239_ = v___y_1287_;
v___y_1240_ = v___y_1288_;
v___y_1241_ = v___y_1289_;
v___y_1242_ = v___y_1290_;
v___y_1243_ = v___y_1291_;
v___y_1244_ = v___y_1285_;
v___y_1245_ = v___y_1286_;
v___y_1246_ = v___y_1292_;
goto v___jp_1237_;
}
else
{
v___y_1274_ = v___y_1292_;
v___y_1275_ = v___y_1287_;
v___y_1276_ = v___y_1288_;
v___y_1277_ = v___y_1289_;
v___y_1278_ = v___y_1290_;
v___y_1279_ = v___y_1291_;
v___y_1280_ = v___y_1293_;
v___y_1281_ = v___y_1285_;
v___y_1282_ = v___y_1286_;
goto v___jp_1273_;
}
}
}
v___jp_1295_:
{
uint8_t v___x_1307_; uint8_t v_isPost_1308_; 
v___x_1307_ = 23;
v_isPost_1308_ = l_Std_Http_instBEqMethod_beq(v___y_1299_, v___x_1307_);
switch(lean_obj_tag(v_status_1157_))
{
case 15:
{
v___y_1262_ = v___y_1301_;
v___y_1263_ = v___y_1302_;
v___y_1264_ = v___y_1297_;
v___y_1265_ = v___y_1298_;
v___y_1266_ = v___y_1300_;
v___y_1267_ = v_isPost_1308_;
v___y_1268_ = v___y_1303_;
v___y_1269_ = v___y_1304_;
v___y_1270_ = v___y_1305_;
v___y_1271_ = v___y_1296_;
v___y_1272_ = v___y_1306_;
goto v___jp_1261_;
}
case 16:
{
v___y_1262_ = v___y_1301_;
v___y_1263_ = v___y_1302_;
v___y_1264_ = v___y_1297_;
v___y_1265_ = v___y_1298_;
v___y_1266_ = v___y_1300_;
v___y_1267_ = v_isPost_1308_;
v___y_1268_ = v___y_1303_;
v___y_1269_ = v___y_1304_;
v___y_1270_ = v___y_1305_;
v___y_1271_ = v___y_1296_;
v___y_1272_ = v___y_1306_;
goto v___jp_1261_;
}
case 21:
{
v___y_1285_ = v___y_1301_;
v___y_1286_ = v___y_1302_;
v___y_1287_ = v___y_1297_;
v___y_1288_ = v___y_1298_;
v___y_1289_ = v___y_1300_;
v___y_1290_ = v___y_1303_;
v___y_1291_ = v___y_1304_;
v___y_1292_ = v___y_1305_;
v___y_1293_ = v___y_1296_;
v___y_1294_ = v___y_1306_;
goto v___jp_1284_;
}
case 22:
{
v___y_1285_ = v___y_1301_;
v___y_1286_ = v___y_1302_;
v___y_1287_ = v___y_1297_;
v___y_1288_ = v___y_1298_;
v___y_1289_ = v___y_1300_;
v___y_1290_ = v___y_1303_;
v___y_1291_ = v___y_1304_;
v___y_1292_ = v___y_1305_;
v___y_1293_ = v___y_1296_;
v___y_1294_ = v___y_1306_;
goto v___jp_1284_;
}
default: 
{
v___y_1238_ = v___y_1296_;
v___y_1239_ = v___y_1297_;
v___y_1240_ = v___y_1298_;
v___y_1241_ = v___y_1300_;
v___y_1242_ = v___y_1303_;
v___y_1243_ = v___y_1304_;
v___y_1244_ = v___y_1301_;
v___y_1245_ = v___y_1302_;
v___y_1246_ = v___y_1305_;
goto v___jp_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_1416_, lean_object* v_request_1417_, lean_object* v_bodyReplayable_1418_, lean_object* v_onlySafeRedirects_1419_, lean_object* v_responseVersion_1420_, lean_object* v_status_1421_, lean_object* v_responseHeaders_1422_){
_start:
{
uint8_t v_bodyReplayable_boxed_1423_; uint8_t v_onlySafeRedirects_boxed_1424_; uint8_t v_responseVersion_boxed_1425_; lean_object* v_res_1426_; 
v_bodyReplayable_boxed_1423_ = lean_unbox(v_bodyReplayable_1418_);
v_onlySafeRedirects_boxed_1424_ = lean_unbox(v_onlySafeRedirects_1419_);
v_responseVersion_boxed_1425_ = lean_unbox(v_responseVersion_1420_);
v_res_1426_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1416_, v_request_1417_, v_bodyReplayable_boxed_1423_, v_onlySafeRedirects_boxed_1424_, v_responseVersion_boxed_1425_, v_status_1421_, v_responseHeaders_1422_);
lean_dec_ref(v_responseHeaders_1422_);
lean_dec(v_status_1421_);
lean_dec_ref(v_request_1417_);
return v_res_1426_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Status(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Redirect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default = _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default();
l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction = _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction();
l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default = _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default();
lean_mark_persistent(l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default);
l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome = _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome();
lean_mark_persistent(l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Redirect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Status(uint8_t builtin);
lean_object* initialize_Std_Http_Data_URI(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Redirect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Redirect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Redirect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Redirect(builtin);
}
#ifdef __cplusplus
}
#endif
