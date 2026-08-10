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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object*);
lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_host;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_proxyAuthorization;
extern lean_object* l_Std_Http_Header_Name_lastModified;
extern lean_object* l_Std_Http_Header_Name_contentLocation;
extern lean_object* l_Std_Http_Header_Name_contentLanguage;
extern lean_object* l_Std_Http_Header_Name_contentEncoding;
extern lean_object* l_Std_Http_Header_Name_contentLength;
extern lean_object* l_Std_Http_Header_Name_contentType;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1_value;
static const lean_array_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object* v___x_363_, lean_object* v___x_364_, size_t v_sz_365_, size_t v_i_366_, lean_object* v_bs_367_){
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
v___x_373_ = lean_array_fget_borrowed(v___x_364_, v___x_372_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object* v___x_380_, lean_object* v___x_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_bs_384_){
_start:
{
size_t v_sz_boxed_385_; size_t v_i_boxed_386_; lean_object* v_res_387_; 
v_sz_boxed_385_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_386_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v___x_380_, v___x_381_, v_sz_boxed_385_, v_i_boxed_386_, v_bs_384_);
lean_dec_ref(v___x_381_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_key_441_; lean_object* v_value_442_; lean_object* v_tail_443_; uint8_t v___x_444_; 
v_key_441_ = lean_ctor_get(v_x_440_, 0);
v_value_442_ = lean_ctor_get(v_x_440_, 1);
v_tail_443_ = lean_ctor_get(v_x_440_, 2);
v___x_444_ = lean_string_dec_eq(v_key_441_, v_a_439_);
if (v___x_444_ == 0)
{
v_x_440_ = v_tail_443_;
goto _start;
}
else
{
lean_inc(v_value_442_);
return v_value_442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object* v_a_446_, lean_object* v_x_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_446_, v_x_447_);
lean_dec(v_x_447_);
lean_dec_ref(v_a_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object* v_m_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_buckets_451_; lean_object* v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v_fold_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; size_t v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_buckets_451_ = lean_ctor_get(v_m_449_, 1);
v___x_452_ = lean_array_get_size(v_buckets_451_);
v___x_453_ = lean_string_hash(v_a_450_);
v___x_454_ = 32ULL;
v___x_455_ = lean_uint64_shift_right(v___x_453_, v___x_454_);
v_fold_456_ = lean_uint64_xor(v___x_453_, v___x_455_);
v___x_457_ = 16ULL;
v___x_458_ = lean_uint64_shift_right(v_fold_456_, v___x_457_);
v___x_459_ = lean_uint64_xor(v_fold_456_, v___x_458_);
v___x_460_ = lean_uint64_to_usize(v___x_459_);
v___x_461_ = lean_usize_of_nat(v___x_452_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_sub(v___x_461_, v___x_462_);
v___x_464_ = lean_usize_land(v___x_460_, v___x_463_);
v___x_465_ = lean_array_uget_borrowed(v_buckets_451_, v___x_464_);
v___x_466_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_450_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object* v_m_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_467_, v_a_468_);
lean_dec_ref(v_a_468_);
lean_dec_ref(v_m_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___f_476_; lean_object* v___f_477_; uint8_t v___x_478_; 
v___x_475_ = l_Std_Http_Header_Name_connection;
v___f_476_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_477_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_478_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_476_, v___f_477_, v___x_475_, v_headers_474_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2));
return v___x_479_;
}
else
{
lean_object* v_indexes_480_; lean_object* v___x_481_; size_t v_sz_482_; size_t v___x_483_; lean_object* v_entries_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_indexes_480_ = lean_ctor_get(v_headers_474_, 1);
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_480_, v___x_475_);
v_sz_482_ = lean_array_size(v___x_481_);
v___x_483_ = ((size_t)0ULL);
lean_inc(v___x_481_);
v_entries_484_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_headers_474_, v___x_481_, v_sz_482_, v___x_483_, v___x_481_);
lean_dec(v___x_481_);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2));
v___x_487_ = lean_array_get_size(v_entries_484_);
v___x_488_ = lean_nat_dec_lt(v___x_485_, v___x_487_);
if (v___x_488_ == 0)
{
lean_dec_ref(v_entries_484_);
return v___x_486_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = lean_nat_dec_le(v___x_487_, v___x_487_);
if (v___x_489_ == 0)
{
if (v___x_488_ == 0)
{
lean_dec_ref(v_entries_484_);
return v___x_486_;
}
else
{
size_t v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_usize_of_nat(v___x_487_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v_entries_484_, v___x_483_, v___x_490_, v___x_486_);
lean_dec_ref(v_entries_484_);
return v___x_491_;
}
}
else
{
size_t v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_usize_of_nat(v___x_487_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v_entries_484_, v___x_483_, v___x_492_, v___x_486_);
lean_dec_ref(v_entries_484_);
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_494_);
lean_dec_ref(v_headers_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_00_u03b2_496_, lean_object* v_m_497_, lean_object* v_a_498_, lean_object* v_hma_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_497_, v_a_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_00_u03b2_501_, lean_object* v_m_502_, lean_object* v_a_503_, lean_object* v_hma_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_00_u03b2_501_, v_m_502_, v_a_503_, v_hma_504_);
lean_dec_ref(v_a_503_);
lean_dec_ref(v_m_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v___x_506_, lean_object* v___x_507_, lean_object* v_as_508_, size_t v_sz_509_, size_t v_i_510_, lean_object* v_bs_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v___x_506_, v___x_507_, v_sz_509_, v_i_510_, v_bs_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v_as_515_, lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_bs_518_){
_start:
{
size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_sz_boxed_519_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v___x_513_, v___x_514_, v_as_515_, v_sz_boxed_519_, v_i_boxed_520_, v_bs_518_);
lean_dec_ref(v_as_515_);
lean_dec_ref(v___x_514_);
lean_dec_ref(v___x_513_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object* v_00_u03b2_522_, lean_object* v_a_523_, lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_523_, v_x_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(v_00_u03b2_527_, v_a_528_, v_x_529_, v_x_530_);
lean_dec(v_x_529_);
lean_dec_ref(v_a_528_);
return v_res_531_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_532_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_mk_empty_array_with_capacity(v___x_533_);
v___x_535_ = lean_array_push(v___x_534_, v___x_532_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_536_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_537_ = l_Std_Http_Header_Name_referer;
v___x_538_ = l_Std_Http_Header_Name_cookie;
v___x_539_ = l_Std_Http_Header_Name_authorization;
v___x_540_ = lean_unsigned_to_nat(3u);
v___x_541_ = lean_mk_empty_array_with_capacity(v___x_540_);
v___x_542_ = lean_array_push(v___x_541_, v___x_539_);
v___x_543_ = lean_array_push(v___x_542_, v___x_538_);
v___x_544_ = lean_array_push(v___x_543_, v___x_537_);
return v___x_544_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_545_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_546_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_547_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_548_ = lean_unsigned_to_nat(2u);
v___x_549_ = lean_mk_empty_array_with_capacity(v___x_548_);
v___x_550_ = lean_array_push(v___x_549_, v___x_547_);
v___x_551_ = lean_array_push(v___x_550_, v___x_546_);
return v___x_551_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_552_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_553_ = l_Std_Http_Header_Name_lastModified;
v___x_554_ = l_Std_Http_Header_Name_contentLocation;
v___x_555_ = l_Std_Http_Header_Name_contentLanguage;
v___x_556_ = l_Std_Http_Header_Name_contentEncoding;
v___x_557_ = l_Std_Http_Header_Name_contentLength;
v___x_558_ = l_Std_Http_Header_Name_contentType;
v___x_559_ = lean_unsigned_to_nat(6u);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_559_);
v___x_561_ = lean_array_push(v___x_560_, v___x_558_);
v___x_562_ = lean_array_push(v___x_561_, v___x_557_);
v___x_563_ = lean_array_push(v___x_562_, v___x_556_);
v___x_564_ = lean_array_push(v___x_563_, v___x_555_);
v___x_565_ = lean_array_push(v___x_564_, v___x_554_);
v___x_566_ = lean_array_push(v___x_565_, v___x_553_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_567_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_box(0);
v___x_571_ = lean_unsigned_to_nat(16u);
v___x_572_ = lean_mk_array(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2);
v___x_577_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0));
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v_00_u03b2_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2___lam__0(lean_object* v_i_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_array_push(v___x_584_, v_i_581_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v_val_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v_val_587_ = lean_ctor_get(v_x_582_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_595_ == 0)
{
v___x_589_ = v_x_582_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_val_587_);
lean_dec(v_x_582_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_array_push(v_val_587_, v_i_581_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2(lean_object* v_i_596_, lean_object* v_a_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_val_601_; lean_object* v___x_602_; 
v___x_599_ = lean_box(0);
v___x_600_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2___lam__0(v_i_596_, v___x_599_);
v_val_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_val_601_);
lean_dec(v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_602_, 0, v_a_597_);
lean_ctor_set(v___x_602_, 1, v_val_601_);
lean_ctor_set(v___x_602_, 2, v_x_598_);
return v___x_602_;
}
else
{
lean_object* v_key_603_; lean_object* v_value_604_; lean_object* v_tail_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_620_; 
v_key_603_ = lean_ctor_get(v_x_598_, 0);
v_value_604_ = lean_ctor_get(v_x_598_, 1);
v_tail_605_ = lean_ctor_get(v_x_598_, 2);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_620_ == 0)
{
v___x_607_ = v_x_598_;
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_tail_605_);
lean_inc(v_value_604_);
lean_inc(v_key_603_);
lean_dec(v_x_598_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = lean_string_dec_eq(v_key_603_, v_a_597_);
if (v___x_609_ == 0)
{
lean_object* v_tail_610_; lean_object* v___x_612_; 
v_tail_610_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2(v_i_596_, v_a_597_, v_tail_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 2, v_tail_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_key_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_value_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_tail_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_val_616_; lean_object* v___x_618_; 
lean_dec(v_key_603_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_value_604_);
v___x_615_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2___lam__0(v_i_596_, v___x_614_);
v_val_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_val_616_);
lean_dec(v___x_615_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_val_616_);
lean_ctor_set(v___x_607_, 0, v_a_597_);
v___x_618_ = v___x_607_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_597_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_val_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_tail_605_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(lean_object* v_a_621_, lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
else
{
lean_object* v_key_624_; lean_object* v_tail_625_; uint8_t v___x_626_; 
v_key_624_ = lean_ctor_get(v_x_622_, 0);
v_tail_625_ = lean_ctor_get(v_x_622_, 2);
v___x_626_ = lean_string_dec_eq(v_key_624_, v_a_621_);
if (v___x_626_ == 0)
{
v_x_622_ = v_tail_625_;
goto _start;
}
else
{
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg___boxed(lean_object* v_a_628_, lean_object* v_x_629_){
_start:
{
uint8_t v_res_630_; lean_object* v_r_631_; 
v_res_630_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_628_, v_x_629_);
lean_dec(v_x_629_);
lean_dec_ref(v_a_628_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
return v_x_632_;
}
else
{
lean_object* v_key_634_; lean_object* v_value_635_; lean_object* v_tail_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_659_; 
v_key_634_ = lean_ctor_get(v_x_633_, 0);
v_value_635_ = lean_ctor_get(v_x_633_, 1);
v_tail_636_ = lean_ctor_get(v_x_633_, 2);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_659_ == 0)
{
v___x_638_ = v_x_633_;
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_tail_636_);
lean_inc(v_value_635_);
lean_inc(v_key_634_);
lean_dec(v_x_633_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; uint64_t v___x_641_; uint64_t v___x_642_; uint64_t v___x_643_; uint64_t v_fold_644_; uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_640_ = lean_array_get_size(v_x_632_);
v___x_641_ = lean_string_hash(v_key_634_);
v___x_642_ = 32ULL;
v___x_643_ = lean_uint64_shift_right(v___x_641_, v___x_642_);
v_fold_644_ = lean_uint64_xor(v___x_641_, v___x_643_);
v___x_645_ = 16ULL;
v___x_646_ = lean_uint64_shift_right(v_fold_644_, v___x_645_);
v___x_647_ = lean_uint64_xor(v_fold_644_, v___x_646_);
v___x_648_ = lean_uint64_to_usize(v___x_647_);
v___x_649_ = lean_usize_of_nat(v___x_640_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_sub(v___x_649_, v___x_650_);
v___x_652_ = lean_usize_land(v___x_648_, v___x_651_);
v___x_653_ = lean_array_uget_borrowed(v_x_632_, v___x_652_);
lean_inc(v___x_653_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 2, v___x_653_);
v___x_655_ = v___x_638_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_key_634_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_value_635_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v___x_653_);
v___x_655_ = v_reuseFailAlloc_658_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_array_uset(v_x_632_, v___x_652_, v___x_655_);
v_x_632_ = v___x_656_;
v_x_633_ = v_tail_636_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3___redArg(lean_object* v_i_660_, lean_object* v_source_661_, lean_object* v_target_662_){
_start:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_array_get_size(v_source_661_);
v___x_664_ = lean_nat_dec_lt(v_i_660_, v___x_663_);
if (v___x_664_ == 0)
{
lean_dec_ref(v_source_661_);
lean_dec(v_i_660_);
return v_target_662_;
}
else
{
lean_object* v_es_665_; lean_object* v___x_666_; lean_object* v_source_667_; lean_object* v_target_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_es_665_ = lean_array_fget(v_source_661_, v_i_660_);
v___x_666_ = lean_box(0);
v_source_667_ = lean_array_fset(v_source_661_, v_i_660_, v___x_666_);
v_target_668_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6___redArg(v_target_662_, v_es_665_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_i_660_, v___x_669_);
lean_dec(v_i_660_);
v_i_660_ = v___x_670_;
v_source_661_ = v_source_667_;
v_target_662_ = v_target_668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1___redArg(lean_object* v_data_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_nbuckets_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_673_ = lean_array_get_size(v_data_672_);
v___x_674_ = lean_unsigned_to_nat(2u);
v_nbuckets_675_ = lean_nat_mul(v___x_673_, v___x_674_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_box(0);
v___x_678_ = lean_mk_array(v_nbuckets_675_, v___x_677_);
v___x_679_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3___redArg(v___x_676_, v_data_672_, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_i_680_, lean_object* v_m_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_size_683_; lean_object* v_buckets_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_734_; 
v_size_683_ = lean_ctor_get(v_m_681_, 0);
v_buckets_684_ = lean_ctor_get(v_m_681_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_m_681_);
if (v_isSharedCheck_734_ == 0)
{
v___x_686_ = v_m_681_;
v_isShared_687_ = v_isSharedCheck_734_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_buckets_684_);
lean_inc(v_size_683_);
lean_dec(v_m_681_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_734_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; uint64_t v___x_689_; uint64_t v___x_690_; uint64_t v___x_691_; uint64_t v_fold_692_; uint64_t v___x_693_; uint64_t v___x_694_; uint64_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; lean_object* v_bkt_701_; uint8_t v___x_702_; 
v___x_688_ = lean_array_get_size(v_buckets_684_);
v___x_689_ = lean_string_hash(v_a_682_);
v___x_690_ = 32ULL;
v___x_691_ = lean_uint64_shift_right(v___x_689_, v___x_690_);
v_fold_692_ = lean_uint64_xor(v___x_689_, v___x_691_);
v___x_693_ = 16ULL;
v___x_694_ = lean_uint64_shift_right(v_fold_692_, v___x_693_);
v___x_695_ = lean_uint64_xor(v_fold_692_, v___x_694_);
v___x_696_ = lean_uint64_to_usize(v___x_695_);
v___x_697_ = lean_usize_of_nat(v___x_688_);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_sub(v___x_697_, v___x_698_);
v___x_700_ = lean_usize_land(v___x_696_, v___x_699_);
v_bkt_701_ = lean_array_uget_borrowed(v_buckets_684_, v___x_700_);
v___x_702_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_682_, v_bkt_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_size_x27_706_; lean_object* v___x_707_; lean_object* v_buckets_x27_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_mk_empty_array_with_capacity(v___x_703_);
v___x_705_ = lean_array_push(v___x_704_, v_i_680_);
v_size_x27_706_ = lean_nat_add(v_size_683_, v___x_703_);
lean_dec(v_size_683_);
lean_inc(v_bkt_701_);
v___x_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_707_, 0, v_a_682_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
lean_ctor_set(v___x_707_, 2, v_bkt_701_);
v_buckets_x27_708_ = lean_array_uset(v_buckets_684_, v___x_700_, v___x_707_);
v___x_709_ = lean_unsigned_to_nat(4u);
v___x_710_ = lean_nat_mul(v_size_x27_706_, v___x_709_);
v___x_711_ = lean_unsigned_to_nat(3u);
v___x_712_ = lean_nat_div(v___x_710_, v___x_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_array_get_size(v_buckets_x27_708_);
v___x_714_ = lean_nat_dec_le(v___x_712_, v___x_713_);
lean_dec(v___x_712_);
if (v___x_714_ == 0)
{
lean_object* v_val_715_; lean_object* v___x_717_; 
v_val_715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1___redArg(v_buckets_x27_708_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_val_715_);
lean_ctor_set(v___x_686_, 0, v_size_x27_706_);
v___x_717_ = v___x_686_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_size_x27_706_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_val_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_object* v___x_720_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_buckets_x27_708_);
lean_ctor_set(v___x_686_, 0, v_size_x27_706_);
v___x_720_ = v___x_686_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_size_x27_706_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_buckets_x27_708_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
lean_object* v___x_722_; lean_object* v_buckets_x27_723_; lean_object* v_bkt_x27_724_; lean_object* v___y_726_; uint8_t v___x_731_; 
lean_inc(v_bkt_701_);
v___x_722_ = lean_box(0);
v_buckets_x27_723_ = lean_array_uset(v_buckets_684_, v___x_700_, v___x_722_);
lean_inc_ref(v_a_682_);
v_bkt_x27_724_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2(v_i_680_, v_a_682_, v_bkt_701_);
v___x_731_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_682_, v_bkt_x27_724_);
lean_dec_ref(v_a_682_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_sub(v_size_683_, v___x_732_);
lean_dec(v_size_683_);
v___y_726_ = v___x_733_;
goto v___jp_725_;
}
else
{
v___y_726_ = v_size_683_;
goto v___jp_725_;
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_array_uset(v_buckets_x27_723_, v___x_700_, v_bkt_x27_724_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_727_);
lean_ctor_set(v___x_686_, 0, v___y_726_);
v___x_729_ = v___x_686_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___y_726_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4(lean_object* v_a_735_, lean_object* v_as_736_, size_t v_i_737_, size_t v_stop_738_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = lean_usize_dec_eq(v_i_737_, v_stop_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_array_uget_borrowed(v_as_736_, v_i_737_);
v___x_741_ = lean_string_dec_eq(v_a_735_, v___x_740_);
if (v___x_741_ == 0)
{
size_t v___x_742_; size_t v___x_743_; 
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_737_, v___x_742_);
v_i_737_ = v___x_743_;
goto _start;
}
else
{
return v___x_741_;
}
}
else
{
uint8_t v___x_745_; 
v___x_745_ = 0;
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4___boxed(lean_object* v_a_746_, lean_object* v_as_747_, lean_object* v_i_748_, lean_object* v_stop_749_){
_start:
{
size_t v_i_boxed_750_; size_t v_stop_boxed_751_; uint8_t v_res_752_; lean_object* v_r_753_; 
v_i_boxed_750_ = lean_unbox_usize(v_i_748_);
lean_dec(v_i_748_);
v_stop_boxed_751_ = lean_unbox_usize(v_stop_749_);
lean_dec(v_stop_749_);
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4(v_a_746_, v_as_747_, v_i_boxed_750_, v_stop_boxed_751_);
lean_dec_ref(v_as_747_);
lean_dec_ref(v_a_746_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v_as_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_array_get_size(v_as_754_);
v___x_758_ = lean_nat_dec_lt(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
return v___x_758_;
}
else
{
if (v___x_758_ == 0)
{
return v___x_758_;
}
else
{
size_t v___x_759_; size_t v___x_760_; uint8_t v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_757_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4(v_a_755_, v_as_754_, v___x_759_, v___x_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object* v_as_762_, lean_object* v_a_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v_as_762_, v_a_763_);
lean_dec_ref(v_a_763_);
lean_dec_ref(v_as_762_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object* v___y_766_, lean_object* v_as_767_, size_t v_i_768_, size_t v_stop_769_, lean_object* v_b_770_){
_start:
{
lean_object* v___y_772_; uint8_t v___x_776_; 
v___x_776_ = lean_usize_dec_eq(v_i_768_, v_stop_769_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v_fst_778_; uint8_t v___x_792_; 
v___x_777_ = lean_array_uget_borrowed(v_as_767_, v_i_768_);
v_fst_778_ = lean_ctor_get(v___x_777_, 0);
v___x_792_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_766_, v_fst_778_);
if (v___x_792_ == 0)
{
goto v___jp_779_;
}
else
{
if (v___x_776_ == 0)
{
v___y_772_ = v_b_770_;
goto v___jp_771_;
}
else
{
goto v___jp_779_;
}
}
v___jp_779_:
{
lean_object* v_entries_780_; lean_object* v_indexes_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
v_entries_780_ = lean_ctor_get(v_b_770_, 0);
v_indexes_781_ = lean_ctor_get(v_b_770_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_b_770_);
if (v_isSharedCheck_791_ == 0)
{
v___x_783_ = v_b_770_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_indexes_781_);
lean_inc(v_entries_780_);
lean_dec(v_b_770_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_i_785_; lean_object* v_entries_786_; lean_object* v_indexes_787_; lean_object* v___x_789_; 
v_i_785_ = lean_array_get_size(v_entries_780_);
lean_inc(v___x_777_);
v_entries_786_ = lean_array_push(v_entries_780_, v___x_777_);
lean_inc(v_fst_778_);
v_indexes_787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_i_785_, v_indexes_781_, v_fst_778_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v_indexes_787_);
lean_ctor_set(v___x_783_, 0, v_entries_786_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_entries_786_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_indexes_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v___y_772_ = v___x_789_;
goto v___jp_771_;
}
}
}
}
else
{
return v_b_770_;
}
v___jp_771_:
{
size_t v___x_773_; size_t v___x_774_; 
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_add(v_i_768_, v___x_773_);
v_i_768_ = v___x_774_;
v_b_770_ = v___y_772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object* v___y_793_, lean_object* v_as_794_, lean_object* v_i_795_, lean_object* v_stop_796_, lean_object* v_b_797_){
_start:
{
size_t v_i_boxed_798_; size_t v_stop_boxed_799_; lean_object* v_res_800_; 
v_i_boxed_798_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_stop_boxed_799_ = lean_unbox_usize(v_stop_796_);
lean_dec(v_stop_796_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_793_, v_as_794_, v_i_boxed_798_, v_stop_boxed_799_, v_b_797_);
lean_dec_ref(v_as_794_);
lean_dec_ref(v___y_793_);
return v_res_800_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0(void){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_box(0));
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_802_, uint8_t v_isCrossOrigin_803_, uint8_t v_methodChanged_804_){
_start:
{
lean_object* v___y_806_; lean_object* v___y_820_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_afterConnection_827_; 
v___x_825_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_826_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_802_);
v_afterConnection_827_ = l_Array_append___redArg(v___x_825_, v___x_826_);
lean_dec_ref(v___x_826_);
if (v_isCrossOrigin_803_ == 0)
{
v___y_820_ = v_afterConnection_827_;
goto v___jp_819_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_828_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_829_ = l_Array_append___redArg(v_afterConnection_827_, v___x_828_);
v___x_830_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_831_ = l_Array_append___redArg(v___x_829_, v___x_830_);
v___x_832_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_833_ = l_Array_append___redArg(v___x_831_, v___x_832_);
v___y_820_ = v___x_833_;
goto v___jp_819_;
}
v___jp_805_:
{
lean_object* v_entries_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_entries_807_ = lean_ctor_get(v_headers_802_, 0);
v___x_808_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_array_get_size(v_entries_807_);
v___x_811_ = lean_nat_dec_lt(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_dec_ref(v___y_806_);
return v___x_808_;
}
else
{
uint8_t v___x_812_; 
v___x_812_ = lean_nat_dec_le(v___x_810_, v___x_810_);
if (v___x_812_ == 0)
{
if (v___x_811_ == 0)
{
lean_dec_ref(v___y_806_);
return v___x_808_;
}
else
{
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v___x_813_ = ((size_t)0ULL);
v___x_814_ = lean_usize_of_nat(v___x_810_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_806_, v_entries_807_, v___x_813_, v___x_814_, v___x_808_);
lean_dec_ref(v___y_806_);
return v___x_815_;
}
}
else
{
size_t v___x_816_; size_t v___x_817_; lean_object* v___x_818_; 
v___x_816_ = ((size_t)0ULL);
v___x_817_ = lean_usize_of_nat(v___x_810_);
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_806_, v_entries_807_, v___x_816_, v___x_817_, v___x_808_);
lean_dec_ref(v___y_806_);
return v___x_818_;
}
}
}
v___jp_819_:
{
if (v_methodChanged_804_ == 0)
{
v___y_806_ = v___y_820_;
goto v___jp_805_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_821_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_822_ = l_Array_append___redArg(v___y_820_, v___x_821_);
v___x_823_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_824_ = l_Array_append___redArg(v___x_822_, v___x_823_);
v___y_806_ = v___x_824_;
goto v___jp_805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_834_, lean_object* v_isCrossOrigin_835_, lean_object* v_methodChanged_836_){
_start:
{
uint8_t v_isCrossOrigin_boxed_837_; uint8_t v_methodChanged_boxed_838_; lean_object* v_res_839_; 
v_isCrossOrigin_boxed_837_ = lean_unbox(v_isCrossOrigin_835_);
v_methodChanged_boxed_838_ = lean_unbox(v_methodChanged_836_);
v_res_839_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_834_, v_isCrossOrigin_boxed_837_, v_methodChanged_boxed_838_);
lean_dec_ref(v_headers_834_);
return v_res_839_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_841_, v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_00_u03b2_844_, lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_00_u03b2_844_, v_a_845_, v_x_846_);
lean_dec(v_x_846_);
lean_dec_ref(v_a_845_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1(lean_object* v_00_u03b2_849_, lean_object* v_data_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1___redArg(v_data_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_852_, lean_object* v_i_853_, lean_object* v_source_854_, lean_object* v_target_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3___redArg(v_i_853_, v_source_854_, v_target_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6___redArg(v_x_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(lean_object* v_m_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_buckets_863_; lean_object* v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v___x_867_; uint64_t v_fold_868_; uint64_t v___x_869_; uint64_t v___x_870_; uint64_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_buckets_863_ = lean_ctor_get(v_m_861_, 1);
v___x_864_ = lean_array_get_size(v_buckets_863_);
v___x_865_ = lean_string_hash(v_a_862_);
v___x_866_ = 32ULL;
v___x_867_ = lean_uint64_shift_right(v___x_865_, v___x_866_);
v_fold_868_ = lean_uint64_xor(v___x_865_, v___x_867_);
v___x_869_ = 16ULL;
v___x_870_ = lean_uint64_shift_right(v_fold_868_, v___x_869_);
v___x_871_ = lean_uint64_xor(v_fold_868_, v___x_870_);
v___x_872_ = lean_uint64_to_usize(v___x_871_);
v___x_873_ = lean_usize_of_nat(v___x_864_);
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_sub(v___x_873_, v___x_874_);
v___x_876_ = lean_usize_land(v___x_872_, v___x_875_);
v___x_877_ = lean_array_uget_borrowed(v_buckets_863_, v___x_876_);
v___x_878_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_862_, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg___boxed(lean_object* v_m_879_, lean_object* v_a_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_m_879_, v_a_880_);
lean_dec_ref(v_a_880_);
lean_dec_ref(v_m_879_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_883_, lean_object* v_origin_884_){
_start:
{
lean_object* v_entries_885_; lean_object* v_indexes_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_entries_885_ = lean_ctor_get(v_headers_883_, 0);
v_indexes_886_ = lean_ctor_get(v_headers_883_, 1);
v___x_887_ = l_Std_Http_Header_Name_host;
v___x_888_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_indexes_886_, v___x_887_);
if (v___x_888_ == 0)
{
lean_dec_ref(v_origin_884_);
return v_headers_883_;
}
else
{
lean_object* v___f_889_; lean_object* v___f_890_; uint8_t v___x_891_; 
v___f_889_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_890_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_891_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_889_, v___f_890_, v___x_887_, v_headers_883_);
if (v___x_891_ == 0)
{
lean_dec_ref(v_origin_884_);
return v_headers_883_;
}
else
{
lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_907_; 
lean_inc_ref(v_indexes_886_);
lean_inc_ref(v_entries_885_);
v_isSharedCheck_907_ = !lean_is_exclusive(v_headers_883_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_908_ = lean_ctor_get(v_headers_883_, 1);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_headers_883_, 0);
lean_dec(v_unused_909_);
v___x_893_ = v_headers_883_;
v_isShared_894_ = v_isSharedCheck_907_;
goto v_resetjp_892_;
}
else
{
lean_dec(v_headers_883_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_907_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_idxs_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_lastIdx_901_; lean_object* v___x_902_; lean_object* v_entries_903_; lean_object* v___x_905_; 
v___x_895_ = l_Std_Http_URI_Origin_hostHeader(v_origin_884_);
v___x_896_ = l_Std_Http_Header_Value_ofString_x21(v___x_895_);
v_idxs_897_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_886_, v___x_887_);
v___x_898_ = lean_array_get_size(v_idxs_897_);
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_sub(v___x_898_, v___x_899_);
v_lastIdx_901_ = lean_array_fget(v_idxs_897_, v___x_900_);
lean_dec(v___x_900_);
lean_dec(v_idxs_897_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_887_);
lean_ctor_set(v___x_902_, 1, v___x_896_);
v_entries_903_ = lean_array_fset(v_entries_885_, v_lastIdx_901_, v___x_902_);
lean_dec(v_lastIdx_901_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v_entries_903_);
v___x_905_ = v___x_893_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_entries_903_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_indexes_886_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(lean_object* v_00_u03b2_910_, lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
uint8_t v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_m_911_, v_a_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___boxed(lean_object* v_00_u03b2_914_, lean_object* v_m_915_, lean_object* v_a_916_){
_start:
{
uint8_t v_res_917_; lean_object* v_r_918_; 
v_res_917_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_00_u03b2_914_, v_m_915_, v_a_916_);
lean_dec_ref(v_a_916_);
lean_dec_ref(v_m_915_);
v_r_918_ = lean_box(v_res_917_);
return v_r_918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_919_){
_start:
{
switch(lean_obj_tag(v_x_919_))
{
case 0:
{
lean_object* v_query_920_; 
v_query_920_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_query_920_);
return v_query_920_;
}
case 1:
{
lean_object* v_uri_921_; lean_object* v_query_922_; 
v_uri_921_ = lean_ctor_get(v_x_919_, 0);
v_query_922_ = lean_ctor_get(v_uri_921_, 3);
lean_inc(v_query_922_);
return v_query_922_;
}
default: 
{
lean_object* v___x_923_; 
v___x_923_ = lean_box(0);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_924_);
lean_dec(v_x_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_926_, uint8_t v_isCrossOrigin_927_, lean_object* v_basePath_928_, lean_object* v_baseQuery_929_, lean_object* v_currentScheme_930_){
_start:
{
lean_object* v___y_932_; lean_object* v___y_933_; 
if (lean_obj_tag(v_ref_926_) == 0)
{
lean_object* v_uri_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v_currentScheme_930_);
lean_dec(v_baseQuery_929_);
lean_dec_ref(v_basePath_928_);
v_uri_936_ = lean_ctor_get(v_ref_926_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v_ref_926_);
if (v_isSharedCheck_978_ == 0)
{
v___x_938_ = v_ref_926_;
v_isShared_939_ = v_isSharedCheck_978_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_uri_936_);
lean_dec(v_ref_926_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_978_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_scheme_940_; lean_object* v_authority_941_; lean_object* v_path_942_; lean_object* v_query_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_976_; 
v_scheme_940_ = lean_ctor_get(v_uri_936_, 0);
v_authority_941_ = lean_ctor_get(v_uri_936_, 1);
v_path_942_ = lean_ctor_get(v_uri_936_, 2);
v_query_943_ = lean_ctor_get(v_uri_936_, 3);
v_isSharedCheck_976_ = !lean_is_exclusive(v_uri_936_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_uri_936_, 4);
lean_dec(v_unused_977_);
v___x_945_ = v_uri_936_;
v_isShared_946_ = v_isSharedCheck_976_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_query_943_);
lean_inc(v_path_942_);
lean_inc(v_authority_941_);
lean_inc(v_scheme_940_);
lean_dec(v_uri_936_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_976_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___y_948_; 
if (lean_obj_tag(v_authority_941_) == 0)
{
v___y_948_ = v_authority_941_;
goto v___jp_947_;
}
else
{
lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_975_; 
v_val_957_ = lean_ctor_get(v_authority_941_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_authority_941_);
if (v_isSharedCheck_975_ == 0)
{
v___x_959_ = v_authority_941_;
v_isShared_960_ = v_isSharedCheck_975_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v_authority_941_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_975_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_host_961_; lean_object* v_port_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v_host_961_ = lean_ctor_get(v_val_957_, 1);
v_port_962_ = lean_ctor_get(v_val_957_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v_val_957_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v_val_957_, 0);
lean_dec(v_unused_974_);
v___x_964_ = v_val_957_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_port_962_);
lean_inc(v_host_961_);
lean_dec(v_val_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_host_961_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_port_962_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_968_);
v___x_970_ = v___x_959_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v___y_948_ = v___x_970_;
goto v___jp_947_;
}
}
}
}
}
v___jp_947_:
{
if (v_isCrossOrigin_927_ == 0)
{
lean_object* v___x_949_; 
lean_dec(v___y_948_);
lean_del_object(v___x_945_);
lean_dec_ref(v_scheme_940_);
lean_del_object(v___x_938_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_path_942_);
lean_ctor_set(v___x_949_, 1, v_query_943_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v_stripped_952_; 
v___x_950_ = lean_box(0);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 4, v___x_950_);
lean_ctor_set(v___x_945_, 1, v___y_948_);
v_stripped_952_ = v___x_945_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_scheme_940_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___y_948_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_path_942_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_query_943_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v___x_950_);
v_stripped_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 1);
lean_ctor_set(v___x_938_, 0, v_stripped_952_);
v___x_954_ = v___x_938_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_stripped_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
}
else
{
lean_object* v_ref_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1020_; 
v_ref_979_ = lean_ctor_get(v_ref_926_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_ref_926_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_981_ = v_ref_926_;
v_isShared_982_ = v_isSharedCheck_1020_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_ref_979_);
lean_dec(v_ref_926_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1020_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_authority_983_; lean_object* v_path_984_; lean_object* v_query_985_; lean_object* v___y_987_; uint8_t v___y_988_; 
v_authority_983_ = lean_ctor_get(v_ref_979_, 0);
lean_inc(v_authority_983_);
v_path_984_ = lean_ctor_get(v_ref_979_, 1);
lean_inc_ref(v_path_984_);
v_query_985_ = lean_ctor_get(v_ref_979_, 2);
lean_inc(v_query_985_);
lean_dec_ref(v_ref_979_);
if (lean_obj_tag(v_authority_983_) == 0)
{
uint8_t v___x_989_; lean_object* v___y_991_; 
lean_del_object(v___x_981_);
lean_dec_ref(v_currentScheme_930_);
v___x_989_ = l_Std_Http_URI_Path_isEmpty(v_path_984_);
if (v___x_989_ == 0)
{
uint8_t v_absolute_992_; 
v_absolute_992_ = lean_ctor_get_uint8(v_path_984_, sizeof(void*)*1);
if (v_absolute_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = l_Std_Http_URI_Path_parent(v_basePath_928_);
v___x_994_ = l_Std_Http_URI_Path_join(v___x_993_, v_path_984_);
lean_dec_ref(v_path_984_);
v___y_991_ = v___x_994_;
goto v___jp_990_;
}
else
{
lean_dec_ref(v_basePath_928_);
v___y_991_ = v_path_984_;
goto v___jp_990_;
}
}
else
{
lean_dec_ref(v_path_984_);
v___y_991_ = v_basePath_928_;
goto v___jp_990_;
}
v___jp_990_:
{
if (v___x_989_ == 0)
{
v___y_987_ = v___y_991_;
v___y_988_ = v___x_989_;
goto v___jp_986_;
}
else
{
if (lean_obj_tag(v_query_985_) == 0)
{
v___y_987_ = v___y_991_;
v___y_988_ = v___x_989_;
goto v___jp_986_;
}
else
{
lean_dec(v_baseQuery_929_);
v___y_932_ = v___y_991_;
v___y_933_ = v_query_985_;
goto v___jp_931_;
}
}
}
}
else
{
lean_dec(v_baseQuery_929_);
lean_dec_ref(v_basePath_928_);
if (v_isCrossOrigin_927_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec_ref_known(v_authority_983_, 1);
lean_del_object(v___x_981_);
lean_dec_ref(v_currentScheme_930_);
v___x_995_ = l_Std_Http_URI_Path_normalize(v_path_984_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v_query_985_);
return v___x_996_;
}
else
{
lean_object* v_val_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1019_; 
v_val_997_ = lean_ctor_get(v_authority_983_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_authority_983_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_999_ = v_authority_983_;
v_isShared_1000_ = v_isSharedCheck_1019_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_val_997_);
lean_dec(v_authority_983_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1019_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_host_1001_; lean_object* v_port_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1017_; 
v_host_1001_ = lean_ctor_get(v_val_997_, 1);
v_port_1002_ = lean_ctor_get(v_val_997_, 2);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_val_997_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v_val_997_, 0);
lean_dec(v_unused_1018_);
v___x_1004_ = v_val_997_;
v_isShared_1005_ = v_isSharedCheck_1017_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_port_1002_);
lean_inc(v_host_1001_);
lean_dec(v_val_997_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1017_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v_stripped_1008_; 
v___x_1006_ = lean_box(0);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1006_);
v_stripped_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_host_1001_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_port_1002_);
v_stripped_1008_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_stripped_1008_);
v___x_1010_ = v___x_999_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_stripped_1008_);
v___x_1010_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v_af_1011_; lean_object* v___x_1013_; 
v_af_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_1011_, 0, v_currentScheme_930_);
lean_ctor_set(v_af_1011_, 1, v___x_1010_);
lean_ctor_set(v_af_1011_, 2, v_path_984_);
lean_ctor_set(v_af_1011_, 3, v_query_985_);
lean_ctor_set(v_af_1011_, 4, v___x_1006_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v_af_1011_);
v___x_1013_ = v___x_981_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_af_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
}
}
v___jp_986_:
{
if (v___y_988_ == 0)
{
lean_dec(v_baseQuery_929_);
v___y_932_ = v___y_987_;
v___y_933_ = v_query_985_;
goto v___jp_931_;
}
else
{
lean_dec(v_query_985_);
v___y_932_ = v___y_987_;
v___y_933_ = v_baseQuery_929_;
goto v___jp_931_;
}
}
}
}
v___jp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = l_Std_Http_URI_Path_normalize(v___y_932_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___y_933_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_1021_, lean_object* v_isCrossOrigin_1022_, lean_object* v_basePath_1023_, lean_object* v_baseQuery_1024_, lean_object* v_currentScheme_1025_){
_start:
{
uint8_t v_isCrossOrigin_boxed_1026_; lean_object* v_res_1027_; 
v_isCrossOrigin_boxed_1026_ = lean_unbox(v_isCrossOrigin_1022_);
v_res_1027_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_1021_, v_isCrossOrigin_boxed_1026_, v_basePath_1023_, v_baseQuery_1024_, v_currentScheme_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Std_Http_URI_Parser_parseURIReference(v___x_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_pos_1034_; lean_object* v_array_1035_; lean_object* v_idx_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_pos_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_pos_1034_);
v_array_1035_ = lean_ctor_get(v_pos_1034_, 0);
v_idx_1036_ = lean_ctor_get(v_pos_1034_, 1);
v___x_1037_ = lean_byte_array_size(v_array_1035_);
v___x_1038_ = lean_nat_dec_lt(v_idx_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec(v_pos_1034_);
return v___x_1033_;
}
else
{
lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; lean_object* v_unused_1048_; 
v_unused_1047_ = lean_ctor_get(v___x_1033_, 1);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v___x_1033_, 0);
lean_dec(v_unused_1048_);
v___x_1040_ = v___x_1033_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_dec(v___x_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 1);
lean_ctor_set(v___x_1040_, 1, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_pos_1034_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_1061_, lean_object* v_request_1062_, uint8_t v_bodyReplayable_1063_, uint8_t v_onlySafeRedirects_1064_, uint8_t v_responseVersion_1065_, lean_object* v_status_1066_, lean_object* v_responseHeaders_1067_){
_start:
{
uint8_t v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1075_; uint8_t v___y_1083_; lean_object* v___y_1084_; uint8_t v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; uint8_t v___y_1091_; lean_object* v___y_1092_; uint8_t v___y_1093_; uint8_t v___y_1094_; uint8_t v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1104_; uint8_t v___y_1105_; uint8_t v___y_1106_; lean_object* v___y_1107_; uint8_t v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; uint8_t v___y_1114_; lean_object* v___y_1115_; uint8_t v___y_1116_; uint8_t v___y_1117_; uint8_t v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; uint8_t v___y_1122_; uint8_t v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1128_; uint8_t v___y_1129_; uint8_t v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; uint8_t v___y_1134_; uint8_t v___y_1137_; uint8_t v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; uint8_t v___y_1144_; lean_object* v___y_1145_; uint8_t v___y_1147_; lean_object* v___y_1148_; uint8_t v___y_1149_; lean_object* v___y_1150_; uint8_t v___y_1151_; uint8_t v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; lean_object* v___y_1159_; uint8_t v___y_1160_; uint8_t v___y_1161_; lean_object* v___y_1162_; uint8_t v___y_1163_; uint8_t v___y_1164_; lean_object* v___y_1165_; uint8_t v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1168_; uint8_t v___y_1171_; lean_object* v___y_1172_; uint8_t v___y_1173_; uint8_t v___y_1174_; lean_object* v___y_1175_; uint8_t v___y_1176_; uint8_t v___y_1177_; lean_object* v___y_1178_; uint8_t v___y_1179_; lean_object* v___y_1180_; uint8_t v___y_1181_; lean_object* v___y_1183_; uint8_t v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; uint8_t v___y_1187_; uint8_t v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; uint8_t v___y_1191_; uint8_t v___y_1194_; lean_object* v___y_1195_; uint8_t v___y_1196_; uint8_t v___y_1197_; lean_object* v___y_1198_; uint8_t v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; uint8_t v___y_1203_; lean_object* v___y_1205_; uint8_t v___y_1206_; uint8_t v___y_1207_; uint8_t v___y_1208_; lean_object* v___y_1209_; uint8_t v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; uint8_t v___y_1214_; uint8_t v___y_1215_; uint16_t v___x_1218_; uint16_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = 300;
v___x_1219_ = l_Std_Http_Status_toCode(v_status_1066_);
v___x_1220_ = lean_uint16_dec_le(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
lean_dec_ref(v_current_1061_);
v___x_1221_ = lean_box(0);
return v___x_1221_;
}
else
{
uint16_t v___x_1222_; uint8_t v___x_1223_; lean_object* v___y_1225_; uint8_t v___y_1226_; uint8_t v___y_1227_; uint8_t v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; uint8_t v___y_1232_; uint8_t v___y_1233_; lean_object* v___y_1239_; uint8_t v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; uint8_t v___y_1245_; uint8_t v___y_1246_; lean_object* v___y_1249_; uint8_t v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; uint8_t v___y_1255_; lean_object* v___y_1258_; uint8_t v___y_1259_; lean_object* v___y_1260_; uint8_t v___y_1261_; uint8_t v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v_scheme_1265_; uint8_t v___y_1270_; uint8_t v___y_1315_; 
v___x_1222_ = 400;
v___x_1223_ = lean_uint16_dec_lt(v___x_1219_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1319_; 
lean_dec_ref(v_current_1061_);
v___x_1319_ = lean_box(0);
return v___x_1319_;
}
else
{
uint8_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = 0;
v___x_1321_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_1065_, v___x_1320_);
if (v___x_1321_ == 0)
{
v___y_1315_ = v___x_1321_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_box(15);
v___x_1323_ = l_Std_Http_instBEqStatus_beq(v_status_1066_, v___x_1322_);
if (v___x_1323_ == 0)
{
v___y_1315_ = v___x_1321_;
goto v___jp_1314_;
}
else
{
goto v___jp_1298_;
}
}
}
v___jp_1224_:
{
uint8_t v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = 8;
v___x_1235_ = l_Std_Http_instBEqMethod_beq(v___y_1227_, v___x_1234_);
if (v___x_1235_ == 0)
{
uint8_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = 9;
v___x_1237_ = l_Std_Http_instBEqMethod_beq(v___y_1227_, v___x_1236_);
v___y_1205_ = v___y_1225_;
v___y_1206_ = v___y_1226_;
v___y_1207_ = v___y_1227_;
v___y_1208_ = v___y_1233_;
v___y_1209_ = v___y_1229_;
v___y_1210_ = v___y_1228_;
v___y_1211_ = v___x_1234_;
v___y_1212_ = v___y_1230_;
v___y_1213_ = v___y_1231_;
v___y_1214_ = v___y_1232_;
v___y_1215_ = v___x_1237_;
goto v___jp_1204_;
}
else
{
v___y_1205_ = v___y_1225_;
v___y_1206_ = v___y_1226_;
v___y_1207_ = v___y_1227_;
v___y_1208_ = v___y_1233_;
v___y_1209_ = v___y_1229_;
v___y_1210_ = v___y_1228_;
v___y_1211_ = v___x_1234_;
v___y_1212_ = v___y_1230_;
v___y_1213_ = v___y_1231_;
v___y_1214_ = v___y_1232_;
v___y_1215_ = v___x_1223_;
goto v___jp_1204_;
}
}
v___jp_1238_:
{
uint8_t v___x_1247_; 
v___x_1247_ = l_Std_Http_instBEqMethod_beq(v___y_1242_, v___y_1240_);
if (v___x_1247_ == 0)
{
v___y_1225_ = v___y_1239_;
v___y_1226_ = v___y_1246_;
v___y_1227_ = v___y_1240_;
v___y_1228_ = v___y_1242_;
v___y_1229_ = v___y_1241_;
v___y_1230_ = v___y_1243_;
v___y_1231_ = v___y_1244_;
v___y_1232_ = v___y_1245_;
v___y_1233_ = v___x_1223_;
goto v___jp_1224_;
}
else
{
v___y_1225_ = v___y_1239_;
v___y_1226_ = v___y_1246_;
v___y_1227_ = v___y_1240_;
v___y_1228_ = v___y_1242_;
v___y_1229_ = v___y_1241_;
v___y_1230_ = v___y_1243_;
v___y_1231_ = v___y_1244_;
v___y_1232_ = v___y_1245_;
v___y_1233_ = v___y_1245_;
goto v___jp_1224_;
}
}
v___jp_1248_:
{
uint8_t v___x_1256_; 
v___x_1256_ = l_Std_Http_URI_instBEqOrigin_beq(v___y_1254_, v_current_1061_);
if (v___x_1256_ == 0)
{
v___y_1239_ = v___y_1249_;
v___y_1240_ = v___y_1250_;
v___y_1241_ = v___y_1252_;
v___y_1242_ = v___y_1251_;
v___y_1243_ = v___y_1253_;
v___y_1244_ = v___y_1254_;
v___y_1245_ = v___y_1255_;
v___y_1246_ = v___x_1223_;
goto v___jp_1238_;
}
else
{
v___y_1239_ = v___y_1249_;
v___y_1240_ = v___y_1250_;
v___y_1241_ = v___y_1252_;
v___y_1242_ = v___y_1251_;
v___y_1243_ = v___y_1253_;
v___y_1244_ = v___y_1254_;
v___y_1245_ = v___y_1255_;
v___y_1246_ = v___y_1255_;
goto v___jp_1238_;
}
}
v___jp_1257_:
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__0));
v___x_1267_ = lean_string_dec_eq(v_scheme_1265_, v___x_1266_);
lean_dec_ref(v_scheme_1265_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec_ref(v___y_1264_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v_current_1061_);
v___x_1268_ = lean_box(0);
return v___x_1268_;
}
else
{
v___y_1249_ = v___y_1258_;
v___y_1250_ = v___y_1259_;
v___y_1251_ = v___y_1261_;
v___y_1252_ = v___y_1260_;
v___y_1253_ = v___y_1263_;
v___y_1254_ = v___y_1264_;
v___y_1255_ = v___y_1262_;
goto v___jp_1248_;
}
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; uint8_t v___x_1274_; 
v___x_1271_ = l_Std_Http_Header_Name_location;
v___f_1272_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_1273_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_1274_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1272_, v___f_1273_, v___x_1271_, v_responseHeaders_1067_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec_ref(v_current_1061_);
v___x_1275_ = lean_box(0);
return v___x_1275_;
}
else
{
lean_object* v_entries_1276_; lean_object* v_indexes_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_entry_1280_; lean_object* v___x_1281_; lean_object* v_snd_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_entries_1276_ = lean_ctor_get(v_responseHeaders_1067_, 0);
v_indexes_1277_ = lean_ctor_get(v_responseHeaders_1067_, 1);
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_1277_, v___x_1271_);
v___x_1279_ = lean_unsigned_to_nat(0u);
v_entry_1280_ = lean_array_fget(v___x_1278_, v___x_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_array_fget_borrowed(v_entries_1276_, v_entry_1280_);
lean_dec(v_entry_1280_);
v_snd_1282_ = lean_ctor_get(v___x_1281_, 1);
v___f_1283_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
v___x_1284_ = lean_string_to_utf8(v_snd_1282_);
v___x_1285_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1283_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1286_; 
lean_dec_ref_known(v___x_1285_, 1);
lean_dec_ref(v_current_1061_);
v___x_1286_ = lean_box(0);
return v___x_1286_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1285_, 0);
lean_inc_n(v_a_1287_, 2);
lean_dec_ref_known(v___x_1285_, 1);
lean_inc_ref(v_current_1061_);
v___x_1288_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_1061_, v_a_1287_);
if (lean_obj_tag(v___x_1288_) == 1)
{
lean_object* v_val_1289_; uint8_t v_method_1290_; lean_object* v_uri_1291_; lean_object* v_headers_1292_; lean_object* v_scheme_1293_; uint8_t v_newMethod_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_val_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v_method_1290_ = lean_ctor_get_uint8(v_request_1062_, sizeof(void*)*2);
v_uri_1291_ = lean_ctor_get(v_request_1062_, 0);
v_headers_1292_ = lean_ctor_get(v_request_1062_, 1);
v_scheme_1293_ = lean_ctor_get(v_val_1289_, 0);
v_newMethod_1294_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_1290_, v_responseVersion_1065_, v_status_1066_);
v___x_1295_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_1296_ = lean_string_dec_eq(v_scheme_1293_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_inc_ref(v_scheme_1293_);
v___y_1258_ = v_headers_1292_;
v___y_1259_ = v_method_1290_;
v___y_1260_ = v_a_1287_;
v___y_1261_ = v_newMethod_1294_;
v___y_1262_ = v___y_1270_;
v___y_1263_ = v_uri_1291_;
v___y_1264_ = v_val_1289_;
v_scheme_1265_ = v_scheme_1293_;
goto v___jp_1257_;
}
else
{
if (v___y_1270_ == 0)
{
v___y_1249_ = v_headers_1292_;
v___y_1250_ = v_method_1290_;
v___y_1251_ = v_newMethod_1294_;
v___y_1252_ = v_a_1287_;
v___y_1253_ = v_uri_1291_;
v___y_1254_ = v_val_1289_;
v___y_1255_ = v___y_1270_;
goto v___jp_1248_;
}
else
{
lean_inc_ref(v_scheme_1293_);
v___y_1258_ = v_headers_1292_;
v___y_1259_ = v_method_1290_;
v___y_1260_ = v_a_1287_;
v___y_1261_ = v_newMethod_1294_;
v___y_1262_ = v___y_1270_;
v___y_1263_ = v_uri_1291_;
v___y_1264_ = v_val_1289_;
v_scheme_1265_ = v_scheme_1293_;
goto v___jp_1257_;
}
}
}
else
{
lean_object* v___x_1297_; 
lean_dec(v___x_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_current_1061_);
v___x_1297_ = lean_box(0);
return v___x_1297_;
}
}
}
}
v___jp_1298_:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_box(19);
v___x_1300_ = l_Std_Http_instBEqStatus_beq(v_status_1066_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = lean_box(20);
v___x_1302_ = l_Std_Http_instBEqStatus_beq(v_status_1066_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_box(18);
v___x_1304_ = l_Std_Http_instBEqStatus_beq(v_status_1066_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = lean_box(14);
v___x_1306_ = l_Std_Http_instBEqStatus_beq(v_status_1066_, v___x_1305_);
if (v___x_1306_ == 0)
{
if (v_onlySafeRedirects_1064_ == 0)
{
v___y_1270_ = v_onlySafeRedirects_1064_;
goto v___jp_1269_;
}
else
{
uint8_t v_method_1307_; uint8_t v___x_1308_; 
v_method_1307_ = lean_ctor_get_uint8(v_request_1062_, sizeof(void*)*2);
v___x_1308_ = l_Std_Http_Method_isSafe(v_method_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_dec_ref(v_current_1061_);
v___x_1309_ = lean_box(0);
return v___x_1309_;
}
else
{
v___y_1270_ = v___x_1306_;
goto v___jp_1269_;
}
}
}
else
{
lean_object* v___x_1310_; 
lean_dec_ref(v_current_1061_);
v___x_1310_ = lean_box(0);
return v___x_1310_;
}
}
else
{
lean_object* v___x_1311_; 
lean_dec_ref(v_current_1061_);
v___x_1311_ = lean_box(0);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1312_; 
lean_dec_ref(v_current_1061_);
v___x_1312_ = lean_box(0);
return v___x_1312_;
}
}
else
{
lean_object* v___x_1313_; 
lean_dec_ref(v_current_1061_);
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
}
v___jp_1314_:
{
if (v___y_1315_ == 0)
{
goto v___jp_1298_;
}
else
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = lean_box(16);
v___x_1317_ = l_Std_Http_instBEqStatus_beq(v_status_1066_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_dec_ref(v_current_1061_);
v___x_1318_ = lean_box(0);
return v___x_1318_;
}
else
{
goto v___jp_1298_;
}
}
}
}
v___jp_1068_:
{
lean_object* v_scheme_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_rewrittenTarget_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_scheme_1076_ = lean_ctor_get(v_current_1061_, 0);
lean_inc_ref(v_scheme_1076_);
lean_dec_ref(v_current_1061_);
v___x_1077_ = l_Std_Http_RequestTarget_pathOrRoot(v___y_1072_);
v___x_1078_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v___y_1072_);
v_rewrittenTarget_1079_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v___y_1071_, v___y_1069_, v___x_1077_, v___x_1078_, v_scheme_1076_);
v___x_1080_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1080_, 0, v___y_1074_);
lean_ctor_set(v___x_1080_, 1, v_rewrittenTarget_1079_);
lean_ctor_set(v___x_1080_, 2, v___y_1073_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*3, v___y_1070_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*3 + 1, v___y_1075_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*3 + 2, v___y_1069_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
v___jp_1082_:
{
uint8_t v___x_1089_; 
v___x_1089_ = 0;
v___y_1069_ = v___y_1083_;
v___y_1070_ = v___y_1085_;
v___y_1071_ = v___y_1084_;
v___y_1072_ = v___y_1086_;
v___y_1073_ = v___y_1088_;
v___y_1074_ = v___y_1087_;
v___y_1075_ = v___x_1089_;
goto v___jp_1068_;
}
v___jp_1090_:
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Std_Http_instBEqMethod_beq(v___y_1094_, v___y_1095_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = 9;
v___x_1101_ = l_Std_Http_instBEqMethod_beq(v___y_1094_, v___x_1100_);
if (v___x_1101_ == 0)
{
if (v___y_1093_ == 0)
{
uint8_t v___x_1102_; 
v___x_1102_ = 1;
v___y_1069_ = v___y_1091_;
v___y_1070_ = v___y_1094_;
v___y_1071_ = v___y_1092_;
v___y_1072_ = v___y_1096_;
v___y_1073_ = v___y_1098_;
v___y_1074_ = v___y_1097_;
v___y_1075_ = v___x_1102_;
goto v___jp_1068_;
}
else
{
v___y_1083_ = v___y_1091_;
v___y_1084_ = v___y_1092_;
v___y_1085_ = v___y_1094_;
v___y_1086_ = v___y_1096_;
v___y_1087_ = v___y_1097_;
v___y_1088_ = v___y_1098_;
goto v___jp_1082_;
}
}
else
{
v___y_1083_ = v___y_1091_;
v___y_1084_ = v___y_1092_;
v___y_1085_ = v___y_1094_;
v___y_1086_ = v___y_1096_;
v___y_1087_ = v___y_1097_;
v___y_1088_ = v___y_1098_;
goto v___jp_1082_;
}
}
else
{
v___y_1083_ = v___y_1091_;
v___y_1084_ = v___y_1092_;
v___y_1085_ = v___y_1094_;
v___y_1086_ = v___y_1096_;
v___y_1087_ = v___y_1097_;
v___y_1088_ = v___y_1098_;
goto v___jp_1082_;
}
}
v___jp_1103_:
{
if (v_bodyReplayable_1063_ == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1107_);
lean_dec_ref(v_current_1061_);
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
else
{
v___y_1091_ = v___y_1104_;
v___y_1092_ = v___y_1107_;
v___y_1093_ = v___y_1106_;
v___y_1094_ = v___y_1105_;
v___y_1095_ = v___y_1108_;
v___y_1096_ = v___y_1109_;
v___y_1097_ = v___y_1111_;
v___y_1098_ = v___y_1110_;
goto v___jp_1090_;
}
}
v___jp_1113_:
{
uint8_t v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = 9;
v___x_1124_ = l_Std_Http_instBEqMethod_beq(v___y_1117_, v___x_1123_);
if (v___x_1124_ == 0)
{
v___y_1104_ = v___y_1114_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___y_1116_;
v___y_1107_ = v___y_1115_;
v___y_1108_ = v___y_1118_;
v___y_1109_ = v___y_1119_;
v___y_1110_ = v___y_1121_;
v___y_1111_ = v___y_1120_;
goto v___jp_1103_;
}
else
{
if (v___y_1122_ == 0)
{
v___y_1091_ = v___y_1114_;
v___y_1092_ = v___y_1115_;
v___y_1093_ = v___y_1116_;
v___y_1094_ = v___y_1117_;
v___y_1095_ = v___y_1118_;
v___y_1096_ = v___y_1119_;
v___y_1097_ = v___y_1120_;
v___y_1098_ = v___y_1121_;
goto v___jp_1090_;
}
else
{
v___y_1104_ = v___y_1114_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___y_1116_;
v___y_1107_ = v___y_1115_;
v___y_1108_ = v___y_1118_;
v___y_1109_ = v___y_1119_;
v___y_1110_ = v___y_1121_;
v___y_1111_ = v___y_1120_;
goto v___jp_1103_;
}
}
}
v___jp_1125_:
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Std_Http_instBEqMethod_beq(v___y_1129_, v___y_1130_);
if (v___x_1135_ == 0)
{
v___y_1114_ = v___y_1126_;
v___y_1115_ = v___y_1128_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
v___y_1119_ = v___y_1131_;
v___y_1120_ = v___y_1133_;
v___y_1121_ = v___y_1132_;
v___y_1122_ = v___y_1134_;
goto v___jp_1113_;
}
else
{
if (v___y_1134_ == 0)
{
v___y_1091_ = v___y_1126_;
v___y_1092_ = v___y_1128_;
v___y_1093_ = v___y_1127_;
v___y_1094_ = v___y_1129_;
v___y_1095_ = v___y_1130_;
v___y_1096_ = v___y_1131_;
v___y_1097_ = v___y_1133_;
v___y_1098_ = v___y_1132_;
goto v___jp_1090_;
}
else
{
v___y_1114_ = v___y_1126_;
v___y_1115_ = v___y_1128_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
v___y_1119_ = v___y_1131_;
v___y_1120_ = v___y_1133_;
v___y_1121_ = v___y_1132_;
v___y_1122_ = v___y_1134_;
goto v___jp_1113_;
}
}
}
v___jp_1136_:
{
if (v___y_1138_ == 0)
{
v___y_1126_ = v___y_1137_;
v___y_1127_ = v___y_1138_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___y_1140_;
v___y_1130_ = v___y_1141_;
v___y_1131_ = v___y_1142_;
v___y_1132_ = v___y_1145_;
v___y_1133_ = v___y_1143_;
v___y_1134_ = v___y_1144_;
goto v___jp_1125_;
}
else
{
if (v___y_1144_ == 0)
{
v___y_1091_ = v___y_1137_;
v___y_1092_ = v___y_1139_;
v___y_1093_ = v___y_1138_;
v___y_1094_ = v___y_1140_;
v___y_1095_ = v___y_1141_;
v___y_1096_ = v___y_1142_;
v___y_1097_ = v___y_1143_;
v___y_1098_ = v___y_1145_;
goto v___jp_1090_;
}
else
{
v___y_1126_ = v___y_1137_;
v___y_1127_ = v___y_1138_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___y_1140_;
v___y_1130_ = v___y_1141_;
v___y_1131_ = v___y_1142_;
v___y_1132_ = v___y_1145_;
v___y_1133_ = v___y_1143_;
v___y_1134_ = v___y_1144_;
goto v___jp_1125_;
}
}
}
v___jp_1146_:
{
lean_object* v_scrubbed_1156_; 
v_scrubbed_1156_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v___y_1148_, v___y_1147_, v___y_1151_);
if (v___y_1147_ == 0)
{
v___y_1137_ = v___y_1147_;
v___y_1138_ = v___y_1151_;
v___y_1139_ = v___y_1150_;
v___y_1140_ = v___y_1149_;
v___y_1141_ = v___y_1152_;
v___y_1142_ = v___y_1153_;
v___y_1143_ = v___y_1154_;
v___y_1144_ = v___y_1155_;
v___y_1145_ = v_scrubbed_1156_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1157_; 
lean_inc_ref(v___y_1154_);
v___x_1157_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_1156_, v___y_1154_);
v___y_1137_ = v___y_1147_;
v___y_1138_ = v___y_1151_;
v___y_1139_ = v___y_1150_;
v___y_1140_ = v___y_1149_;
v___y_1141_ = v___y_1152_;
v___y_1142_ = v___y_1153_;
v___y_1143_ = v___y_1154_;
v___y_1144_ = v___y_1155_;
v___y_1145_ = v___x_1157_;
goto v___jp_1136_;
}
}
v___jp_1158_:
{
if (v___y_1166_ == 0)
{
lean_object* v___x_1169_; 
lean_dec_ref(v___y_1167_);
lean_dec_ref(v___y_1162_);
lean_dec_ref(v_current_1061_);
v___x_1169_ = lean_box(0);
return v___x_1169_;
}
else
{
v___y_1147_ = v___y_1160_;
v___y_1148_ = v___y_1159_;
v___y_1149_ = v___y_1163_;
v___y_1150_ = v___y_1162_;
v___y_1151_ = v___y_1161_;
v___y_1152_ = v___y_1164_;
v___y_1153_ = v___y_1165_;
v___y_1154_ = v___y_1167_;
v___y_1155_ = v___y_1168_;
goto v___jp_1146_;
}
}
v___jp_1170_:
{
if (v___y_1173_ == 0)
{
v___y_1159_ = v___y_1172_;
v___y_1160_ = v___y_1171_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1175_;
v___y_1163_ = v___y_1174_;
v___y_1164_ = v___y_1177_;
v___y_1165_ = v___y_1178_;
v___y_1166_ = v___y_1179_;
v___y_1167_ = v___y_1180_;
v___y_1168_ = v___y_1181_;
goto v___jp_1158_;
}
else
{
if (v___y_1181_ == 0)
{
v___y_1147_ = v___y_1171_;
v___y_1148_ = v___y_1172_;
v___y_1149_ = v___y_1174_;
v___y_1150_ = v___y_1175_;
v___y_1151_ = v___y_1176_;
v___y_1152_ = v___y_1177_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___y_1180_;
v___y_1155_ = v___y_1181_;
goto v___jp_1146_;
}
else
{
v___y_1159_ = v___y_1172_;
v___y_1160_ = v___y_1171_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1175_;
v___y_1163_ = v___y_1174_;
v___y_1164_ = v___y_1177_;
v___y_1165_ = v___y_1178_;
v___y_1166_ = v___y_1179_;
v___y_1167_ = v___y_1180_;
v___y_1168_ = v___y_1181_;
goto v___jp_1158_;
}
}
}
v___jp_1182_:
{
if (v_bodyReplayable_1063_ == 0)
{
lean_object* v___x_1192_; 
lean_dec_ref(v___y_1190_);
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_current_1061_);
v___x_1192_ = lean_box(0);
return v___x_1192_;
}
else
{
v___y_1147_ = v___y_1184_;
v___y_1148_ = v___y_1183_;
v___y_1149_ = v___y_1187_;
v___y_1150_ = v___y_1186_;
v___y_1151_ = v___y_1185_;
v___y_1152_ = v___y_1188_;
v___y_1153_ = v___y_1189_;
v___y_1154_ = v___y_1190_;
v___y_1155_ = v___y_1191_;
goto v___jp_1146_;
}
}
v___jp_1193_:
{
if (v___y_1196_ == 0)
{
v___y_1183_ = v___y_1195_;
v___y_1184_ = v___y_1194_;
v___y_1185_ = v___y_1199_;
v___y_1186_ = v___y_1198_;
v___y_1187_ = v___y_1197_;
v___y_1188_ = v___y_1200_;
v___y_1189_ = v___y_1201_;
v___y_1190_ = v___y_1202_;
v___y_1191_ = v___y_1203_;
goto v___jp_1182_;
}
else
{
if (v___y_1203_ == 0)
{
v___y_1147_ = v___y_1194_;
v___y_1148_ = v___y_1195_;
v___y_1149_ = v___y_1197_;
v___y_1150_ = v___y_1198_;
v___y_1151_ = v___y_1199_;
v___y_1152_ = v___y_1200_;
v___y_1153_ = v___y_1201_;
v___y_1154_ = v___y_1202_;
v___y_1155_ = v___y_1203_;
goto v___jp_1146_;
}
else
{
v___y_1183_ = v___y_1195_;
v___y_1184_ = v___y_1194_;
v___y_1185_ = v___y_1199_;
v___y_1186_ = v___y_1198_;
v___y_1187_ = v___y_1197_;
v___y_1188_ = v___y_1200_;
v___y_1189_ = v___y_1201_;
v___y_1190_ = v___y_1202_;
v___y_1191_ = v___y_1203_;
goto v___jp_1182_;
}
}
}
v___jp_1204_:
{
uint8_t v___x_1216_; uint8_t v_isPost_1217_; 
v___x_1216_ = 23;
v_isPost_1217_ = l_Std_Http_instBEqMethod_beq(v___y_1207_, v___x_1216_);
switch(lean_obj_tag(v_status_1066_))
{
case 15:
{
v___y_1171_ = v___y_1206_;
v___y_1172_ = v___y_1205_;
v___y_1173_ = v___y_1215_;
v___y_1174_ = v___y_1210_;
v___y_1175_ = v___y_1209_;
v___y_1176_ = v___y_1208_;
v___y_1177_ = v___y_1211_;
v___y_1178_ = v___y_1212_;
v___y_1179_ = v_isPost_1217_;
v___y_1180_ = v___y_1213_;
v___y_1181_ = v___y_1214_;
goto v___jp_1170_;
}
case 16:
{
v___y_1171_ = v___y_1206_;
v___y_1172_ = v___y_1205_;
v___y_1173_ = v___y_1215_;
v___y_1174_ = v___y_1210_;
v___y_1175_ = v___y_1209_;
v___y_1176_ = v___y_1208_;
v___y_1177_ = v___y_1211_;
v___y_1178_ = v___y_1212_;
v___y_1179_ = v_isPost_1217_;
v___y_1180_ = v___y_1213_;
v___y_1181_ = v___y_1214_;
goto v___jp_1170_;
}
case 21:
{
v___y_1194_ = v___y_1206_;
v___y_1195_ = v___y_1205_;
v___y_1196_ = v___y_1215_;
v___y_1197_ = v___y_1210_;
v___y_1198_ = v___y_1209_;
v___y_1199_ = v___y_1208_;
v___y_1200_ = v___y_1211_;
v___y_1201_ = v___y_1212_;
v___y_1202_ = v___y_1213_;
v___y_1203_ = v___y_1214_;
goto v___jp_1193_;
}
case 22:
{
v___y_1194_ = v___y_1206_;
v___y_1195_ = v___y_1205_;
v___y_1196_ = v___y_1215_;
v___y_1197_ = v___y_1210_;
v___y_1198_ = v___y_1209_;
v___y_1199_ = v___y_1208_;
v___y_1200_ = v___y_1211_;
v___y_1201_ = v___y_1212_;
v___y_1202_ = v___y_1213_;
v___y_1203_ = v___y_1214_;
goto v___jp_1193_;
}
default: 
{
v___y_1147_ = v___y_1206_;
v___y_1148_ = v___y_1205_;
v___y_1149_ = v___y_1210_;
v___y_1150_ = v___y_1209_;
v___y_1151_ = v___y_1208_;
v___y_1152_ = v___y_1211_;
v___y_1153_ = v___y_1212_;
v___y_1154_ = v___y_1213_;
v___y_1155_ = v___y_1214_;
goto v___jp_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_1324_, lean_object* v_request_1325_, lean_object* v_bodyReplayable_1326_, lean_object* v_onlySafeRedirects_1327_, lean_object* v_responseVersion_1328_, lean_object* v_status_1329_, lean_object* v_responseHeaders_1330_){
_start:
{
uint8_t v_bodyReplayable_boxed_1331_; uint8_t v_onlySafeRedirects_boxed_1332_; uint8_t v_responseVersion_boxed_1333_; lean_object* v_res_1334_; 
v_bodyReplayable_boxed_1331_ = lean_unbox(v_bodyReplayable_1326_);
v_onlySafeRedirects_boxed_1332_ = lean_unbox(v_onlySafeRedirects_1327_);
v_responseVersion_boxed_1333_ = lean_unbox(v_responseVersion_1328_);
v_res_1334_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1324_, v_request_1325_, v_bodyReplayable_boxed_1331_, v_onlySafeRedirects_boxed_1332_, v_responseVersion_boxed_1333_, v_status_1329_, v_responseHeaders_1330_);
lean_dec_ref(v_responseHeaders_1330_);
lean_dec(v_status_1329_);
lean_dec_ref(v_request_1325_);
return v_res_1334_;
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
