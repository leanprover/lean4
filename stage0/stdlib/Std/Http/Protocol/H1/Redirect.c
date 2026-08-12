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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Std_Http_Protocol_H1_RedirectBodyAction_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(lean_object* v_empty_27_){
_start:
{
lean_inc(v_empty_27_);
return v_empty_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg___boxed(lean_object* v_empty_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(v_empty_28_);
lean_dec(v_empty_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_empty_33_){
_start:
{
lean_inc(v_empty_33_);
return v_empty_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_empty_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_empty_37_);
lean_dec(v_empty_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(lean_object* v_replay_40_){
_start:
{
lean_inc(v_replay_40_);
return v_replay_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg___boxed(lean_object* v_replay_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(v_replay_41_);
lean_dec(v_replay_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_replay_46_){
_start:
{
lean_inc(v_replay_46_);
return v_replay_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_replay_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_replay_50_);
lean_dec(v_replay_50_);
return v_res_52_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(lean_object* v_n_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_nat_dec_le(v_n_53_, v___x_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = 1;
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = 0;
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat___boxed(lean_object* v_n_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(v_n_58_);
lean_dec(v_n_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(uint8_t v_x_61_, uint8_t v_y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_63_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_x_61_);
v___x_64_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_y_62_);
v___x_65_ = lean_nat_dec_eq(v___x_63_, v___x_64_);
lean_dec(v___x_64_);
lean_dec(v___x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction___boxed(lean_object* v_x_66_, lean_object* v_y_67_){
_start:
{
uint8_t v_x_13__boxed_68_; uint8_t v_y_14__boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v_x_13__boxed_68_ = lean_unbox(v_x_66_);
v_y_14__boxed_69_ = lean_unbox(v_y_67_);
v_res_70_ = l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(v_x_13__boxed_68_, v_y_14__boxed_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(uint8_t v_x_82_, lean_object* v_prec_83_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_92_; 
if (v_x_82_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1024u);
v___x_99_ = lean_nat_dec_le(v___x_98_, v_prec_83_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_85_ = v___x_100_;
goto v___jp_84_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_85_ = v___x_101_;
goto v___jp_84_;
}
}
else
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_83_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_92_ = v___x_104_;
goto v___jp_91_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_92_ = v___x_105_;
goto v___jp_91_;
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_83_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_83_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed(lean_object* v_x_106_, lean_object* v_prec_107_){
_start:
{
uint8_t v_x_121__boxed_108_; lean_object* v_res_109_; 
v_x_121__boxed_108_ = lean_unbox(v_x_106_);
v_res_109_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_x_121__boxed_108_, v_prec_107_);
lean_dec(v_prec_107_);
return v_res_109_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default(void){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction(void){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Protocol_H1_instReprRedirectPlan_repr_spec__0(lean_object* v_a_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_nat_to_int(v_a_114_);
return v___x_115_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(10u);
v___x_130_ = lean_nat_to_int(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(11u);
v___x_144_ = lean_nat_to_int(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(14u);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(17u);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0));
v___x_157_ = lean_string_length(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24);
v___x_159_ = lean_nat_to_int(v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(lean_object* v_x_164_){
_start:
{
lean_object* v_origin_165_; lean_object* v_target_166_; uint8_t v_method_167_; lean_object* v_headers_168_; uint8_t v_bodyAction_169_; uint8_t v_isCrossOrigin_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_origin_165_ = lean_ctor_get(v_x_164_, 0);
lean_inc_ref(v_origin_165_);
v_target_166_ = lean_ctor_get(v_x_164_, 1);
lean_inc(v_target_166_);
v_method_167_ = lean_ctor_get_uint8(v_x_164_, sizeof(void*)*3);
v_headers_168_ = lean_ctor_get(v_x_164_, 2);
lean_inc_ref(v_headers_168_);
v_bodyAction_169_ = lean_ctor_get_uint8(v_x_164_, sizeof(void*)*3 + 1);
v_isCrossOrigin_170_ = lean_ctor_get_uint8(v_x_164_, sizeof(void*)*3 + 2);
lean_dec_ref(v_x_164_);
v___x_171_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5));
v___x_172_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6));
v___x_173_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_origin_165_);
v___x_176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_173_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = 0;
v___x_178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*1, v___x_177_);
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_172_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9));
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_box(1);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11));
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_171_);
v___x_187_ = l_Std_Http_instReprRequestTarget_repr(v_target_166_, v___x_174_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_173_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_177_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_186_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_180_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_182_);
v___x_193_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13));
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_171_);
v___x_196_ = l_Std_Http_instReprMethod_repr(v_method_167_, v___x_174_);
v___x_197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_173_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_177_);
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_195_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_180_);
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_182_);
v___x_202_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15));
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_171_);
v___x_205_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16);
v___x_206_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_168_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*1, v___x_177_);
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_204_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_180_);
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_182_);
v___x_212_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18));
v___x_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_171_);
v___x_215_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19);
v___x_216_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_bodyAction_169_, v___x_174_);
v___x_217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*1, v___x_177_);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_214_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_180_);
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_182_);
v___x_222_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21));
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_171_);
v___x_225_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22);
v___x_226_ = l_Bool_repr___redArg(v_isCrossOrigin_170_);
v___x_227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_177_);
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_224_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25);
v___x_231_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26));
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_229_);
v___x_233_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27));
v___x_234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_230_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_177_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(lean_object* v_x_237_, lean_object* v_prec_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(v_x_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed(lean_object* v_x_240_, lean_object* v_prec_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(v_x_240_, v_prec_241_);
lean_dec(v_prec_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx(lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_unsigned_to_nat(0u);
return v___x_246_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_unsigned_to_nat(1u);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___boxed(lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx(v_x_248_);
lean_dec(v_x_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(lean_object* v_t_250_, lean_object* v_k_251_){
_start:
{
if (lean_obj_tag(v_t_250_) == 0)
{
return v_k_251_;
}
else
{
lean_object* v_plan_252_; lean_object* v___x_253_; 
v_plan_252_ = lean_ctor_get(v_t_250_, 0);
lean_inc_ref(v_plan_252_);
lean_dec_ref_known(v_t_250_, 1);
v___x_253_ = lean_apply_1(v_k_251_, v_plan_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(lean_object* v_motive_254_, lean_object* v_ctorIdx_255_, lean_object* v_t_256_, lean_object* v_h_257_, lean_object* v_k_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_256_, v_k_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___boxed(lean_object* v_motive_260_, lean_object* v_ctorIdx_261_, lean_object* v_t_262_, lean_object* v_h_263_, lean_object* v_k_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(v_motive_260_, v_ctorIdx_261_, v_t_262_, v_h_263_, v_k_264_);
lean_dec(v_ctorIdx_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim___redArg(lean_object* v_t_266_, lean_object* v_done_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_266_, v_done_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim(lean_object* v_motive_269_, lean_object* v_t_270_, lean_object* v_h_271_, lean_object* v_done_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_270_, v_done_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim___redArg(lean_object* v_t_274_, lean_object* v_follow_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_274_, v_follow_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_follow_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_278_, v_follow_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_box(0);
return v___x_282_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_box(0);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(lean_object* v_current_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v_uri_286_; lean_object* v_authority_287_; 
lean_dec_ref(v_current_284_);
v_uri_286_ = lean_ctor_get(v_x_285_, 0);
lean_inc_ref(v_uri_286_);
lean_dec_ref_known(v_x_285_, 1);
v_authority_287_ = lean_ctor_get(v_uri_286_, 1);
lean_inc(v_authority_287_);
if (lean_obj_tag(v_authority_287_) == 0)
{
lean_object* v___x_288_; 
lean_dec_ref(v_uri_286_);
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_304_; 
v_val_289_ = lean_ctor_get(v_authority_287_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_authority_287_);
if (v_isSharedCheck_304_ == 0)
{
v___x_291_ = v_authority_287_;
v_isShared_292_ = v_isSharedCheck_304_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v_authority_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_304_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_scheme_293_; lean_object* v_host_294_; lean_object* v_port_295_; uint16_t v___y_297_; 
v_scheme_293_ = lean_ctor_get(v_uri_286_, 0);
lean_inc_ref(v_scheme_293_);
lean_dec_ref(v_uri_286_);
v_host_294_ = lean_ctor_get(v_val_289_, 1);
lean_inc_ref(v_host_294_);
v_port_295_ = lean_ctor_get(v_val_289_, 2);
lean_inc(v_port_295_);
lean_dec(v_val_289_);
if (lean_obj_tag(v_port_295_) == 2)
{
uint16_t v_port_302_; 
v_port_302_ = lean_ctor_get_uint16(v_port_295_, 0);
lean_dec_ref_known(v_port_295_, 0);
v___y_297_ = v_port_302_;
goto v___jp_296_;
}
else
{
uint16_t v___x_303_; 
lean_dec(v_port_295_);
v___x_303_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_293_);
v___y_297_ = v___x_303_;
goto v___jp_296_;
}
v___jp_296_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_298_, 0, v_scheme_293_);
lean_ctor_set(v___x_298_, 1, v_host_294_);
lean_ctor_set_uint16(v___x_298_, sizeof(void*)*2, v___y_297_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_298_);
v___x_300_ = v___x_291_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v_ref_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_337_; 
v_ref_305_ = lean_ctor_get(v_x_285_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_337_ == 0)
{
v___x_307_ = v_x_285_;
v_isShared_308_ = v_isSharedCheck_337_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_ref_305_);
lean_dec(v_x_285_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_337_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_authority_309_; 
v_authority_309_ = lean_ctor_get(v_ref_305_, 0);
lean_inc(v_authority_309_);
lean_dec_ref(v_ref_305_);
if (lean_obj_tag(v_authority_309_) == 1)
{
lean_object* v_val_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_333_; 
lean_del_object(v___x_307_);
v_val_310_ = lean_ctor_get(v_authority_309_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_authority_309_);
if (v_isSharedCheck_333_ == 0)
{
v___x_312_ = v_authority_309_;
v_isShared_313_ = v_isSharedCheck_333_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_val_310_);
lean_dec(v_authority_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_333_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_host_314_; lean_object* v_port_315_; uint16_t v___y_317_; 
v_host_314_ = lean_ctor_get(v_val_310_, 1);
lean_inc_ref(v_host_314_);
v_port_315_ = lean_ctor_get(v_val_310_, 2);
lean_inc(v_port_315_);
lean_dec(v_val_310_);
if (lean_obj_tag(v_port_315_) == 2)
{
uint16_t v_port_330_; 
v_port_330_ = lean_ctor_get_uint16(v_port_315_, 0);
lean_dec_ref_known(v_port_315_, 0);
v___y_317_ = v_port_330_;
goto v___jp_316_;
}
else
{
lean_object* v_scheme_331_; uint16_t v___x_332_; 
lean_dec(v_port_315_);
v_scheme_331_ = lean_ctor_get(v_current_284_, 0);
v___x_332_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_331_);
v___y_317_ = v___x_332_;
goto v___jp_316_;
}
v___jp_316_:
{
lean_object* v_scheme_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_scheme_318_ = lean_ctor_get(v_current_284_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_current_284_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_current_284_, 1);
lean_dec(v_unused_329_);
v___x_320_ = v_current_284_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_scheme_318_);
lean_dec(v_current_284_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v_host_314_);
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_scheme_318_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_host_314_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
lean_ctor_set_uint16(v___x_323_, sizeof(void*)*2, v___y_317_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_323_);
v___x_325_ = v___x_312_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
else
{
lean_object* v___x_335_; 
lean_dec(v_authority_309_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v_current_284_);
v___x_335_ = v___x_307_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_current_284_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t v_originalMethod_338_, uint8_t v_responseVersion_339_, lean_object* v_x_340_){
_start:
{
uint8_t v___y_342_; 
switch(lean_obj_tag(v_x_340_))
{
case 17:
{
uint8_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 9;
v___x_350_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_338_, v___x_349_);
if (v___x_350_ == 0)
{
uint8_t v___x_351_; 
v___x_351_ = 8;
return v___x_351_;
}
else
{
return v___x_349_;
}
}
case 15:
{
goto v___jp_344_;
}
case 16:
{
goto v___jp_344_;
}
default: 
{
return v_originalMethod_338_;
}
}
v___jp_341_:
{
if (v___y_342_ == 0)
{
return v_originalMethod_338_;
}
else
{
uint8_t v___x_343_; 
v___x_343_ = 8;
return v___x_343_;
}
}
v___jp_344_:
{
uint8_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 23;
v___x_346_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_338_, v___x_345_);
if (v___x_346_ == 0)
{
v___y_342_ = v___x_346_;
goto v___jp_341_;
}
else
{
uint8_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 0;
v___x_348_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_339_, v___x_347_);
if (v___x_348_ == 0)
{
v___y_342_ = v___x_346_;
goto v___jp_341_;
}
else
{
return v_originalMethod_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_352_, lean_object* v_responseVersion_353_, lean_object* v_x_354_){
_start:
{
uint8_t v_originalMethod_boxed_355_; uint8_t v_responseVersion_boxed_356_; uint8_t v_res_357_; lean_object* v_r_358_; 
v_originalMethod_boxed_355_ = lean_unbox(v_originalMethod_352_);
v_responseVersion_boxed_356_ = lean_unbox(v_responseVersion_353_);
v_res_357_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_355_, v_responseVersion_boxed_356_, v_x_354_);
lean_dec(v_x_354_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_359_ = l_Std_Http_Header_Name_transferEncoding;
v___x_360_ = l_Std_Http_Header_Name_keepAlive;
v___x_361_ = l_Std_Http_Header_Name_connection;
v___x_362_ = lean_unsigned_to_nat(3u);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_362_);
v___x_364_ = lean_array_push(v___x_363_, v___x_361_);
v___x_365_ = lean_array_push(v___x_364_, v___x_360_);
v___x_366_ = lean_array_push(v___x_365_, v___x_359_);
return v___x_366_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object* v___x_368_, lean_object* v___x_369_, size_t v_sz_370_, size_t v_i_371_, lean_object* v_bs_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_lt(v_i_371_, v_sz_370_);
if (v___x_373_ == 0)
{
return v_bs_372_;
}
else
{
lean_object* v_entries_374_; lean_object* v___x_375_; lean_object* v_bs_x27_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_snd_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; 
v_entries_374_ = lean_ctor_get(v___x_368_, 0);
v___x_375_ = lean_unsigned_to_nat(0u);
v_bs_x27_376_ = lean_array_uset(v_bs_372_, v_i_371_, v___x_375_);
v___x_377_ = lean_usize_to_nat(v_i_371_);
v___x_378_ = lean_array_fget_borrowed(v___x_369_, v___x_377_);
lean_dec(v___x_377_);
v___x_379_ = lean_array_fget_borrowed(v_entries_374_, v___x_378_);
v_snd_380_ = lean_ctor_get(v___x_379_, 1);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_add(v_i_371_, v___x_381_);
lean_inc(v_snd_380_);
v___x_383_ = lean_array_uset(v_bs_x27_376_, v_i_371_, v_snd_380_);
v_i_371_ = v___x_382_;
v_bs_372_ = v___x_383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_bs_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_391_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v___x_385_, v___x_386_, v_sz_boxed_390_, v_i_boxed_391_, v_bs_389_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_385_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_393_, size_t v_i_394_, size_t v_stop_395_, lean_object* v_b_396_){
_start:
{
lean_object* v___y_398_; uint8_t v___x_402_; 
v___x_402_ = lean_usize_dec_eq(v_i_394_, v_stop_395_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_array_uget_borrowed(v_as_393_, v_i_394_);
lean_inc(v___x_403_);
v___x_404_ = l_Std_Http_Header_Name_ofString_x3f(v___x_403_);
if (lean_obj_tag(v___x_404_) == 0)
{
v___y_398_ = v_b_396_;
goto v___jp_397_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_406_; 
v_val_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v___x_404_, 1);
v___x_406_ = lean_array_push(v_b_396_, v_val_405_);
v___y_398_ = v___x_406_;
goto v___jp_397_;
}
}
else
{
return v_b_396_;
}
v___jp_397_:
{
size_t v___x_399_; size_t v___x_400_; 
v___x_399_ = ((size_t)1ULL);
v___x_400_ = lean_usize_add(v_i_394_, v___x_399_);
v_i_394_ = v___x_400_;
v_b_396_ = v___y_398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_407_, lean_object* v_i_408_, lean_object* v_stop_409_, lean_object* v_b_410_){
_start:
{
size_t v_i_boxed_411_; size_t v_stop_boxed_412_; lean_object* v_res_413_; 
v_i_boxed_411_ = lean_unbox_usize(v_i_408_);
lean_dec(v_i_408_);
v_stop_boxed_412_ = lean_unbox_usize(v_stop_409_);
lean_dec(v_stop_409_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_407_, v_i_boxed_411_, v_stop_boxed_412_, v_b_410_);
lean_dec_ref(v_as_407_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object* v_as_414_, size_t v_i_415_, size_t v_stop_416_, lean_object* v_b_417_){
_start:
{
lean_object* v___y_419_; uint8_t v___x_423_; 
v___x_423_ = lean_usize_dec_eq(v_i_415_, v_stop_416_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_array_uget_borrowed(v_as_414_, v_i_415_);
lean_inc(v___x_424_);
v___x_425_ = l_Std_Http_Header_Connection_parse(v___x_424_);
if (lean_obj_tag(v___x_425_) == 0)
{
v___y_419_ = v_b_417_;
goto v___jp_418_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_val_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v___x_425_, 1);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_array_get_size(v_val_426_);
v___x_429_ = lean_nat_dec_lt(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_dec(v_val_426_);
v___y_419_ = v_b_417_;
goto v___jp_418_;
}
else
{
uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_le(v___x_428_, v___x_428_);
if (v___x_430_ == 0)
{
if (v___x_429_ == 0)
{
lean_dec(v_val_426_);
v___y_419_ = v_b_417_;
goto v___jp_418_;
}
else
{
size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((size_t)0ULL);
v___x_432_ = lean_usize_of_nat(v___x_428_);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_426_, v___x_431_, v___x_432_, v_b_417_);
lean_dec(v_val_426_);
v___y_419_ = v___x_433_;
goto v___jp_418_;
}
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((size_t)0ULL);
v___x_435_ = lean_usize_of_nat(v___x_428_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_426_, v___x_434_, v___x_435_, v_b_417_);
lean_dec(v_val_426_);
v___y_419_ = v___x_436_;
goto v___jp_418_;
}
}
}
}
else
{
return v_b_417_;
}
v___jp_418_:
{
size_t v___x_420_; size_t v___x_421_; 
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_add(v_i_415_, v___x_420_);
v_i_415_ = v___x_421_;
v_b_417_ = v___y_419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object* v_as_437_, lean_object* v_i_438_, lean_object* v_stop_439_, lean_object* v_b_440_){
_start:
{
size_t v_i_boxed_441_; size_t v_stop_boxed_442_; lean_object* v_res_443_; 
v_i_boxed_441_ = lean_unbox_usize(v_i_438_);
lean_dec(v_i_438_);
v_stop_boxed_442_ = lean_unbox_usize(v_stop_439_);
lean_dec(v_stop_439_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v_as_437_, v_i_boxed_441_, v_stop_boxed_442_, v_b_440_);
lean_dec_ref(v_as_437_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object* v_a_444_, lean_object* v_x_445_){
_start:
{
lean_object* v_key_446_; lean_object* v_value_447_; lean_object* v_tail_448_; uint8_t v___x_449_; 
v_key_446_ = lean_ctor_get(v_x_445_, 0);
v_value_447_ = lean_ctor_get(v_x_445_, 1);
v_tail_448_ = lean_ctor_get(v_x_445_, 2);
v___x_449_ = lean_string_dec_eq(v_key_446_, v_a_444_);
if (v___x_449_ == 0)
{
v_x_445_ = v_tail_448_;
goto _start;
}
else
{
lean_inc(v_value_447_);
return v_value_447_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_451_, v_x_452_);
lean_dec(v_x_452_);
lean_dec_ref(v_a_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object* v_m_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_buckets_456_; lean_object* v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v_fold_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_buckets_456_ = lean_ctor_get(v_m_454_, 1);
v___x_457_ = lean_array_get_size(v_buckets_456_);
v___x_458_ = lean_string_hash(v_a_455_);
v___x_459_ = 32ULL;
v___x_460_ = lean_uint64_shift_right(v___x_458_, v___x_459_);
v_fold_461_ = lean_uint64_xor(v___x_458_, v___x_460_);
v___x_462_ = 16ULL;
v___x_463_ = lean_uint64_shift_right(v_fold_461_, v___x_462_);
v___x_464_ = lean_uint64_xor(v_fold_461_, v___x_463_);
v___x_465_ = lean_uint64_to_usize(v___x_464_);
v___x_466_ = lean_usize_of_nat(v___x_457_);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_sub(v___x_466_, v___x_467_);
v___x_469_ = lean_usize_land(v___x_465_, v___x_468_);
v___x_470_ = lean_array_uget_borrowed(v_buckets_456_, v___x_469_);
v___x_471_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_455_, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object* v_m_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_472_, v_a_473_);
lean_dec_ref(v_a_473_);
lean_dec_ref(v_m_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___f_481_; lean_object* v___f_482_; uint8_t v___x_483_; 
v___x_480_ = l_Std_Http_Header_Name_connection;
v___f_481_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_482_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_483_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_481_, v___f_482_, v___x_480_, v_headers_479_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2));
return v___x_484_;
}
else
{
lean_object* v_indexes_485_; lean_object* v___x_486_; size_t v_sz_487_; size_t v___x_488_; lean_object* v_entries_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_indexes_485_ = lean_ctor_get(v_headers_479_, 1);
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_485_, v___x_480_);
v_sz_487_ = lean_array_size(v___x_486_);
v___x_488_ = ((size_t)0ULL);
lean_inc(v___x_486_);
v_entries_489_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_headers_479_, v___x_486_, v_sz_487_, v___x_488_, v___x_486_);
lean_dec(v___x_486_);
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__2));
v___x_492_ = lean_array_get_size(v_entries_489_);
v___x_493_ = lean_nat_dec_lt(v___x_490_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec_ref(v_entries_489_);
return v___x_491_;
}
else
{
uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_le(v___x_492_, v___x_492_);
if (v___x_494_ == 0)
{
if (v___x_493_ == 0)
{
lean_dec_ref(v_entries_489_);
return v___x_491_;
}
else
{
size_t v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_usize_of_nat(v___x_492_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v_entries_489_, v___x_488_, v___x_495_, v___x_491_);
lean_dec_ref(v_entries_489_);
return v___x_496_;
}
}
else
{
size_t v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_usize_of_nat(v___x_492_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v_entries_489_, v___x_488_, v___x_497_, v___x_491_);
lean_dec_ref(v_entries_489_);
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_499_);
lean_dec_ref(v_headers_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_00_u03b2_501_, lean_object* v_m_502_, lean_object* v_a_503_, lean_object* v_hma_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_502_, v_a_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_00_u03b2_506_, lean_object* v_m_507_, lean_object* v_a_508_, lean_object* v_hma_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_00_u03b2_506_, v_m_507_, v_a_508_, v_hma_509_);
lean_dec_ref(v_a_508_);
lean_dec_ref(v_m_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v___x_511_, lean_object* v___x_512_, lean_object* v_as_513_, size_t v_sz_514_, size_t v_i_515_, lean_object* v_bs_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v___x_511_, v___x_512_, v_sz_514_, v_i_515_, v_bs_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v_as_520_, lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_bs_523_){
_start:
{
size_t v_sz_boxed_524_; size_t v_i_boxed_525_; lean_object* v_res_526_; 
v_sz_boxed_524_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v___x_518_, v___x_519_, v_as_520_, v_sz_boxed_524_, v_i_boxed_525_, v_bs_523_);
lean_dec_ref(v_as_520_);
lean_dec_ref(v___x_519_);
lean_dec_ref(v___x_518_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_528_, v_x_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object* v_00_u03b2_532_, lean_object* v_a_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(v_00_u03b2_532_, v_a_533_, v_x_534_, v_x_535_);
lean_dec(v_x_534_);
lean_dec_ref(v_a_533_);
return v_res_536_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_mk_empty_array_with_capacity(v___x_538_);
v___x_540_ = lean_array_push(v___x_539_, v___x_537_);
return v___x_540_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_541_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_542_ = l_Std_Http_Header_Name_referer;
v___x_543_ = l_Std_Http_Header_Name_cookie;
v___x_544_ = l_Std_Http_Header_Name_authorization;
v___x_545_ = lean_unsigned_to_nat(3u);
v___x_546_ = lean_mk_empty_array_with_capacity(v___x_545_);
v___x_547_ = lean_array_push(v___x_546_, v___x_544_);
v___x_548_ = lean_array_push(v___x_547_, v___x_543_);
v___x_549_ = lean_array_push(v___x_548_, v___x_542_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_550_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_551_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_552_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_553_ = lean_unsigned_to_nat(2u);
v___x_554_ = lean_mk_empty_array_with_capacity(v___x_553_);
v___x_555_ = lean_array_push(v___x_554_, v___x_552_);
v___x_556_ = lean_array_push(v___x_555_, v___x_551_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_557_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_558_ = l_Std_Http_Header_Name_lastModified;
v___x_559_ = l_Std_Http_Header_Name_contentLocation;
v___x_560_ = l_Std_Http_Header_Name_contentLanguage;
v___x_561_ = l_Std_Http_Header_Name_contentEncoding;
v___x_562_ = l_Std_Http_Header_Name_contentLength;
v___x_563_ = l_Std_Http_Header_Name_contentType;
v___x_564_ = lean_unsigned_to_nat(6u);
v___x_565_ = lean_mk_empty_array_with_capacity(v___x_564_);
v___x_566_ = lean_array_push(v___x_565_, v___x_563_);
v___x_567_ = lean_array_push(v___x_566_, v___x_562_);
v___x_568_ = lean_array_push(v___x_567_, v___x_561_);
v___x_569_ = lean_array_push(v___x_568_, v___x_560_);
v___x_570_ = lean_array_push(v___x_569_, v___x_559_);
v___x_571_ = lean_array_push(v___x_570_, v___x_558_);
return v___x_571_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_572_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
v___x_576_ = lean_unsigned_to_nat(16u);
v___x_577_ = lean_mk_array(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__1);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__2);
v___x_582_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0));
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v_00_u03b2_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__3);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2___lam__0(lean_object* v_i_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
v___x_590_ = lean_array_push(v___x_589_, v_i_586_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
else
{
lean_object* v_val_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_val_592_ = lean_ctor_get(v_x_587_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v_x_587_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_val_592_);
lean_dec(v_x_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_array_push(v_val_592_, v_i_586_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2(lean_object* v_i_601_, lean_object* v_a_602_, lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_val_606_; lean_object* v___x_607_; 
v___x_604_ = lean_box(0);
v___x_605_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2___lam__0(v_i_601_, v___x_604_);
v_val_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_606_);
lean_dec(v___x_605_);
v___x_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_607_, 0, v_a_602_);
lean_ctor_set(v___x_607_, 1, v_val_606_);
lean_ctor_set(v___x_607_, 2, v_x_603_);
return v___x_607_;
}
else
{
lean_object* v_key_608_; lean_object* v_value_609_; lean_object* v_tail_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_625_; 
v_key_608_ = lean_ctor_get(v_x_603_, 0);
v_value_609_ = lean_ctor_get(v_x_603_, 1);
v_tail_610_ = lean_ctor_get(v_x_603_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_625_ == 0)
{
v___x_612_ = v_x_603_;
v_isShared_613_ = v_isSharedCheck_625_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_tail_610_);
lean_inc(v_value_609_);
lean_inc(v_key_608_);
lean_dec(v_x_603_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_625_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___x_614_; 
v___x_614_ = lean_string_dec_eq(v_key_608_, v_a_602_);
if (v___x_614_ == 0)
{
lean_object* v_tail_615_; lean_object* v___x_617_; 
v_tail_615_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2(v_i_601_, v_a_602_, v_tail_610_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 2, v_tail_615_);
v___x_617_ = v___x_612_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_key_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_value_609_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_tail_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_val_621_; lean_object* v___x_623_; 
lean_dec(v_key_608_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v_value_609_);
v___x_620_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2___lam__0(v_i_601_, v___x_619_);
v_val_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_val_621_);
lean_dec(v___x_620_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v_val_621_);
lean_ctor_set(v___x_612_, 0, v_a_602_);
v___x_623_ = v___x_612_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_602_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_val_621_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_tail_610_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(lean_object* v_a_626_, lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
else
{
lean_object* v_key_629_; lean_object* v_tail_630_; uint8_t v___x_631_; 
v_key_629_ = lean_ctor_get(v_x_627_, 0);
v_tail_630_ = lean_ctor_get(v_x_627_, 2);
v___x_631_ = lean_string_dec_eq(v_key_629_, v_a_626_);
if (v___x_631_ == 0)
{
v_x_627_ = v_tail_630_;
goto _start;
}
else
{
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg___boxed(lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_633_, v_x_634_);
lean_dec(v_x_634_);
lean_dec_ref(v_a_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_638_) == 0)
{
return v_x_637_;
}
else
{
lean_object* v_key_639_; lean_object* v_value_640_; lean_object* v_tail_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_664_; 
v_key_639_ = lean_ctor_get(v_x_638_, 0);
v_value_640_ = lean_ctor_get(v_x_638_, 1);
v_tail_641_ = lean_ctor_get(v_x_638_, 2);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_638_);
if (v_isSharedCheck_664_ == 0)
{
v___x_643_ = v_x_638_;
v_isShared_644_ = v_isSharedCheck_664_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_tail_641_);
lean_inc(v_value_640_);
lean_inc(v_key_639_);
lean_dec(v_x_638_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_664_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; uint64_t v___x_648_; uint64_t v_fold_649_; uint64_t v___x_650_; uint64_t v___x_651_; uint64_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_645_ = lean_array_get_size(v_x_637_);
v___x_646_ = lean_string_hash(v_key_639_);
v___x_647_ = 32ULL;
v___x_648_ = lean_uint64_shift_right(v___x_646_, v___x_647_);
v_fold_649_ = lean_uint64_xor(v___x_646_, v___x_648_);
v___x_650_ = 16ULL;
v___x_651_ = lean_uint64_shift_right(v_fold_649_, v___x_650_);
v___x_652_ = lean_uint64_xor(v_fold_649_, v___x_651_);
v___x_653_ = lean_uint64_to_usize(v___x_652_);
v___x_654_ = lean_usize_of_nat(v___x_645_);
v___x_655_ = ((size_t)1ULL);
v___x_656_ = lean_usize_sub(v___x_654_, v___x_655_);
v___x_657_ = lean_usize_land(v___x_653_, v___x_656_);
v___x_658_ = lean_array_uget_borrowed(v_x_637_, v___x_657_);
lean_inc(v___x_658_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 2, v___x_658_);
v___x_660_ = v___x_643_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_key_639_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_value_640_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v___x_658_);
v___x_660_ = v_reuseFailAlloc_663_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; 
v___x_661_ = lean_array_uset(v_x_637_, v___x_657_, v___x_660_);
v_x_637_ = v___x_661_;
v_x_638_ = v_tail_641_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3___redArg(lean_object* v_i_665_, lean_object* v_source_666_, lean_object* v_target_667_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_array_get_size(v_source_666_);
v___x_669_ = lean_nat_dec_lt(v_i_665_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec_ref(v_source_666_);
lean_dec(v_i_665_);
return v_target_667_;
}
else
{
lean_object* v_es_670_; lean_object* v___x_671_; lean_object* v_source_672_; lean_object* v_target_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_es_670_ = lean_array_fget(v_source_666_, v_i_665_);
v___x_671_ = lean_box(0);
v_source_672_ = lean_array_fset(v_source_666_, v_i_665_, v___x_671_);
v_target_673_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6___redArg(v_target_667_, v_es_670_);
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_add(v_i_665_, v___x_674_);
lean_dec(v_i_665_);
v_i_665_ = v___x_675_;
v_source_666_ = v_source_672_;
v_target_667_ = v_target_673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1___redArg(lean_object* v_data_677_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_nbuckets_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_678_ = lean_array_get_size(v_data_677_);
v___x_679_ = lean_unsigned_to_nat(2u);
v_nbuckets_680_ = lean_nat_mul(v___x_678_, v___x_679_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_box(0);
v___x_683_ = lean_mk_array(v_nbuckets_680_, v___x_682_);
v___x_684_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3___redArg(v___x_681_, v_data_677_, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_i_685_, lean_object* v_m_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_size_688_; lean_object* v_buckets_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_739_; 
v_size_688_ = lean_ctor_get(v_m_686_, 0);
v_buckets_689_ = lean_ctor_get(v_m_686_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_m_686_);
if (v_isSharedCheck_739_ == 0)
{
v___x_691_ = v_m_686_;
v_isShared_692_ = v_isSharedCheck_739_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_buckets_689_);
lean_inc(v_size_688_);
lean_dec(v_m_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_739_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v___x_696_; uint64_t v_fold_697_; uint64_t v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v_bkt_706_; uint8_t v___x_707_; 
v___x_693_ = lean_array_get_size(v_buckets_689_);
v___x_694_ = lean_string_hash(v_a_687_);
v___x_695_ = 32ULL;
v___x_696_ = lean_uint64_shift_right(v___x_694_, v___x_695_);
v_fold_697_ = lean_uint64_xor(v___x_694_, v___x_696_);
v___x_698_ = 16ULL;
v___x_699_ = lean_uint64_shift_right(v_fold_697_, v___x_698_);
v___x_700_ = lean_uint64_xor(v_fold_697_, v___x_699_);
v___x_701_ = lean_uint64_to_usize(v___x_700_);
v___x_702_ = lean_usize_of_nat(v___x_693_);
v___x_703_ = ((size_t)1ULL);
v___x_704_ = lean_usize_sub(v___x_702_, v___x_703_);
v___x_705_ = lean_usize_land(v___x_701_, v___x_704_);
v_bkt_706_ = lean_array_uget_borrowed(v_buckets_689_, v___x_705_);
v___x_707_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_687_, v_bkt_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_size_x27_711_; lean_object* v___x_712_; lean_object* v_buckets_x27_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_mk_empty_array_with_capacity(v___x_708_);
v___x_710_ = lean_array_push(v___x_709_, v_i_685_);
v_size_x27_711_ = lean_nat_add(v_size_688_, v___x_708_);
lean_dec(v_size_688_);
lean_inc(v_bkt_706_);
v___x_712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_712_, 0, v_a_687_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v_bkt_706_);
v_buckets_x27_713_ = lean_array_uset(v_buckets_689_, v___x_705_, v___x_712_);
v___x_714_ = lean_unsigned_to_nat(4u);
v___x_715_ = lean_nat_mul(v_size_x27_711_, v___x_714_);
v___x_716_ = lean_unsigned_to_nat(3u);
v___x_717_ = lean_nat_div(v___x_715_, v___x_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_array_get_size(v_buckets_x27_713_);
v___x_719_ = lean_nat_dec_le(v___x_717_, v___x_718_);
lean_dec(v___x_717_);
if (v___x_719_ == 0)
{
lean_object* v_val_720_; lean_object* v___x_722_; 
v_val_720_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1___redArg(v_buckets_x27_713_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_val_720_);
lean_ctor_set(v___x_691_, 0, v_size_x27_711_);
v___x_722_ = v___x_691_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_size_x27_711_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_val_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v___x_725_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_buckets_x27_713_);
lean_ctor_set(v___x_691_, 0, v_size_x27_711_);
v___x_725_ = v___x_691_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_size_x27_711_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_buckets_x27_713_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v___x_727_; lean_object* v_buckets_x27_728_; lean_object* v_bkt_x27_729_; lean_object* v___y_731_; uint8_t v___x_736_; 
lean_inc(v_bkt_706_);
v___x_727_ = lean_box(0);
v_buckets_x27_728_ = lean_array_uset(v_buckets_689_, v___x_705_, v___x_727_);
lean_inc_ref(v_a_687_);
v_bkt_x27_729_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__2(v_i_685_, v_a_687_, v_bkt_706_);
v___x_736_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_687_, v_bkt_x27_729_);
lean_dec_ref(v_a_687_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_sub(v_size_688_, v___x_737_);
lean_dec(v_size_688_);
v___y_731_ = v___x_738_;
goto v___jp_730_;
}
else
{
v___y_731_ = v_size_688_;
goto v___jp_730_;
}
v___jp_730_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_array_uset(v_buckets_x27_728_, v___x_705_, v_bkt_x27_729_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_732_);
lean_ctor_set(v___x_691_, 0, v___y_731_);
v___x_734_ = v___x_691_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___y_731_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4(lean_object* v_a_740_, lean_object* v_as_741_, size_t v_i_742_, size_t v_stop_743_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = lean_usize_dec_eq(v_i_742_, v_stop_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_array_uget_borrowed(v_as_741_, v_i_742_);
v___x_746_ = lean_string_dec_eq(v_a_740_, v___x_745_);
if (v___x_746_ == 0)
{
size_t v___x_747_; size_t v___x_748_; 
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_add(v_i_742_, v___x_747_);
v_i_742_ = v___x_748_;
goto _start;
}
else
{
return v___x_746_;
}
}
else
{
uint8_t v___x_750_; 
v___x_750_ = 0;
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4___boxed(lean_object* v_a_751_, lean_object* v_as_752_, lean_object* v_i_753_, lean_object* v_stop_754_){
_start:
{
size_t v_i_boxed_755_; size_t v_stop_boxed_756_; uint8_t v_res_757_; lean_object* v_r_758_; 
v_i_boxed_755_ = lean_unbox_usize(v_i_753_);
lean_dec(v_i_753_);
v_stop_boxed_756_ = lean_unbox_usize(v_stop_754_);
lean_dec(v_stop_754_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4(v_a_751_, v_as_752_, v_i_boxed_755_, v_stop_boxed_756_);
lean_dec_ref(v_as_752_);
lean_dec_ref(v_a_751_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v_as_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_array_get_size(v_as_759_);
v___x_763_ = lean_nat_dec_lt(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
return v___x_763_;
}
else
{
if (v___x_763_ == 0)
{
return v___x_763_;
}
else
{
size_t v___x_764_; size_t v___x_765_; uint8_t v___x_766_; 
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_762_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__4(v_a_760_, v_as_759_, v___x_764_, v___x_765_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object* v_as_767_, lean_object* v_a_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v_as_767_, v_a_768_);
lean_dec_ref(v_a_768_);
lean_dec_ref(v_as_767_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object* v___y_771_, lean_object* v_as_772_, size_t v_i_773_, size_t v_stop_774_, lean_object* v_b_775_){
_start:
{
lean_object* v___y_777_; uint8_t v___x_781_; 
v___x_781_ = lean_usize_dec_eq(v_i_773_, v_stop_774_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v_fst_783_; uint8_t v___x_797_; 
v___x_782_ = lean_array_uget_borrowed(v_as_772_, v_i_773_);
v_fst_783_ = lean_ctor_get(v___x_782_, 0);
v___x_797_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_771_, v_fst_783_);
if (v___x_797_ == 0)
{
goto v___jp_784_;
}
else
{
if (v___x_781_ == 0)
{
v___y_777_ = v_b_775_;
goto v___jp_776_;
}
else
{
goto v___jp_784_;
}
}
v___jp_784_:
{
lean_object* v_entries_785_; lean_object* v_indexes_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_796_; 
v_entries_785_ = lean_ctor_get(v_b_775_, 0);
v_indexes_786_ = lean_ctor_get(v_b_775_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_b_775_);
if (v_isSharedCheck_796_ == 0)
{
v___x_788_ = v_b_775_;
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_indexes_786_);
lean_inc(v_entries_785_);
lean_dec(v_b_775_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_i_790_; lean_object* v_entries_791_; lean_object* v_indexes_792_; lean_object* v___x_794_; 
v_i_790_ = lean_array_get_size(v_entries_785_);
lean_inc(v___x_782_);
v_entries_791_ = lean_array_push(v_entries_785_, v___x_782_);
lean_inc(v_fst_783_);
v_indexes_792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_i_790_, v_indexes_786_, v_fst_783_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v_indexes_792_);
lean_ctor_set(v___x_788_, 0, v_entries_791_);
v___x_794_ = v___x_788_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_entries_791_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_indexes_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v___y_777_ = v___x_794_;
goto v___jp_776_;
}
}
}
}
else
{
return v_b_775_;
}
v___jp_776_:
{
size_t v___x_778_; size_t v___x_779_; 
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_773_, v___x_778_);
v_i_773_ = v___x_779_;
v_b_775_ = v___y_777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object* v___y_798_, lean_object* v_as_799_, lean_object* v_i_800_, lean_object* v_stop_801_, lean_object* v_b_802_){
_start:
{
size_t v_i_boxed_803_; size_t v_stop_boxed_804_; lean_object* v_res_805_; 
v_i_boxed_803_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_stop_boxed_804_ = lean_unbox_usize(v_stop_801_);
lean_dec(v_stop_801_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_798_, v_as_799_, v_i_boxed_803_, v_stop_boxed_804_, v_b_802_);
lean_dec_ref(v_as_799_);
lean_dec_ref(v___y_798_);
return v_res_805_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0(void){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_box(0));
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_807_, uint8_t v_isCrossOrigin_808_, uint8_t v_methodChanged_809_){
_start:
{
lean_object* v___y_811_; lean_object* v___y_825_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_afterConnection_832_; 
v___x_830_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_831_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_807_);
v_afterConnection_832_ = l_Array_append___redArg(v___x_830_, v___x_831_);
lean_dec_ref(v___x_831_);
if (v_isCrossOrigin_808_ == 0)
{
v___y_825_ = v_afterConnection_832_;
goto v___jp_824_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_833_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_834_ = l_Array_append___redArg(v_afterConnection_832_, v___x_833_);
v___x_835_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_836_ = l_Array_append___redArg(v___x_834_, v___x_835_);
v___x_837_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_838_ = l_Array_append___redArg(v___x_836_, v___x_837_);
v___y_825_ = v___x_838_;
goto v___jp_824_;
}
v___jp_810_:
{
lean_object* v_entries_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_entries_812_ = lean_ctor_get(v_headers_807_, 0);
v___x_813_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_array_get_size(v_entries_812_);
v___x_816_ = lean_nat_dec_lt(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_dec_ref(v___y_811_);
return v___x_813_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = lean_nat_dec_le(v___x_815_, v___x_815_);
if (v___x_817_ == 0)
{
if (v___x_816_ == 0)
{
lean_dec_ref(v___y_811_);
return v___x_813_;
}
else
{
size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((size_t)0ULL);
v___x_819_ = lean_usize_of_nat(v___x_815_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_811_, v_entries_812_, v___x_818_, v___x_819_, v___x_813_);
lean_dec_ref(v___y_811_);
return v___x_820_;
}
}
else
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((size_t)0ULL);
v___x_822_ = lean_usize_of_nat(v___x_815_);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_811_, v_entries_812_, v___x_821_, v___x_822_, v___x_813_);
lean_dec_ref(v___y_811_);
return v___x_823_;
}
}
}
v___jp_824_:
{
if (v_methodChanged_809_ == 0)
{
v___y_811_ = v___y_825_;
goto v___jp_810_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_827_ = l_Array_append___redArg(v___y_825_, v___x_826_);
v___x_828_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_829_ = l_Array_append___redArg(v___x_827_, v___x_828_);
v___y_811_ = v___x_829_;
goto v___jp_810_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_839_, lean_object* v_isCrossOrigin_840_, lean_object* v_methodChanged_841_){
_start:
{
uint8_t v_isCrossOrigin_boxed_842_; uint8_t v_methodChanged_boxed_843_; lean_object* v_res_844_; 
v_isCrossOrigin_boxed_842_ = lean_unbox(v_isCrossOrigin_840_);
v_methodChanged_boxed_843_ = lean_unbox(v_methodChanged_841_);
v_res_844_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_839_, v_isCrossOrigin_boxed_842_, v_methodChanged_boxed_843_);
lean_dec_ref(v_headers_839_);
return v_res_844_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_00_u03b2_845_, lean_object* v_a_846_, lean_object* v_x_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_846_, v_x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_00_u03b2_849_, lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_00_u03b2_849_, v_a_850_, v_x_851_);
lean_dec(v_x_851_);
lean_dec_ref(v_a_850_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1(lean_object* v_00_u03b2_854_, lean_object* v_data_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1___redArg(v_data_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_857_, lean_object* v_i_858_, lean_object* v_source_859_, lean_object* v_target_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3___redArg(v_i_858_, v_source_859_, v_target_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__1_spec__3_spec__6___redArg(v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(lean_object* v_m_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_buckets_868_; lean_object* v___x_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v_fold_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_buckets_868_ = lean_ctor_get(v_m_866_, 1);
v___x_869_ = lean_array_get_size(v_buckets_868_);
v___x_870_ = lean_string_hash(v_a_867_);
v___x_871_ = 32ULL;
v___x_872_ = lean_uint64_shift_right(v___x_870_, v___x_871_);
v_fold_873_ = lean_uint64_xor(v___x_870_, v___x_872_);
v___x_874_ = 16ULL;
v___x_875_ = lean_uint64_shift_right(v_fold_873_, v___x_874_);
v___x_876_ = lean_uint64_xor(v_fold_873_, v___x_875_);
v___x_877_ = lean_uint64_to_usize(v___x_876_);
v___x_878_ = lean_usize_of_nat(v___x_869_);
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_sub(v___x_878_, v___x_879_);
v___x_881_ = lean_usize_land(v___x_877_, v___x_880_);
v___x_882_ = lean_array_uget_borrowed(v_buckets_868_, v___x_881_);
v___x_883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___redArg(v_a_867_, v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg___boxed(lean_object* v_m_884_, lean_object* v_a_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_m_884_, v_a_885_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_m_884_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_888_, lean_object* v_origin_889_){
_start:
{
lean_object* v_entries_890_; lean_object* v_indexes_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v_entries_890_ = lean_ctor_get(v_headers_888_, 0);
v_indexes_891_ = lean_ctor_get(v_headers_888_, 1);
v___x_892_ = l_Std_Http_Header_Name_host;
v___x_893_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_indexes_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_dec_ref(v_origin_889_);
return v_headers_888_;
}
else
{
lean_object* v___f_894_; lean_object* v___f_895_; uint8_t v___x_896_; 
v___f_894_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_895_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_896_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_894_, v___f_895_, v___x_892_, v_headers_888_);
if (v___x_896_ == 0)
{
lean_dec_ref(v_origin_889_);
return v_headers_888_;
}
else
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_912_; 
lean_inc_ref(v_indexes_891_);
lean_inc_ref(v_entries_890_);
v_isSharedCheck_912_ = !lean_is_exclusive(v_headers_888_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; lean_object* v_unused_914_; 
v_unused_913_ = lean_ctor_get(v_headers_888_, 1);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_headers_888_, 0);
lean_dec(v_unused_914_);
v___x_898_ = v_headers_888_;
v_isShared_899_ = v_isSharedCheck_912_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_headers_888_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_912_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_idxs_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_lastIdx_906_; lean_object* v___x_907_; lean_object* v_entries_908_; lean_object* v___x_910_; 
v___x_900_ = l_Std_Http_URI_Origin_hostHeader(v_origin_889_);
v___x_901_ = l_Std_Http_Header_Value_ofString_x21(v___x_900_);
v_idxs_902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_891_, v___x_892_);
v___x_903_ = lean_array_get_size(v_idxs_902_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_sub(v___x_903_, v___x_904_);
v_lastIdx_906_ = lean_array_fget(v_idxs_902_, v___x_905_);
lean_dec(v___x_905_);
lean_dec(v_idxs_902_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_892_);
lean_ctor_set(v___x_907_, 1, v___x_901_);
v_entries_908_ = lean_array_fset(v_entries_890_, v_lastIdx_906_, v___x_907_);
lean_dec(v_lastIdx_906_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v_entries_908_);
v___x_910_ = v___x_898_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_entries_908_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_indexes_891_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(lean_object* v_00_u03b2_915_, lean_object* v_m_916_, lean_object* v_a_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___redArg(v_m_916_, v_a_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___boxed(lean_object* v_00_u03b2_919_, lean_object* v_m_920_, lean_object* v_a_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_00_u03b2_919_, v_m_920_, v_a_921_);
lean_dec_ref(v_a_921_);
lean_dec_ref(v_m_920_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_924_){
_start:
{
switch(lean_obj_tag(v_x_924_))
{
case 0:
{
lean_object* v_query_925_; 
v_query_925_ = lean_ctor_get(v_x_924_, 1);
lean_inc(v_query_925_);
return v_query_925_;
}
case 1:
{
lean_object* v_uri_926_; lean_object* v_query_927_; 
v_uri_926_ = lean_ctor_get(v_x_924_, 0);
v_query_927_ = lean_ctor_get(v_uri_926_, 3);
lean_inc(v_query_927_);
return v_query_927_;
}
default: 
{
lean_object* v___x_928_; 
v___x_928_ = lean_box(0);
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_929_);
lean_dec(v_x_929_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_931_, uint8_t v_isCrossOrigin_932_, lean_object* v_basePath_933_, lean_object* v_baseQuery_934_, lean_object* v_currentScheme_935_){
_start:
{
lean_object* v___y_937_; lean_object* v___y_938_; 
if (lean_obj_tag(v_ref_931_) == 0)
{
lean_object* v_uri_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v_currentScheme_935_);
lean_dec(v_baseQuery_934_);
lean_dec_ref(v_basePath_933_);
v_uri_941_ = lean_ctor_get(v_ref_931_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_ref_931_);
if (v_isSharedCheck_983_ == 0)
{
v___x_943_ = v_ref_931_;
v_isShared_944_ = v_isSharedCheck_983_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_uri_941_);
lean_dec(v_ref_931_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_983_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_scheme_945_; lean_object* v_authority_946_; lean_object* v_path_947_; lean_object* v_query_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_981_; 
v_scheme_945_ = lean_ctor_get(v_uri_941_, 0);
v_authority_946_ = lean_ctor_get(v_uri_941_, 1);
v_path_947_ = lean_ctor_get(v_uri_941_, 2);
v_query_948_ = lean_ctor_get(v_uri_941_, 3);
v_isSharedCheck_981_ = !lean_is_exclusive(v_uri_941_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v_uri_941_, 4);
lean_dec(v_unused_982_);
v___x_950_ = v_uri_941_;
v_isShared_951_ = v_isSharedCheck_981_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_query_948_);
lean_inc(v_path_947_);
lean_inc(v_authority_946_);
lean_inc(v_scheme_945_);
lean_dec(v_uri_941_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_981_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___y_953_; 
if (lean_obj_tag(v_authority_946_) == 0)
{
v___y_953_ = v_authority_946_;
goto v___jp_952_;
}
else
{
lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_980_; 
v_val_962_ = lean_ctor_get(v_authority_946_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v_authority_946_);
if (v_isSharedCheck_980_ == 0)
{
v___x_964_ = v_authority_946_;
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v_authority_946_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_host_966_; lean_object* v_port_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_978_; 
v_host_966_ = lean_ctor_get(v_val_962_, 1);
v_port_967_ = lean_ctor_get(v_val_962_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v_val_962_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v_val_962_, 0);
lean_dec(v_unused_979_);
v___x_969_ = v_val_962_;
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_port_967_);
lean_inc(v_host_966_);
lean_dec(v_val_962_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_box(0);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_host_966_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_port_967_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_973_);
v___x_975_ = v___x_964_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
v___y_953_ = v___x_975_;
goto v___jp_952_;
}
}
}
}
}
v___jp_952_:
{
if (v_isCrossOrigin_932_ == 0)
{
lean_object* v___x_954_; 
lean_dec(v___y_953_);
lean_del_object(v___x_950_);
lean_dec_ref(v_scheme_945_);
lean_del_object(v___x_943_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_path_947_);
lean_ctor_set(v___x_954_, 1, v_query_948_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v_stripped_957_; 
v___x_955_ = lean_box(0);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v___x_955_);
lean_ctor_set(v___x_950_, 1, v___y_953_);
v_stripped_957_ = v___x_950_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_scheme_945_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___y_953_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_path_947_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_query_948_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v___x_955_);
v_stripped_957_ = v_reuseFailAlloc_961_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_959_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 1);
lean_ctor_set(v___x_943_, 0, v_stripped_957_);
v___x_959_ = v___x_943_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_stripped_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
}
else
{
lean_object* v_ref_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1025_; 
v_ref_984_ = lean_ctor_get(v_ref_931_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_ref_931_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_986_ = v_ref_931_;
v_isShared_987_ = v_isSharedCheck_1025_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_ref_984_);
lean_dec(v_ref_931_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1025_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_authority_988_; lean_object* v_path_989_; lean_object* v_query_990_; lean_object* v___y_992_; uint8_t v___y_993_; 
v_authority_988_ = lean_ctor_get(v_ref_984_, 0);
lean_inc(v_authority_988_);
v_path_989_ = lean_ctor_get(v_ref_984_, 1);
lean_inc_ref(v_path_989_);
v_query_990_ = lean_ctor_get(v_ref_984_, 2);
lean_inc(v_query_990_);
lean_dec_ref(v_ref_984_);
if (lean_obj_tag(v_authority_988_) == 0)
{
uint8_t v___x_994_; lean_object* v___y_996_; 
lean_del_object(v___x_986_);
lean_dec_ref(v_currentScheme_935_);
v___x_994_ = l_Std_Http_URI_Path_isEmpty(v_path_989_);
if (v___x_994_ == 0)
{
uint8_t v_absolute_997_; 
v_absolute_997_ = lean_ctor_get_uint8(v_path_989_, sizeof(void*)*1);
if (v_absolute_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = l_Std_Http_URI_Path_parent(v_basePath_933_);
v___x_999_ = l_Std_Http_URI_Path_join(v___x_998_, v_path_989_);
lean_dec_ref(v_path_989_);
v___y_996_ = v___x_999_;
goto v___jp_995_;
}
else
{
lean_dec_ref(v_basePath_933_);
v___y_996_ = v_path_989_;
goto v___jp_995_;
}
}
else
{
lean_dec_ref(v_path_989_);
v___y_996_ = v_basePath_933_;
goto v___jp_995_;
}
v___jp_995_:
{
if (v___x_994_ == 0)
{
v___y_992_ = v___y_996_;
v___y_993_ = v___x_994_;
goto v___jp_991_;
}
else
{
if (lean_obj_tag(v_query_990_) == 0)
{
v___y_992_ = v___y_996_;
v___y_993_ = v___x_994_;
goto v___jp_991_;
}
else
{
lean_dec(v_baseQuery_934_);
v___y_937_ = v___y_996_;
v___y_938_ = v_query_990_;
goto v___jp_936_;
}
}
}
}
else
{
lean_dec(v_baseQuery_934_);
lean_dec_ref(v_basePath_933_);
if (v_isCrossOrigin_932_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec_ref_known(v_authority_988_, 1);
lean_del_object(v___x_986_);
lean_dec_ref(v_currentScheme_935_);
v___x_1000_ = l_Std_Http_URI_Path_normalize(v_path_989_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_query_990_);
return v___x_1001_;
}
else
{
lean_object* v_val_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1024_; 
v_val_1002_ = lean_ctor_get(v_authority_988_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_authority_988_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1004_ = v_authority_988_;
v_isShared_1005_ = v_isSharedCheck_1024_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_val_1002_);
lean_dec(v_authority_988_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1024_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_host_1006_; lean_object* v_port_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1022_; 
v_host_1006_ = lean_ctor_get(v_val_1002_, 1);
v_port_1007_ = lean_ctor_get(v_val_1002_, 2);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_val_1002_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_val_1002_, 0);
lean_dec(v_unused_1023_);
v___x_1009_ = v_val_1002_;
v_isShared_1010_ = v_isSharedCheck_1022_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_port_1007_);
lean_inc(v_host_1006_);
lean_dec(v_val_1002_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1022_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v_stripped_1013_; 
v___x_1011_ = lean_box(0);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1011_);
v_stripped_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_host_1006_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_port_1007_);
v_stripped_1013_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_stripped_1013_);
v___x_1015_ = v___x_1004_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_stripped_1013_);
v___x_1015_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v_af_1016_; lean_object* v___x_1018_; 
v_af_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_1016_, 0, v_currentScheme_935_);
lean_ctor_set(v_af_1016_, 1, v___x_1015_);
lean_ctor_set(v_af_1016_, 2, v_path_989_);
lean_ctor_set(v_af_1016_, 3, v_query_990_);
lean_ctor_set(v_af_1016_, 4, v___x_1011_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v_af_1016_);
v___x_1018_ = v___x_986_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_af_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
}
v___jp_991_:
{
if (v___y_993_ == 0)
{
lean_dec(v_baseQuery_934_);
v___y_937_ = v___y_992_;
v___y_938_ = v_query_990_;
goto v___jp_936_;
}
else
{
lean_dec(v_query_990_);
v___y_937_ = v___y_992_;
v___y_938_ = v_baseQuery_934_;
goto v___jp_936_;
}
}
}
}
v___jp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = l_Std_Http_URI_Path_normalize(v___y_937_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___y_938_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_1026_, lean_object* v_isCrossOrigin_1027_, lean_object* v_basePath_1028_, lean_object* v_baseQuery_1029_, lean_object* v_currentScheme_1030_){
_start:
{
uint8_t v_isCrossOrigin_boxed_1031_; lean_object* v_res_1032_; 
v_isCrossOrigin_boxed_1031_ = lean_unbox(v_isCrossOrigin_1027_);
v_res_1032_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_1026_, v_isCrossOrigin_boxed_1031_, v_basePath_1028_, v_baseQuery_1029_, v_currentScheme_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Std_Http_URI_Parser_parseURIReference(v___x_1036_, v___y_1037_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_pos_1039_; lean_object* v_array_1040_; lean_object* v_idx_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_pos_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_pos_1039_);
v_array_1040_ = lean_ctor_get(v_pos_1039_, 0);
v_idx_1041_ = lean_ctor_get(v_pos_1039_, 1);
v___x_1042_ = lean_byte_array_size(v_array_1040_);
v___x_1043_ = lean_nat_dec_lt(v_idx_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_dec(v_pos_1039_);
return v___x_1038_;
}
else
{
lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1051_; 
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; lean_object* v_unused_1053_; 
v_unused_1052_ = lean_ctor_get(v___x_1038_, 1);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v___x_1038_, 0);
lean_dec(v_unused_1053_);
v___x_1045_ = v___x_1038_;
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
else
{
lean_dec(v___x_1038_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
lean_ctor_set(v___x_1045_, 1, v___x_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_pos_1039_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
return v___x_1038_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_1066_, lean_object* v_request_1067_, uint8_t v_bodyReplayable_1068_, uint8_t v_onlySafeRedirects_1069_, uint8_t v_responseVersion_1070_, lean_object* v_status_1071_, lean_object* v_responseHeaders_1072_){
_start:
{
lean_object* v___y_1074_; lean_object* v___y_1075_; uint8_t v___y_1076_; lean_object* v___y_1077_; uint8_t v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1096_; uint8_t v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; uint8_t v___y_1100_; uint8_t v___y_1101_; uint8_t v___y_1102_; lean_object* v___y_1103_; uint8_t v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; uint8_t v___y_1112_; lean_object* v___y_1113_; uint8_t v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1119_; uint8_t v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; uint8_t v___y_1124_; uint8_t v___y_1125_; uint8_t v___y_1126_; lean_object* v___y_1127_; uint8_t v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; uint8_t v___y_1134_; lean_object* v___y_1135_; uint8_t v___y_1136_; uint8_t v___y_1137_; uint8_t v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; uint8_t v___y_1146_; uint8_t v___y_1147_; uint8_t v___y_1148_; uint8_t v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1152_; lean_object* v___y_1153_; uint8_t v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; uint8_t v___y_1157_; uint8_t v___y_1158_; uint8_t v___y_1159_; uint8_t v___y_1160_; lean_object* v___y_1164_; uint8_t v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1168_; lean_object* v___y_1169_; uint8_t v___y_1170_; uint8_t v___y_1171_; uint8_t v___y_1172_; uint8_t v___y_1173_; lean_object* v___y_1176_; lean_object* v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; uint8_t v___y_1181_; uint8_t v___y_1182_; uint8_t v___y_1183_; uint8_t v___y_1184_; uint8_t v___y_1185_; uint8_t v___y_1186_; lean_object* v___y_1188_; uint8_t v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; uint8_t v___y_1192_; lean_object* v___y_1193_; uint8_t v___y_1194_; uint8_t v___y_1195_; uint8_t v___y_1196_; lean_object* v___y_1199_; lean_object* v___y_1200_; uint8_t v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; uint8_t v___y_1204_; uint8_t v___y_1205_; uint8_t v___y_1206_; uint8_t v___y_1207_; uint8_t v___y_1208_; lean_object* v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; uint8_t v___y_1214_; lean_object* v___y_1215_; uint8_t v___y_1216_; uint8_t v___y_1217_; uint8_t v___y_1218_; uint8_t v___y_1219_; uint8_t v___y_1220_; uint16_t v___x_1223_; uint16_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1223_ = 300;
v___x_1224_ = l_Std_Http_Status_toCode(v_status_1071_);
v___x_1225_ = lean_uint16_dec_le(v___x_1223_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v_current_1066_);
v___x_1226_ = lean_box(0);
return v___x_1226_;
}
else
{
uint16_t v___x_1227_; uint8_t v___x_1228_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; uint8_t v___y_1233_; lean_object* v___y_1234_; uint8_t v___y_1235_; uint8_t v___y_1236_; uint8_t v___y_1237_; uint8_t v___y_1238_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; uint8_t v___y_1248_; uint8_t v___y_1249_; uint8_t v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; uint8_t v___y_1258_; uint8_t v___y_1259_; uint8_t v___y_1260_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v_scheme_1266_; lean_object* v___y_1267_; uint8_t v___y_1268_; uint8_t v___y_1269_; uint8_t v___y_1270_; uint8_t v___y_1275_; uint8_t v___y_1320_; 
v___x_1227_ = 400;
v___x_1228_ = lean_uint16_dec_lt(v___x_1224_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref(v_current_1066_);
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
else
{
uint8_t v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = 0;
v___x_1326_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_1070_, v___x_1325_);
if (v___x_1326_ == 0)
{
v___y_1320_ = v___x_1326_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = lean_box(15);
v___x_1328_ = l_Std_Http_instBEqStatus_beq(v_status_1071_, v___x_1327_);
if (v___x_1328_ == 0)
{
v___y_1320_ = v___x_1326_;
goto v___jp_1319_;
}
else
{
goto v___jp_1303_;
}
}
}
v___jp_1229_:
{
uint8_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = 8;
v___x_1240_ = l_Std_Http_instBEqMethod_beq(v___y_1237_, v___x_1239_);
if (v___x_1240_ == 0)
{
uint8_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = 9;
v___x_1242_ = l_Std_Http_instBEqMethod_beq(v___y_1237_, v___x_1241_);
v___y_1210_ = v___y_1230_;
v___y_1211_ = v___y_1238_;
v___y_1212_ = v___y_1231_;
v___y_1213_ = v___y_1232_;
v___y_1214_ = v___y_1233_;
v___y_1215_ = v___y_1234_;
v___y_1216_ = v___y_1235_;
v___y_1217_ = v___y_1236_;
v___y_1218_ = v___x_1239_;
v___y_1219_ = v___y_1237_;
v___y_1220_ = v___x_1242_;
goto v___jp_1209_;
}
else
{
v___y_1210_ = v___y_1230_;
v___y_1211_ = v___y_1238_;
v___y_1212_ = v___y_1231_;
v___y_1213_ = v___y_1232_;
v___y_1214_ = v___y_1233_;
v___y_1215_ = v___y_1234_;
v___y_1216_ = v___y_1235_;
v___y_1217_ = v___y_1236_;
v___y_1218_ = v___x_1239_;
v___y_1219_ = v___y_1237_;
v___y_1220_ = v___x_1228_;
goto v___jp_1209_;
}
}
v___jp_1243_:
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Std_Http_instBEqMethod_beq(v___y_1249_, v___y_1250_);
if (v___x_1252_ == 0)
{
v___y_1230_ = v___y_1244_;
v___y_1231_ = v___y_1245_;
v___y_1232_ = v___y_1246_;
v___y_1233_ = v___y_1251_;
v___y_1234_ = v___y_1247_;
v___y_1235_ = v___y_1248_;
v___y_1236_ = v___y_1249_;
v___y_1237_ = v___y_1250_;
v___y_1238_ = v___x_1228_;
goto v___jp_1229_;
}
else
{
v___y_1230_ = v___y_1244_;
v___y_1231_ = v___y_1245_;
v___y_1232_ = v___y_1246_;
v___y_1233_ = v___y_1251_;
v___y_1234_ = v___y_1247_;
v___y_1235_ = v___y_1248_;
v___y_1236_ = v___y_1249_;
v___y_1237_ = v___y_1250_;
v___y_1238_ = v___y_1248_;
goto v___jp_1229_;
}
}
v___jp_1253_:
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Std_Http_URI_instBEqOrigin_beq(v___y_1256_, v_current_1066_);
if (v___x_1261_ == 0)
{
v___y_1244_ = v___y_1254_;
v___y_1245_ = v___y_1255_;
v___y_1246_ = v___y_1256_;
v___y_1247_ = v___y_1257_;
v___y_1248_ = v___y_1260_;
v___y_1249_ = v___y_1258_;
v___y_1250_ = v___y_1259_;
v___y_1251_ = v___x_1228_;
goto v___jp_1243_;
}
else
{
v___y_1244_ = v___y_1254_;
v___y_1245_ = v___y_1255_;
v___y_1246_ = v___y_1256_;
v___y_1247_ = v___y_1257_;
v___y_1248_ = v___y_1260_;
v___y_1249_ = v___y_1258_;
v___y_1250_ = v___y_1259_;
v___y_1251_ = v___y_1260_;
goto v___jp_1243_;
}
}
v___jp_1262_:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__0));
v___x_1272_ = lean_string_dec_eq(v_scheme_1266_, v___x_1271_);
lean_dec_ref(v_scheme_1266_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_dec_ref(v___y_1267_);
lean_dec_ref(v___y_1265_);
lean_dec_ref(v_current_1066_);
v___x_1273_ = lean_box(0);
return v___x_1273_;
}
else
{
v___y_1254_ = v___y_1263_;
v___y_1255_ = v___y_1264_;
v___y_1256_ = v___y_1265_;
v___y_1257_ = v___y_1267_;
v___y_1258_ = v___y_1269_;
v___y_1259_ = v___y_1270_;
v___y_1260_ = v___y_1268_;
goto v___jp_1253_;
}
}
v___jp_1274_:
{
lean_object* v___x_1276_; lean_object* v___f_1277_; lean_object* v___f_1278_; uint8_t v___x_1279_; 
v___x_1276_ = l_Std_Http_Header_Name_location;
v___f_1277_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___f_1278_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__1));
v___x_1279_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1277_, v___f_1278_, v___x_1276_, v_responseHeaders_1072_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref(v_current_1066_);
v___x_1280_ = lean_box(0);
return v___x_1280_;
}
else
{
lean_object* v_entries_1281_; lean_object* v_indexes_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_entry_1285_; lean_object* v___x_1286_; lean_object* v_snd_1287_; lean_object* v___f_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_entries_1281_ = lean_ctor_get(v_responseHeaders_1072_, 0);
v_indexes_1282_ = lean_ctor_get(v_responseHeaders_1072_, 1);
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_1282_, v___x_1276_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v_entry_1285_ = lean_array_fget(v___x_1283_, v___x_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_array_fget_borrowed(v_entries_1281_, v_entry_1285_);
lean_dec(v_entry_1285_);
v_snd_1287_ = lean_ctor_get(v___x_1286_, 1);
v___f_1288_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
v___x_1289_ = lean_string_to_utf8(v_snd_1287_);
v___x_1290_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1288_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v___x_1291_; 
lean_dec_ref_known(v___x_1290_, 1);
lean_dec_ref(v_current_1066_);
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1293_; 
v_a_1292_ = lean_ctor_get(v___x_1290_, 0);
lean_inc_n(v_a_1292_, 2);
lean_dec_ref_known(v___x_1290_, 1);
lean_inc_ref(v_current_1066_);
v___x_1293_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_1066_, v_a_1292_);
if (lean_obj_tag(v___x_1293_) == 1)
{
lean_object* v_val_1294_; uint8_t v_method_1295_; lean_object* v_uri_1296_; lean_object* v_headers_1297_; lean_object* v_scheme_1298_; uint8_t v_newMethod_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v_method_1295_ = lean_ctor_get_uint8(v_request_1067_, sizeof(void*)*2);
v_uri_1296_ = lean_ctor_get(v_request_1067_, 0);
v_headers_1297_ = lean_ctor_get(v_request_1067_, 1);
v_scheme_1298_ = lean_ctor_get(v_val_1294_, 0);
v_newMethod_1299_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_1295_, v_responseVersion_1070_, v_status_1071_);
v___x_1300_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_1301_ = lean_string_dec_eq(v_scheme_1298_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_inc_ref(v_scheme_1298_);
v___y_1263_ = v_headers_1297_;
v___y_1264_ = v_uri_1296_;
v___y_1265_ = v_val_1294_;
v_scheme_1266_ = v_scheme_1298_;
v___y_1267_ = v_a_1292_;
v___y_1268_ = v___y_1275_;
v___y_1269_ = v_newMethod_1299_;
v___y_1270_ = v_method_1295_;
goto v___jp_1262_;
}
else
{
if (v___y_1275_ == 0)
{
v___y_1254_ = v_headers_1297_;
v___y_1255_ = v_uri_1296_;
v___y_1256_ = v_val_1294_;
v___y_1257_ = v_a_1292_;
v___y_1258_ = v_newMethod_1299_;
v___y_1259_ = v_method_1295_;
v___y_1260_ = v___y_1275_;
goto v___jp_1253_;
}
else
{
lean_inc_ref(v_scheme_1298_);
v___y_1263_ = v_headers_1297_;
v___y_1264_ = v_uri_1296_;
v___y_1265_ = v_val_1294_;
v_scheme_1266_ = v_scheme_1298_;
v___y_1267_ = v_a_1292_;
v___y_1268_ = v___y_1275_;
v___y_1269_ = v_newMethod_1299_;
v___y_1270_ = v_method_1295_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v___x_1302_; 
lean_dec(v___x_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_current_1066_);
v___x_1302_ = lean_box(0);
return v___x_1302_;
}
}
}
}
v___jp_1303_:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_box(19);
v___x_1305_ = l_Std_Http_instBEqStatus_beq(v_status_1071_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = lean_box(20);
v___x_1307_ = l_Std_Http_instBEqStatus_beq(v_status_1071_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = lean_box(18);
v___x_1309_ = l_Std_Http_instBEqStatus_beq(v_status_1071_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = lean_box(14);
v___x_1311_ = l_Std_Http_instBEqStatus_beq(v_status_1071_, v___x_1310_);
if (v___x_1311_ == 0)
{
if (v_onlySafeRedirects_1069_ == 0)
{
v___y_1275_ = v_onlySafeRedirects_1069_;
goto v___jp_1274_;
}
else
{
uint8_t v_method_1312_; uint8_t v___x_1313_; 
v_method_1312_ = lean_ctor_get_uint8(v_request_1067_, sizeof(void*)*2);
v___x_1313_ = l_Std_Http_Method_isSafe(v_method_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v_current_1066_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
else
{
v___y_1275_ = v___x_1311_;
goto v___jp_1274_;
}
}
}
else
{
lean_object* v___x_1315_; 
lean_dec_ref(v_current_1066_);
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1316_; 
lean_dec_ref(v_current_1066_);
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
}
else
{
lean_object* v___x_1317_; 
lean_dec_ref(v_current_1066_);
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
}
else
{
lean_object* v___x_1318_; 
lean_dec_ref(v_current_1066_);
v___x_1318_ = lean_box(0);
return v___x_1318_;
}
}
v___jp_1319_:
{
if (v___y_1320_ == 0)
{
goto v___jp_1303_;
}
else
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = lean_box(16);
v___x_1322_ = l_Std_Http_instBEqStatus_beq(v_status_1071_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
lean_dec_ref(v_current_1066_);
v___x_1323_ = lean_box(0);
return v___x_1323_;
}
else
{
goto v___jp_1303_;
}
}
}
}
v___jp_1073_:
{
lean_object* v_scheme_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_rewrittenTarget_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_scheme_1081_ = lean_ctor_get(v_current_1066_, 0);
lean_inc_ref(v_scheme_1081_);
lean_dec_ref(v_current_1066_);
v___x_1082_ = l_Std_Http_RequestTarget_pathOrRoot(v___y_1074_);
v___x_1083_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v___y_1074_);
v_rewrittenTarget_1084_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v___y_1077_, v___y_1076_, v___x_1082_, v___x_1083_, v_scheme_1081_);
v___x_1085_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1085_, 0, v___y_1075_);
lean_ctor_set(v___x_1085_, 1, v_rewrittenTarget_1084_);
lean_ctor_set(v___x_1085_, 2, v___y_1079_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*3, v___y_1078_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*3 + 1, v___y_1080_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*3 + 2, v___y_1076_);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
v___jp_1087_:
{
uint8_t v___x_1094_; 
v___x_1094_ = 0;
v___y_1074_ = v___y_1088_;
v___y_1075_ = v___y_1089_;
v___y_1076_ = v___y_1091_;
v___y_1077_ = v___y_1090_;
v___y_1078_ = v___y_1092_;
v___y_1079_ = v___y_1093_;
v___y_1080_ = v___x_1094_;
goto v___jp_1073_;
}
v___jp_1095_:
{
uint8_t v___x_1104_; 
v___x_1104_ = l_Std_Http_instBEqMethod_beq(v___y_1101_, v___y_1102_);
if (v___x_1104_ == 0)
{
uint8_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = 9;
v___x_1106_ = l_Std_Http_instBEqMethod_beq(v___y_1101_, v___x_1105_);
if (v___x_1106_ == 0)
{
if (v___y_1097_ == 0)
{
uint8_t v___x_1107_; 
v___x_1107_ = 1;
v___y_1074_ = v___y_1096_;
v___y_1075_ = v___y_1098_;
v___y_1076_ = v___y_1100_;
v___y_1077_ = v___y_1099_;
v___y_1078_ = v___y_1101_;
v___y_1079_ = v___y_1103_;
v___y_1080_ = v___x_1107_;
goto v___jp_1073_;
}
else
{
v___y_1088_ = v___y_1096_;
v___y_1089_ = v___y_1098_;
v___y_1090_ = v___y_1099_;
v___y_1091_ = v___y_1100_;
v___y_1092_ = v___y_1101_;
v___y_1093_ = v___y_1103_;
goto v___jp_1087_;
}
}
else
{
v___y_1088_ = v___y_1096_;
v___y_1089_ = v___y_1098_;
v___y_1090_ = v___y_1099_;
v___y_1091_ = v___y_1100_;
v___y_1092_ = v___y_1101_;
v___y_1093_ = v___y_1103_;
goto v___jp_1087_;
}
}
else
{
v___y_1088_ = v___y_1096_;
v___y_1089_ = v___y_1098_;
v___y_1090_ = v___y_1099_;
v___y_1091_ = v___y_1100_;
v___y_1092_ = v___y_1101_;
v___y_1093_ = v___y_1103_;
goto v___jp_1087_;
}
}
v___jp_1108_:
{
if (v_bodyReplayable_1068_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v___y_1116_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v___y_1111_);
lean_dec_ref(v_current_1066_);
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
else
{
v___y_1096_ = v___y_1110_;
v___y_1097_ = v___y_1109_;
v___y_1098_ = v___y_1111_;
v___y_1099_ = v___y_1113_;
v___y_1100_ = v___y_1112_;
v___y_1101_ = v___y_1114_;
v___y_1102_ = v___y_1115_;
v___y_1103_ = v___y_1116_;
goto v___jp_1095_;
}
}
v___jp_1118_:
{
uint8_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = 9;
v___x_1129_ = l_Std_Http_instBEqMethod_beq(v___y_1125_, v___x_1128_);
if (v___x_1129_ == 0)
{
v___y_1109_ = v___y_1120_;
v___y_1110_ = v___y_1119_;
v___y_1111_ = v___y_1121_;
v___y_1112_ = v___y_1123_;
v___y_1113_ = v___y_1122_;
v___y_1114_ = v___y_1125_;
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1127_;
goto v___jp_1108_;
}
else
{
if (v___y_1124_ == 0)
{
v___y_1096_ = v___y_1119_;
v___y_1097_ = v___y_1120_;
v___y_1098_ = v___y_1121_;
v___y_1099_ = v___y_1122_;
v___y_1100_ = v___y_1123_;
v___y_1101_ = v___y_1125_;
v___y_1102_ = v___y_1126_;
v___y_1103_ = v___y_1127_;
goto v___jp_1095_;
}
else
{
v___y_1109_ = v___y_1120_;
v___y_1110_ = v___y_1119_;
v___y_1111_ = v___y_1121_;
v___y_1112_ = v___y_1123_;
v___y_1113_ = v___y_1122_;
v___y_1114_ = v___y_1125_;
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1127_;
goto v___jp_1108_;
}
}
}
v___jp_1130_:
{
uint8_t v___x_1140_; 
v___x_1140_ = l_Std_Http_instBEqMethod_beq(v___y_1137_, v___y_1138_);
if (v___x_1140_ == 0)
{
v___y_1119_ = v___y_1132_;
v___y_1120_ = v___y_1131_;
v___y_1121_ = v___y_1133_;
v___y_1122_ = v___y_1135_;
v___y_1123_ = v___y_1134_;
v___y_1124_ = v___y_1136_;
v___y_1125_ = v___y_1137_;
v___y_1126_ = v___y_1138_;
v___y_1127_ = v___y_1139_;
goto v___jp_1118_;
}
else
{
if (v___y_1136_ == 0)
{
v___y_1096_ = v___y_1132_;
v___y_1097_ = v___y_1131_;
v___y_1098_ = v___y_1133_;
v___y_1099_ = v___y_1135_;
v___y_1100_ = v___y_1134_;
v___y_1101_ = v___y_1137_;
v___y_1102_ = v___y_1138_;
v___y_1103_ = v___y_1139_;
goto v___jp_1095_;
}
else
{
v___y_1119_ = v___y_1132_;
v___y_1120_ = v___y_1131_;
v___y_1121_ = v___y_1133_;
v___y_1122_ = v___y_1135_;
v___y_1123_ = v___y_1134_;
v___y_1124_ = v___y_1136_;
v___y_1125_ = v___y_1137_;
v___y_1126_ = v___y_1138_;
v___y_1127_ = v___y_1139_;
goto v___jp_1118_;
}
}
}
v___jp_1141_:
{
if (v___y_1142_ == 0)
{
v___y_1131_ = v___y_1142_;
v___y_1132_ = v___y_1143_;
v___y_1133_ = v___y_1144_;
v___y_1134_ = v___y_1146_;
v___y_1135_ = v___y_1145_;
v___y_1136_ = v___y_1147_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1150_;
goto v___jp_1130_;
}
else
{
if (v___y_1147_ == 0)
{
v___y_1096_ = v___y_1143_;
v___y_1097_ = v___y_1142_;
v___y_1098_ = v___y_1144_;
v___y_1099_ = v___y_1145_;
v___y_1100_ = v___y_1146_;
v___y_1101_ = v___y_1148_;
v___y_1102_ = v___y_1149_;
v___y_1103_ = v___y_1150_;
goto v___jp_1095_;
}
else
{
v___y_1131_ = v___y_1142_;
v___y_1132_ = v___y_1143_;
v___y_1133_ = v___y_1144_;
v___y_1134_ = v___y_1146_;
v___y_1135_ = v___y_1145_;
v___y_1136_ = v___y_1147_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1150_;
goto v___jp_1130_;
}
}
}
v___jp_1151_:
{
lean_object* v_scrubbed_1161_; 
v_scrubbed_1161_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v___y_1152_, v___y_1157_, v___y_1154_);
if (v___y_1157_ == 0)
{
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___y_1153_;
v___y_1144_ = v___y_1155_;
v___y_1145_ = v___y_1156_;
v___y_1146_ = v___y_1157_;
v___y_1147_ = v___y_1158_;
v___y_1148_ = v___y_1159_;
v___y_1149_ = v___y_1160_;
v___y_1150_ = v_scrubbed_1161_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1162_; 
lean_inc_ref(v___y_1155_);
v___x_1162_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_1161_, v___y_1155_);
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___y_1153_;
v___y_1144_ = v___y_1155_;
v___y_1145_ = v___y_1156_;
v___y_1146_ = v___y_1157_;
v___y_1147_ = v___y_1158_;
v___y_1148_ = v___y_1159_;
v___y_1149_ = v___y_1160_;
v___y_1150_ = v___x_1162_;
goto v___jp_1141_;
}
}
v___jp_1163_:
{
if (v___y_1170_ == 0)
{
lean_object* v___x_1174_; 
lean_dec_ref(v___y_1169_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_current_1066_);
v___x_1174_ = lean_box(0);
return v___x_1174_;
}
else
{
v___y_1152_ = v___y_1164_;
v___y_1153_ = v___y_1166_;
v___y_1154_ = v___y_1165_;
v___y_1155_ = v___y_1167_;
v___y_1156_ = v___y_1169_;
v___y_1157_ = v___y_1168_;
v___y_1158_ = v___y_1171_;
v___y_1159_ = v___y_1172_;
v___y_1160_ = v___y_1173_;
goto v___jp_1151_;
}
}
v___jp_1175_:
{
if (v___y_1185_ == 0)
{
v___y_1164_ = v___y_1176_;
v___y_1165_ = v___y_1178_;
v___y_1166_ = v___y_1177_;
v___y_1167_ = v___y_1179_;
v___y_1168_ = v___y_1181_;
v___y_1169_ = v___y_1180_;
v___y_1170_ = v___y_1182_;
v___y_1171_ = v___y_1183_;
v___y_1172_ = v___y_1184_;
v___y_1173_ = v___y_1186_;
goto v___jp_1163_;
}
else
{
if (v___y_1183_ == 0)
{
v___y_1152_ = v___y_1176_;
v___y_1153_ = v___y_1177_;
v___y_1154_ = v___y_1178_;
v___y_1155_ = v___y_1179_;
v___y_1156_ = v___y_1180_;
v___y_1157_ = v___y_1181_;
v___y_1158_ = v___y_1183_;
v___y_1159_ = v___y_1184_;
v___y_1160_ = v___y_1186_;
goto v___jp_1151_;
}
else
{
v___y_1164_ = v___y_1176_;
v___y_1165_ = v___y_1178_;
v___y_1166_ = v___y_1177_;
v___y_1167_ = v___y_1179_;
v___y_1168_ = v___y_1181_;
v___y_1169_ = v___y_1180_;
v___y_1170_ = v___y_1182_;
v___y_1171_ = v___y_1183_;
v___y_1172_ = v___y_1184_;
v___y_1173_ = v___y_1186_;
goto v___jp_1163_;
}
}
}
v___jp_1187_:
{
if (v_bodyReplayable_1068_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v___y_1193_);
lean_dec_ref(v___y_1191_);
lean_dec_ref(v_current_1066_);
v___x_1197_ = lean_box(0);
return v___x_1197_;
}
else
{
v___y_1152_ = v___y_1188_;
v___y_1153_ = v___y_1190_;
v___y_1154_ = v___y_1189_;
v___y_1155_ = v___y_1191_;
v___y_1156_ = v___y_1193_;
v___y_1157_ = v___y_1192_;
v___y_1158_ = v___y_1194_;
v___y_1159_ = v___y_1195_;
v___y_1160_ = v___y_1196_;
goto v___jp_1151_;
}
}
v___jp_1198_:
{
if (v___y_1207_ == 0)
{
v___y_1188_ = v___y_1199_;
v___y_1189_ = v___y_1201_;
v___y_1190_ = v___y_1200_;
v___y_1191_ = v___y_1202_;
v___y_1192_ = v___y_1204_;
v___y_1193_ = v___y_1203_;
v___y_1194_ = v___y_1205_;
v___y_1195_ = v___y_1206_;
v___y_1196_ = v___y_1208_;
goto v___jp_1187_;
}
else
{
if (v___y_1205_ == 0)
{
v___y_1152_ = v___y_1199_;
v___y_1153_ = v___y_1200_;
v___y_1154_ = v___y_1201_;
v___y_1155_ = v___y_1202_;
v___y_1156_ = v___y_1203_;
v___y_1157_ = v___y_1204_;
v___y_1158_ = v___y_1205_;
v___y_1159_ = v___y_1206_;
v___y_1160_ = v___y_1208_;
goto v___jp_1151_;
}
else
{
v___y_1188_ = v___y_1199_;
v___y_1189_ = v___y_1201_;
v___y_1190_ = v___y_1200_;
v___y_1191_ = v___y_1202_;
v___y_1192_ = v___y_1204_;
v___y_1193_ = v___y_1203_;
v___y_1194_ = v___y_1205_;
v___y_1195_ = v___y_1206_;
v___y_1196_ = v___y_1208_;
goto v___jp_1187_;
}
}
}
v___jp_1209_:
{
uint8_t v___x_1221_; uint8_t v_isPost_1222_; 
v___x_1221_ = 23;
v_isPost_1222_ = l_Std_Http_instBEqMethod_beq(v___y_1219_, v___x_1221_);
switch(lean_obj_tag(v_status_1071_))
{
case 15:
{
v___y_1176_ = v___y_1210_;
v___y_1177_ = v___y_1212_;
v___y_1178_ = v___y_1211_;
v___y_1179_ = v___y_1213_;
v___y_1180_ = v___y_1215_;
v___y_1181_ = v___y_1214_;
v___y_1182_ = v_isPost_1222_;
v___y_1183_ = v___y_1216_;
v___y_1184_ = v___y_1217_;
v___y_1185_ = v___y_1220_;
v___y_1186_ = v___y_1218_;
goto v___jp_1175_;
}
case 16:
{
v___y_1176_ = v___y_1210_;
v___y_1177_ = v___y_1212_;
v___y_1178_ = v___y_1211_;
v___y_1179_ = v___y_1213_;
v___y_1180_ = v___y_1215_;
v___y_1181_ = v___y_1214_;
v___y_1182_ = v_isPost_1222_;
v___y_1183_ = v___y_1216_;
v___y_1184_ = v___y_1217_;
v___y_1185_ = v___y_1220_;
v___y_1186_ = v___y_1218_;
goto v___jp_1175_;
}
case 21:
{
v___y_1199_ = v___y_1210_;
v___y_1200_ = v___y_1212_;
v___y_1201_ = v___y_1211_;
v___y_1202_ = v___y_1213_;
v___y_1203_ = v___y_1215_;
v___y_1204_ = v___y_1214_;
v___y_1205_ = v___y_1216_;
v___y_1206_ = v___y_1217_;
v___y_1207_ = v___y_1220_;
v___y_1208_ = v___y_1218_;
goto v___jp_1198_;
}
case 22:
{
v___y_1199_ = v___y_1210_;
v___y_1200_ = v___y_1212_;
v___y_1201_ = v___y_1211_;
v___y_1202_ = v___y_1213_;
v___y_1203_ = v___y_1215_;
v___y_1204_ = v___y_1214_;
v___y_1205_ = v___y_1216_;
v___y_1206_ = v___y_1217_;
v___y_1207_ = v___y_1220_;
v___y_1208_ = v___y_1218_;
goto v___jp_1198_;
}
default: 
{
v___y_1152_ = v___y_1210_;
v___y_1153_ = v___y_1212_;
v___y_1154_ = v___y_1211_;
v___y_1155_ = v___y_1213_;
v___y_1156_ = v___y_1215_;
v___y_1157_ = v___y_1214_;
v___y_1158_ = v___y_1216_;
v___y_1159_ = v___y_1217_;
v___y_1160_ = v___y_1218_;
goto v___jp_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_1329_, lean_object* v_request_1330_, lean_object* v_bodyReplayable_1331_, lean_object* v_onlySafeRedirects_1332_, lean_object* v_responseVersion_1333_, lean_object* v_status_1334_, lean_object* v_responseHeaders_1335_){
_start:
{
uint8_t v_bodyReplayable_boxed_1336_; uint8_t v_onlySafeRedirects_boxed_1337_; uint8_t v_responseVersion_boxed_1338_; lean_object* v_res_1339_; 
v_bodyReplayable_boxed_1336_ = lean_unbox(v_bodyReplayable_1331_);
v_onlySafeRedirects_boxed_1337_ = lean_unbox(v_onlySafeRedirects_1332_);
v_responseVersion_boxed_1338_ = lean_unbox(v_responseVersion_1333_);
v_res_1339_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1329_, v_request_1330_, v_bodyReplayable_boxed_1336_, v_onlySafeRedirects_boxed_1337_, v_responseVersion_boxed_1338_, v_status_1334_, v_responseHeaders_1335_);
lean_dec_ref(v_responseHeaders_1335_);
lean_dec(v_status_1334_);
lean_dec_ref(v_request_1330_);
return v_res_1339_;
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
