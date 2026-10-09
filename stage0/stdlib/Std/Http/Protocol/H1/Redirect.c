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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object*);
lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
extern lean_object* l_Std_Http_Header_Name_host;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_proxyAuthorization;
extern lean_object* l_Std_Http_Header_Name_lastModified;
extern lean_object* l_Std_Http_Header_Name_contentLocation;
extern lean_object* l_Std_Http_Header_Name_contentLanguage;
extern lean_object* l_Std_Http_Header_Name_contentEncoding;
extern lean_object* l_Std_Http_Header_Name_contentLength;
extern lean_object* l_Std_Http_Header_Name_contentType;
uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object*, lean_object*);
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
lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(lean_object* v_empty_24_){
_start:
{
lean_inc(v_empty_24_);
return v_empty_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg___boxed(lean_object* v_empty_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(v_empty_25_);
lean_dec(v_empty_25_);
return v_res_26_;
}
}
lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_empty_30_){
_start:
{
lean_inc(v_empty_30_);
return v_empty_30_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_empty_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(lean_box(0), v_t_28_, lean_box(0), v_empty_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_empty_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_empty_35_);
lean_dec(v_empty_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(lean_object* v_replay_38_){
_start:
{
lean_inc(v_replay_38_);
return v_replay_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg___boxed(lean_object* v_replay_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(v_replay_39_);
lean_dec(v_replay_39_);
return v_res_40_;
}
}
lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_replay_44_){
_start:
{
lean_inc(v_replay_44_);
return v_replay_44_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_replay_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(lean_box(0), v_t_42_, lean_box(0), v_replay_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_replay_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_replay_49_);
lean_dec(v_replay_49_);
return v_res_51_;
}
}
uint8_t l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(lean_object* v_n_52_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_nat_dec_le(v_n_52_, v___x_53_);
if (v___x_54_ == 0)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_52_ = stack[0].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(v_n_52_);
stack->m_num = v_res_57_;
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
uint8_t l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(uint8_t v_x_61_, uint8_t v_y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_63_ = lean_box(v_x_61_);
v___x_64_ = lean_obj_tag_nat(v___x_63_);
lean_dec(v___x_63_);
v___x_65_ = lean_box(v_y_62_);
v___x_66_ = lean_obj_tag_nat(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_nat_dec_eq(v___x_64_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_61_ = stack[0].m_num;
uint8_t v_y_62_ = stack[1].m_num;
uint8_t v_res_68_;
v_res_68_ = l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(v_x_61_, v_y_62_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_x_23__boxed_71_; uint8_t v_y_24__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_23__boxed_71_ = lean_unbox(v_x_69_);
v_y_24__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(v_x_23__boxed_71_, v_y_24__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(2u);
v___x_82_ = lean_nat_to_int(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(uint8_t v_x_85_, lean_object* v_prec_86_){
_start:
{
lean_object* v___y_88_; lean_object* v___y_95_; 
if (v_x_85_ == 0)
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1024u);
v___x_102_ = lean_nat_dec_le(v___x_101_, v_prec_86_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_88_ = v___x_103_;
goto v___jp_87_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_88_ = v___x_104_;
goto v___jp_87_;
}
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_86_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_95_ = v___x_107_;
goto v___jp_94_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_95_ = v___x_108_;
goto v___jp_94_;
}
}
v___jp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_89_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1));
lean_inc(v___y_88_);
v___x_90_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_90_, 0, v___y_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = 0;
v___x_92_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*1, v___x_91_);
v___x_93_ = l_Repr_addAppParen(v___x_92_, v_prec_86_);
return v___x_93_;
}
v___jp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_96_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3));
lean_inc(v___y_95_);
v___x_97_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_97_, 0, v___y_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = 0;
v___x_99_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set_uint8(v___x_99_, sizeof(void*)*1, v___x_98_);
v___x_100_ = l_Repr_addAppParen(v___x_99_, v_prec_86_);
return v___x_100_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_85_ = stack[0].m_num;
lean_object* v_prec_86_ = stack[1].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_x_85_, v_prec_86_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
uint8_t v_x_117__boxed_112_; lean_object* v_res_113_; 
v_x_117__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_x_117__boxed_112_, v_prec_111_);
lean_dec(v_prec_111_);
return v_res_113_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default(void){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction(void){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Protocol_H1_instReprRedirectPlan_repr_spec__0(lean_object* v_a_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_nat_to_int(v_a_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(10u);
v___x_134_ = lean_nat_to_int(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(11u);
v___x_148_ = lean_nat_to_int(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(14u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(17u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0));
v___x_161_ = lean_string_length(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24);
v___x_163_ = lean_nat_to_int(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(lean_object* v_x_168_){
_start:
{
lean_object* v_origin_169_; lean_object* v_target_170_; uint8_t v_method_171_; lean_object* v_headers_172_; uint8_t v_bodyAction_173_; uint8_t v_isCrossOrigin_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_origin_169_ = lean_ctor_get(v_x_168_, 0);
lean_inc_ref(v_origin_169_);
v_target_170_ = lean_ctor_get(v_x_168_, 1);
lean_inc(v_target_170_);
v_method_171_ = lean_ctor_get_uint8(v_x_168_, sizeof(void*)*3);
v_headers_172_ = lean_ctor_get(v_x_168_, 2);
lean_inc_ref(v_headers_172_);
v_bodyAction_173_ = lean_ctor_get_uint8(v_x_168_, sizeof(void*)*3 + 1);
v_isCrossOrigin_174_ = lean_ctor_get_uint8(v_x_168_, sizeof(void*)*3 + 2);
lean_dec_ref(v_x_168_);
v___x_175_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5));
v___x_176_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6));
v___x_177_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_origin_169_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_177_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = 0;
v___x_182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*1, v___x_181_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_176_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9));
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_box(1);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11));
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_175_);
v___x_191_ = l_Std_Http_instReprRequestTarget_repr(v_target_170_, v___x_178_);
v___x_192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_177_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_181_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_184_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_186_);
v___x_197_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13));
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_175_);
v___x_200_ = l_Std_Http_instReprMethod_repr(v_method_171_, v___x_178_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_177_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*1, v___x_181_);
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_199_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_184_);
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_186_);
v___x_206_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15));
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_175_);
v___x_209_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16);
v___x_210_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_172_);
v___x_211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*1, v___x_181_);
v___x_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_208_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_184_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_186_);
v___x_216_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18));
v___x_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_175_);
v___x_219_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19);
v___x_220_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_bodyAction_173_, v___x_178_);
v___x_221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*1, v___x_181_);
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_218_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_184_);
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_186_);
v___x_226_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21));
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_175_);
v___x_229_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22);
v___x_230_ = l_Bool_repr___redArg(v_isCrossOrigin_174_);
v___x_231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*1, v___x_181_);
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_228_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25);
v___x_235_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26));
v___x_236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_233_);
v___x_237_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27));
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_234_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*1, v___x_181_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(lean_object* v_x_241_, lean_object* v_prec_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(v_x_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed(lean_object* v_x_244_, lean_object* v_prec_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(v_x_244_, v_prec_245_);
lean_dec(v_prec_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl(lean_object* v_x_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_tag_nat(v_x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl___boxed(lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl(v_x_251_);
lean_dec(v_x_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(lean_object* v_t_253_, lean_object* v_k_254_){
_start:
{
if (lean_obj_tag(v_t_253_) == 0)
{
return v_k_254_;
}
else
{
lean_object* v_plan_255_; lean_object* v___x_256_; 
v_plan_255_ = lean_ctor_get(v_t_253_, 0);
lean_inc_ref(v_plan_255_);
lean_dec_ref_known(v_t_253_, 1);
v___x_256_ = lean_apply_1(v_k_254_, v_plan_255_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(lean_object* v_motive_257_, lean_object* v_ctorIdx_258_, lean_object* v_t_259_, lean_object* v_h_260_, lean_object* v_k_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_259_, v_k_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___boxed(lean_object* v_motive_263_, lean_object* v_ctorIdx_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_k_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(v_motive_263_, v_ctorIdx_264_, v_t_265_, v_h_266_, v_k_267_);
lean_dec(v_ctorIdx_264_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim___redArg(lean_object* v_t_269_, lean_object* v_done_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_269_, v_done_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim(lean_object* v_motive_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_done_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_273_, v_done_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim___redArg(lean_object* v_t_277_, lean_object* v_follow_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_277_, v_follow_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim(lean_object* v_motive_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_follow_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_281_, v_follow_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_box(0);
return v___x_285_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(0);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(lean_object* v_current_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
lean_object* v_uri_289_; lean_object* v_authority_290_; 
lean_dec_ref(v_current_287_);
v_uri_289_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_uri_289_);
lean_dec_ref_known(v_x_288_, 1);
v_authority_290_ = lean_ctor_get(v_uri_289_, 1);
lean_inc(v_authority_290_);
if (lean_obj_tag(v_authority_290_) == 0)
{
lean_object* v___x_291_; 
lean_dec_ref(v_uri_289_);
v___x_291_ = lean_box(0);
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_307_; 
v_val_292_ = lean_ctor_get(v_authority_290_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_authority_290_);
if (v_isSharedCheck_307_ == 0)
{
v___x_294_ = v_authority_290_;
v_isShared_295_ = v_isSharedCheck_307_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_val_292_);
lean_dec(v_authority_290_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_307_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v_scheme_296_; lean_object* v_host_297_; lean_object* v_port_298_; uint16_t v___y_300_; 
v_scheme_296_ = lean_ctor_get(v_uri_289_, 0);
lean_inc_ref(v_scheme_296_);
lean_dec_ref(v_uri_289_);
v_host_297_ = lean_ctor_get(v_val_292_, 1);
lean_inc_ref(v_host_297_);
v_port_298_ = lean_ctor_get(v_val_292_, 2);
lean_inc(v_port_298_);
lean_dec(v_val_292_);
if (lean_obj_tag(v_port_298_) == 2)
{
uint16_t v_port_305_; 
v_port_305_ = lean_ctor_get_uint16(v_port_298_, 0);
lean_dec_ref_known(v_port_298_, 0);
v___y_300_ = v_port_305_;
goto v___jp_299_;
}
else
{
uint16_t v___x_306_; 
lean_dec(v_port_298_);
v___x_306_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_296_);
v___y_300_ = v___x_306_;
goto v___jp_299_;
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_301_, 0, v_scheme_296_);
lean_ctor_set(v___x_301_, 1, v_host_297_);
lean_ctor_set_uint16(v___x_301_, sizeof(void*)*2, v___y_300_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_301_);
v___x_303_ = v___x_294_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
else
{
lean_object* v_ref_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_340_; 
v_ref_308_ = lean_ctor_get(v_x_288_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_288_);
if (v_isSharedCheck_340_ == 0)
{
v___x_310_ = v_x_288_;
v_isShared_311_ = v_isSharedCheck_340_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_ref_308_);
lean_dec(v_x_288_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_340_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_authority_312_; 
v_authority_312_ = lean_ctor_get(v_ref_308_, 0);
lean_inc(v_authority_312_);
lean_dec_ref(v_ref_308_);
if (lean_obj_tag(v_authority_312_) == 1)
{
lean_object* v_val_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_336_; 
lean_del_object(v___x_310_);
v_val_313_ = lean_ctor_get(v_authority_312_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_authority_312_);
if (v_isSharedCheck_336_ == 0)
{
v___x_315_ = v_authority_312_;
v_isShared_316_ = v_isSharedCheck_336_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_val_313_);
lean_dec(v_authority_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_336_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_host_317_; lean_object* v_port_318_; uint16_t v___y_320_; 
v_host_317_ = lean_ctor_get(v_val_313_, 1);
lean_inc_ref(v_host_317_);
v_port_318_ = lean_ctor_get(v_val_313_, 2);
lean_inc(v_port_318_);
lean_dec(v_val_313_);
if (lean_obj_tag(v_port_318_) == 2)
{
uint16_t v_port_333_; 
v_port_333_ = lean_ctor_get_uint16(v_port_318_, 0);
lean_dec_ref_known(v_port_318_, 0);
v___y_320_ = v_port_333_;
goto v___jp_319_;
}
else
{
lean_object* v_scheme_334_; uint16_t v___x_335_; 
lean_dec(v_port_318_);
v_scheme_334_ = lean_ctor_get(v_current_287_, 0);
v___x_335_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_334_);
v___y_320_ = v___x_335_;
goto v___jp_319_;
}
v___jp_319_:
{
lean_object* v_scheme_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
v_scheme_321_ = lean_ctor_get(v_current_287_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_current_287_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_current_287_, 1);
lean_dec(v_unused_332_);
v___x_323_ = v_current_287_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_scheme_321_);
lean_dec(v_current_287_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v_host_317_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_scheme_321_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_host_317_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
lean_ctor_set_uint16(v___x_326_, sizeof(void*)*2, v___y_320_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_326_);
v___x_328_ = v___x_315_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
else
{
lean_object* v___x_338_; 
lean_dec(v_authority_312_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v_current_287_);
v___x_338_ = v___x_310_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_current_287_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t v_originalMethod_341_, uint8_t v_responseVersion_342_, lean_object* v_x_343_){
_start:
{
uint8_t v___y_345_; 
switch(lean_obj_tag(v_x_343_))
{
case 17:
{
uint8_t v___x_352_; uint8_t v___x_353_; 
v___x_352_ = 9;
v___x_353_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_341_, v___x_352_);
if (v___x_353_ == 0)
{
uint8_t v___x_354_; 
v___x_354_ = 8;
return v___x_354_;
}
else
{
return v___x_352_;
}
}
case 15:
{
goto v___jp_347_;
}
case 16:
{
goto v___jp_347_;
}
default: 
{
return v_originalMethod_341_;
}
}
v___jp_344_:
{
if (v___y_345_ == 0)
{
return v_originalMethod_341_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 8;
return v___x_346_;
}
}
v___jp_347_:
{
uint8_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = 23;
v___x_349_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_341_, v___x_348_);
if (v___x_349_ == 0)
{
v___y_345_ = v___x_349_;
goto v___jp_344_;
}
else
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 0;
v___x_351_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_342_, v___x_350_);
if (v___x_351_ == 0)
{
v___y_345_ = v___x_349_;
goto v___jp_344_;
}
else
{
return v_originalMethod_341_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod_0interp(lean_interpreter_value* stack)
{
uint8_t v_originalMethod_341_ = stack[0].m_num;
uint8_t v_responseVersion_342_ = stack[1].m_num;
lean_object* v_x_343_ = stack[2].m_obj;
uint8_t v_res_355_;
v_res_355_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_341_, v_responseVersion_342_, v_x_343_);
stack->m_num = v_res_355_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_356_, lean_object* v_responseVersion_357_, lean_object* v_x_358_){
_start:
{
uint8_t v_originalMethod_boxed_359_; uint8_t v_responseVersion_boxed_360_; uint8_t v_res_361_; lean_object* v_r_362_; 
v_originalMethod_boxed_359_ = lean_unbox(v_originalMethod_356_);
v_responseVersion_boxed_360_ = lean_unbox(v_responseVersion_357_);
v_res_361_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_359_, v_responseVersion_boxed_360_, v_x_358_);
lean_dec(v_x_358_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_363_ = l_Std_Http_Header_Name_transferEncoding;
v___x_364_ = l_Std_Http_Header_Name_keepAlive;
v___x_365_ = l_Std_Http_Header_Name_connection;
v___x_366_ = lean_unsigned_to_nat(3u);
v___x_367_ = lean_mk_empty_array_with_capacity(v___x_366_);
v___x_368_ = lean_array_push(v___x_367_, v___x_365_);
v___x_369_ = lean_array_push(v___x_368_, v___x_364_);
v___x_370_ = lean_array_push(v___x_369_, v___x_363_);
return v___x_370_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_371_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object* v_a_372_, lean_object* v_x_373_){
_start:
{
if (lean_obj_tag(v_x_373_) == 0)
{
uint8_t v___x_374_; 
v___x_374_ = 0;
return v___x_374_;
}
else
{
lean_object* v_key_375_; lean_object* v_tail_376_; uint8_t v___x_377_; 
v_key_375_ = lean_ctor_get(v_x_373_, 0);
v_tail_376_ = lean_ctor_get(v_x_373_, 2);
v___x_377_ = lean_string_dec_eq(v_key_375_, v_a_372_);
if (v___x_377_ == 0)
{
v_x_373_ = v_tail_376_;
goto _start;
}
else
{
return v___x_377_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_372_ = stack[0].m_obj;
lean_object* v_x_373_ = stack[1].m_obj;
uint8_t v_res_379_;
v_res_379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_372_, v_x_373_);
stack->m_num = v_res_379_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object* v_a_380_, lean_object* v_x_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_380_, v_x_381_);
lean_dec(v_x_381_);
lean_dec_ref(v_a_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object* v_m_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_buckets_386_; lean_object* v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v_fold_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_buckets_386_ = lean_ctor_get(v_m_384_, 1);
v___x_387_ = lean_array_get_size(v_buckets_386_);
v___x_388_ = lean_string_hash(v_a_385_);
v___x_389_ = 32ULL;
v___x_390_ = lean_uint64_shift_right(v___x_388_, v___x_389_);
v_fold_391_ = lean_uint64_xor(v___x_388_, v___x_390_);
v___x_392_ = 16ULL;
v___x_393_ = lean_uint64_shift_right(v_fold_391_, v___x_392_);
v___x_394_ = lean_uint64_xor(v_fold_391_, v___x_393_);
v___x_395_ = lean_uint64_to_usize(v___x_394_);
v___x_396_ = lean_usize_of_nat(v___x_387_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_sub(v___x_396_, v___x_397_);
v___x_399_ = lean_usize_land(v___x_395_, v___x_398_);
v___x_400_ = lean_array_uget_borrowed(v_buckets_386_, v___x_399_);
v___x_401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_385_, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_384_ = stack[0].m_obj;
lean_object* v_a_385_ = stack[1].m_obj;
uint8_t v_res_402_;
v_res_402_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_384_, v_a_385_);
stack->m_num = v_res_402_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object* v_m_403_, lean_object* v_a_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_403_, v_a_404_);
lean_dec_ref(v_a_404_);
lean_dec_ref(v_m_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(lean_object* v_a_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_key_409_; lean_object* v_value_410_; lean_object* v_tail_411_; uint8_t v___x_412_; 
v_key_409_ = lean_ctor_get(v_x_408_, 0);
v_value_410_ = lean_ctor_get(v_x_408_, 1);
v_tail_411_ = lean_ctor_get(v_x_408_, 2);
v___x_412_ = lean_string_dec_eq(v_key_409_, v_a_407_);
if (v___x_412_ == 0)
{
v_x_408_ = v_tail_411_;
goto _start;
}
else
{
lean_inc(v_value_410_);
return v_value_410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg___boxed(lean_object* v_a_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_414_, v_x_415_);
lean_dec(v_x_415_);
lean_dec_ref(v_a_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_buckets_419_; lean_object* v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v_fold_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_buckets_419_ = lean_ctor_get(v_m_417_, 1);
v___x_420_ = lean_array_get_size(v_buckets_419_);
v___x_421_ = lean_string_hash(v_a_418_);
v___x_422_ = 32ULL;
v___x_423_ = lean_uint64_shift_right(v___x_421_, v___x_422_);
v_fold_424_ = lean_uint64_xor(v___x_421_, v___x_423_);
v___x_425_ = 16ULL;
v___x_426_ = lean_uint64_shift_right(v_fold_424_, v___x_425_);
v___x_427_ = lean_uint64_xor(v_fold_424_, v___x_426_);
v___x_428_ = lean_uint64_to_usize(v___x_427_);
v___x_429_ = lean_usize_of_nat(v___x_420_);
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_sub(v___x_429_, v___x_430_);
v___x_432_ = lean_usize_land(v___x_428_, v___x_431_);
v___x_433_ = lean_array_uget_borrowed(v_buckets_419_, v___x_432_);
v___x_434_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_418_, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object* v_m_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_m_435_, v_a_436_);
lean_dec_ref(v_a_436_);
lean_dec_ref(v_m_435_);
return v_res_437_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_438_, size_t v_i_439_, size_t v_stop_440_, lean_object* v_b_441_){
_start:
{
lean_object* v___y_443_; uint8_t v___x_447_; 
v___x_447_ = lean_usize_dec_eq(v_i_439_, v_stop_440_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_array_uget_borrowed(v_as_438_, v_i_439_);
lean_inc(v___x_448_);
v___x_449_ = l_Std_Http_Header_Name_ofString_x3f(v___x_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
v___y_443_ = v_b_441_;
goto v___jp_442_;
}
else
{
lean_object* v_val_450_; lean_object* v___x_451_; 
v_val_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = lean_array_push(v_b_441_, v_val_450_);
v___y_443_ = v___x_451_;
goto v___jp_442_;
}
}
else
{
return v_b_441_;
}
v___jp_442_:
{
size_t v___x_444_; size_t v___x_445_; 
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_add(v_i_439_, v___x_444_);
v_i_439_ = v___x_445_;
v_b_441_ = v___y_443_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_438_ = stack[0].m_obj;
size_t v_i_439_ = stack[1].m_num;
size_t v_stop_440_ = stack[2].m_num;
lean_object* v_b_441_ = stack[3].m_obj;
lean_object* v_res_452_;
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_438_, v_i_439_, v_stop_440_, v_b_441_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_453_, lean_object* v_i_454_, lean_object* v_stop_455_, lean_object* v_b_456_){
_start:
{
size_t v_i_boxed_457_; size_t v_stop_boxed_458_; lean_object* v_res_459_; 
v_i_boxed_457_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_stop_boxed_458_ = lean_unbox_usize(v_stop_455_);
lean_dec(v_stop_455_);
v_res_459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_453_, v_i_boxed_457_, v_stop_boxed_458_, v_b_456_);
lean_dec_ref(v_as_453_);
return v_res_459_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(lean_object* v_as_460_, size_t v_i_461_, size_t v_stop_462_, lean_object* v_b_463_){
_start:
{
lean_object* v___y_465_; uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_eq(v_i_461_, v_stop_462_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_array_uget_borrowed(v_as_460_, v_i_461_);
lean_inc(v___x_470_);
v___x_471_ = l_Std_Http_Header_Connection_parse(v___x_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
v___y_465_ = v_b_463_;
goto v___jp_464_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_array_get_size(v_val_472_);
v___x_475_ = lean_nat_dec_lt(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_dec(v_val_472_);
v___y_465_ = v_b_463_;
goto v___jp_464_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_le(v___x_474_, v___x_474_);
if (v___x_476_ == 0)
{
if (v___x_475_ == 0)
{
lean_dec(v_val_472_);
v___y_465_ = v_b_463_;
goto v___jp_464_;
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((size_t)0ULL);
v___x_478_ = lean_usize_of_nat(v___x_474_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_472_, v___x_477_, v___x_478_, v_b_463_);
lean_dec(v_val_472_);
v___y_465_ = v___x_479_;
goto v___jp_464_;
}
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_474_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_472_, v___x_480_, v___x_481_, v_b_463_);
lean_dec(v_val_472_);
v___y_465_ = v___x_482_;
goto v___jp_464_;
}
}
}
}
else
{
return v_b_463_;
}
v___jp_464_:
{
size_t v___x_466_; size_t v___x_467_; 
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_add(v_i_461_, v___x_466_);
v_i_461_ = v___x_467_;
v_b_463_ = v___y_465_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_460_ = stack[0].m_obj;
size_t v_i_461_ = stack[1].m_num;
size_t v_stop_462_ = stack[2].m_num;
lean_object* v_b_463_ = stack[3].m_obj;
lean_object* v_res_483_;
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_as_460_, v_i_461_, v_stop_462_, v_b_463_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4___boxed(lean_object* v_as_484_, lean_object* v_i_485_, lean_object* v_stop_486_, lean_object* v_b_487_){
_start:
{
size_t v_i_boxed_488_; size_t v_stop_boxed_489_; lean_object* v_res_490_; 
v_i_boxed_488_ = lean_unbox_usize(v_i_485_);
lean_dec(v_i_485_);
v_stop_boxed_489_ = lean_unbox_usize(v_stop_486_);
lean_dec(v_stop_486_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_as_484_, v_i_boxed_488_, v_stop_boxed_489_, v_b_487_);
lean_dec_ref(v_as_484_);
return v_res_490_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(lean_object* v___x_491_, lean_object* v___x_492_, size_t v_sz_493_, size_t v_i_494_, lean_object* v_bs_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_lt(v_i_494_, v_sz_493_);
if (v___x_496_ == 0)
{
return v_bs_495_;
}
else
{
lean_object* v_entries_497_; lean_object* v___x_498_; lean_object* v_bs_x27_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_snd_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v_entries_497_ = lean_ctor_get(v___x_491_, 0);
v___x_498_ = lean_unsigned_to_nat(0u);
v_bs_x27_499_ = lean_array_uset(v_bs_495_, v_i_494_, v___x_498_);
v___x_500_ = lean_usize_to_nat(v_i_494_);
v___x_501_ = lean_array_fget_borrowed(v___x_492_, v___x_500_);
lean_dec(v___x_500_);
v___x_502_ = lean_array_fget_borrowed(v_entries_497_, v___x_501_);
v_snd_503_ = lean_ctor_get(v___x_502_, 1);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_494_, v___x_504_);
lean_inc(v_snd_503_);
v___x_506_ = lean_array_uset(v_bs_x27_499_, v_i_494_, v_snd_503_);
v_i_494_ = v___x_505_;
v_bs_495_ = v___x_506_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_491_ = stack[0].m_obj;
lean_object* v___x_492_ = stack[1].m_obj;
size_t v_sz_493_ = stack[2].m_num;
size_t v_i_494_ = stack[3].m_num;
lean_object* v_bs_495_ = stack[4].m_obj;
lean_object* v_res_508_;
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_491_, v___x_492_, v_sz_493_, v_i_494_, v_bs_495_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg___boxed(lean_object* v___x_509_, lean_object* v___x_510_, lean_object* v_sz_511_, lean_object* v_i_512_, lean_object* v_bs_513_){
_start:
{
size_t v_sz_boxed_514_; size_t v_i_boxed_515_; lean_object* v_res_516_; 
v_sz_boxed_514_ = lean_unbox_usize(v_sz_511_);
lean_dec(v_sz_511_);
v_i_boxed_515_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_509_, v___x_510_, v_sz_boxed_514_, v_i_boxed_515_, v_bs_513_);
lean_dec_ref(v___x_510_);
lean_dec_ref(v___x_509_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_519_){
_start:
{
lean_object* v_indexes_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_indexes_520_ = lean_ctor_get(v_headers_519_, 1);
v___x_521_ = l_Std_Http_Header_Name_connection;
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
return v___x_523_;
}
else
{
lean_object* v___x_524_; size_t v_sz_525_; size_t v___x_526_; lean_object* v_entries_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_520_, v___x_521_);
v_sz_525_ = lean_array_size(v___x_524_);
v___x_526_ = ((size_t)0ULL);
lean_inc(v___x_524_);
v_entries_527_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v_headers_519_, v___x_524_, v_sz_525_, v___x_526_, v___x_524_);
lean_dec(v___x_524_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_530_ = lean_array_get_size(v_entries_527_);
v___x_531_ = lean_nat_dec_lt(v___x_528_, v___x_530_);
if (v___x_531_ == 0)
{
lean_dec_ref(v_entries_527_);
return v___x_529_;
}
else
{
uint8_t v___x_532_; 
v___x_532_ = lean_nat_dec_le(v___x_530_, v___x_530_);
if (v___x_532_ == 0)
{
if (v___x_531_ == 0)
{
lean_dec_ref(v_entries_527_);
return v___x_529_;
}
else
{
size_t v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_usize_of_nat(v___x_530_);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_entries_527_, v___x_526_, v___x_533_, v___x_529_);
lean_dec_ref(v_entries_527_);
return v___x_534_;
}
}
else
{
size_t v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_usize_of_nat(v___x_530_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_entries_527_, v___x_526_, v___x_535_, v___x_529_);
lean_dec_ref(v_entries_527_);
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_537_);
lean_dec_ref(v_headers_537_);
return v_res_538_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_00_u03b2_539_, lean_object* v_m_540_, lean_object* v_a_541_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_540_, v_a_541_);
return v___x_542_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_540_ = stack[1].m_obj;
lean_object* v_a_541_ = stack[2].m_obj;
uint8_t v_res_543_;
v_res_543_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_box(0), v_m_540_, v_a_541_);
stack->m_num = v_res_543_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_00_u03b2_544_, lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_00_u03b2_544_, v_m_545_, v_a_546_);
lean_dec_ref(v_a_546_);
lean_dec_ref(v_m_545_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v_00_u03b2_549_, lean_object* v_m_550_, lean_object* v_a_551_, lean_object* v_hma_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_m_550_, v_a_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v_00_u03b2_554_, lean_object* v_m_555_, lean_object* v_a_556_, lean_object* v_hma_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_00_u03b2_554_, v_m_555_, v_a_556_, v_hma_557_);
lean_dec_ref(v_a_556_);
lean_dec_ref(v_m_555_);
return v_res_558_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object* v___x_559_, lean_object* v___x_560_, lean_object* v_as_561_, size_t v_sz_562_, size_t v_i_563_, lean_object* v_bs_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_559_, v___x_560_, v_sz_562_, v_i_563_, v_bs_564_);
return v___x_565_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_559_ = stack[0].m_obj;
lean_object* v___x_560_ = stack[1].m_obj;
lean_object* v_as_561_ = stack[2].m_obj;
size_t v_sz_562_ = stack[3].m_num;
size_t v_i_563_ = stack[4].m_num;
lean_object* v_bs_564_ = stack[5].m_obj;
lean_object* v_res_566_;
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v___x_559_, v___x_560_, v_as_561_, v_sz_562_, v_i_563_, v_bs_564_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v_as_569_, lean_object* v_sz_570_, lean_object* v_i_571_, lean_object* v_bs_572_){
_start:
{
size_t v_sz_boxed_573_; size_t v_i_boxed_574_; lean_object* v_res_575_; 
v_sz_boxed_573_ = lean_unbox_usize(v_sz_570_);
lean_dec(v_sz_570_);
v_i_boxed_574_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v___x_567_, v___x_568_, v_as_569_, v_sz_boxed_573_, v_i_boxed_574_, v_bs_572_);
lean_dec_ref(v_as_569_);
lean_dec_ref(v___x_568_);
lean_dec_ref(v___x_567_);
return v_res_575_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object* v_00_u03b2_576_, lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_577_ = stack[1].m_obj;
lean_object* v_x_578_ = stack[2].m_obj;
uint8_t v_res_580_;
v_res_580_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_box(0), v_a_577_, v_x_578_);
stack->m_num = v_res_580_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object* v_00_u03b2_581_, lean_object* v_a_582_, lean_object* v_x_583_){
_start:
{
uint8_t v_res_584_; lean_object* v_r_585_; 
v_res_584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(v_00_u03b2_581_, v_a_582_, v_x_583_);
lean_dec(v_x_583_);
lean_dec_ref(v_a_582_);
v_r_585_ = lean_box(v_res_584_);
return v_r_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(lean_object* v_00_u03b2_586_, lean_object* v_a_587_, lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_587_, v_x_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___boxed(lean_object* v_00_u03b2_591_, lean_object* v_a_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(v_00_u03b2_591_, v_a_592_, v_x_593_, v_x_594_);
lean_dec(v_x_593_);
lean_dec_ref(v_a_592_);
return v_res_595_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_596_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_mk_empty_array_with_capacity(v___x_597_);
v___x_599_ = lean_array_push(v___x_598_, v___x_596_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_600_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_601_ = l_Std_Http_Header_Name_referer;
v___x_602_ = l_Std_Http_Header_Name_cookie;
v___x_603_ = l_Std_Http_Header_Name_authorization;
v___x_604_ = lean_unsigned_to_nat(3u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_array_push(v___x_605_, v___x_603_);
v___x_607_ = lean_array_push(v___x_606_, v___x_602_);
v___x_608_ = lean_array_push(v___x_607_, v___x_601_);
return v___x_608_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_609_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_610_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_611_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_612_ = lean_unsigned_to_nat(2u);
v___x_613_ = lean_mk_empty_array_with_capacity(v___x_612_);
v___x_614_ = lean_array_push(v___x_613_, v___x_611_);
v___x_615_ = lean_array_push(v___x_614_, v___x_610_);
return v___x_615_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_616_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_617_ = l_Std_Http_Header_Name_lastModified;
v___x_618_ = l_Std_Http_Header_Name_contentLocation;
v___x_619_ = l_Std_Http_Header_Name_contentLanguage;
v___x_620_ = l_Std_Http_Header_Name_contentEncoding;
v___x_621_ = l_Std_Http_Header_Name_contentLength;
v___x_622_ = l_Std_Http_Header_Name_contentType;
v___x_623_ = lean_unsigned_to_nat(6u);
v___x_624_ = lean_mk_empty_array_with_capacity(v___x_623_);
v___x_625_ = lean_array_push(v___x_624_, v___x_622_);
v___x_626_ = lean_array_push(v___x_625_, v___x_621_);
v___x_627_ = lean_array_push(v___x_626_, v___x_620_);
v___x_628_ = lean_array_push(v___x_627_, v___x_619_);
v___x_629_ = lean_array_push(v___x_628_, v___x_618_);
v___x_630_ = lean_array_push(v___x_629_, v___x_617_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_631_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_box(0);
v___x_635_ = lean_unsigned_to_nat(16u);
v___x_636_ = lean_mk_array(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2);
v___x_641_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0));
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
return v___x_642_;
}
}
lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg(){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3);
return v___x_644_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_645_;
v_res_645_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
stack->m_obj
 = v_res_645_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___boxed(lean_object* v___dummy_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
return v_res_647_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0(void){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v_00_u03b2_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(lean_object* v_i_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_mk_empty_array_with_capacity(v___x_653_);
v___x_655_ = lean_array_push(v___x_654_, v_i_651_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_val_657_ = lean_ctor_get(v_x_652_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v_x_652_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_val_657_);
lean_dec(v_x_652_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_array_push(v_val_657_, v_i_651_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(lean_object* v_i_666_, lean_object* v_a_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v_val_671_; lean_object* v___x_672_; 
v___x_669_ = lean_box(0);
v___x_670_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(v_i_666_, v___x_669_);
v_val_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_val_671_);
lean_dec(v___x_670_);
v___x_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_672_, 0, v_a_667_);
lean_ctor_set(v___x_672_, 1, v_val_671_);
lean_ctor_set(v___x_672_, 2, v_x_668_);
return v___x_672_;
}
else
{
lean_object* v_key_673_; lean_object* v_value_674_; lean_object* v_tail_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_690_; 
v_key_673_ = lean_ctor_get(v_x_668_, 0);
v_value_674_ = lean_ctor_get(v_x_668_, 1);
v_tail_675_ = lean_ctor_get(v_x_668_, 2);
v_isSharedCheck_690_ = !lean_is_exclusive(v_x_668_);
if (v_isSharedCheck_690_ == 0)
{
v___x_677_ = v_x_668_;
v_isShared_678_ = v_isSharedCheck_690_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_tail_675_);
lean_inc(v_value_674_);
lean_inc(v_key_673_);
lean_dec(v_x_668_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_690_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
uint8_t v___x_679_; 
v___x_679_ = lean_string_dec_eq(v_key_673_, v_a_667_);
if (v___x_679_ == 0)
{
lean_object* v_tail_680_; lean_object* v___x_682_; 
v_tail_680_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(v_i_666_, v_a_667_, v_tail_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 2, v_tail_680_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_key_673_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_value_674_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_tail_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_val_686_; lean_object* v___x_688_; 
lean_dec(v_key_673_);
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v_value_674_);
v___x_685_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(v_i_666_, v___x_684_);
v_val_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_val_686_);
lean_dec(v___x_685_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v_val_686_);
lean_ctor_set(v___x_677_, 0, v_a_667_);
v___x_688_ = v___x_677_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_667_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_val_686_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_tail_675_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
if (lean_obj_tag(v_x_692_) == 0)
{
return v_x_691_;
}
else
{
lean_object* v_key_693_; lean_object* v_value_694_; lean_object* v_tail_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_718_; 
v_key_693_ = lean_ctor_get(v_x_692_, 0);
v_value_694_ = lean_ctor_get(v_x_692_, 1);
v_tail_695_ = lean_ctor_get(v_x_692_, 2);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_692_);
if (v_isSharedCheck_718_ == 0)
{
v___x_697_ = v_x_692_;
v_isShared_698_ = v_isSharedCheck_718_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_tail_695_);
lean_inc(v_value_694_);
lean_inc(v_key_693_);
lean_dec(v_x_692_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_718_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v_fold_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v___x_706_; size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_699_ = lean_array_get_size(v_x_691_);
v___x_700_ = lean_string_hash(v_key_693_);
v___x_701_ = 32ULL;
v___x_702_ = lean_uint64_shift_right(v___x_700_, v___x_701_);
v_fold_703_ = lean_uint64_xor(v___x_700_, v___x_702_);
v___x_704_ = 16ULL;
v___x_705_ = lean_uint64_shift_right(v_fold_703_, v___x_704_);
v___x_706_ = lean_uint64_xor(v_fold_703_, v___x_705_);
v___x_707_ = lean_uint64_to_usize(v___x_706_);
v___x_708_ = lean_usize_of_nat(v___x_699_);
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_sub(v___x_708_, v___x_709_);
v___x_711_ = lean_usize_land(v___x_707_, v___x_710_);
v___x_712_ = lean_array_uget_borrowed(v_x_691_, v___x_711_);
lean_inc(v___x_712_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 2, v___x_712_);
v___x_714_ = v___x_697_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_key_693_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_value_694_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v___x_712_);
v___x_714_ = v_reuseFailAlloc_717_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; 
v___x_715_ = lean_array_uset(v_x_691_, v___x_711_, v___x_714_);
v_x_691_ = v___x_715_;
v_x_692_ = v_tail_695_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(lean_object* v_i_719_, lean_object* v_source_720_, lean_object* v_target_721_){
_start:
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_array_get_size(v_source_720_);
v___x_723_ = lean_nat_dec_lt(v_i_719_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec_ref(v_source_720_);
lean_dec(v_i_719_);
return v_target_721_;
}
else
{
lean_object* v_es_724_; lean_object* v___x_725_; lean_object* v_source_726_; lean_object* v_target_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_es_724_ = lean_array_fget(v_source_720_, v_i_719_);
v___x_725_ = lean_box(0);
v_source_726_ = lean_array_fset(v_source_720_, v_i_719_, v___x_725_);
v_target_727_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(v_target_721_, v_es_724_);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_i_719_, v___x_728_);
lean_dec(v_i_719_);
v_i_719_ = v___x_729_;
v_source_720_ = v_source_726_;
v_target_721_ = v_target_727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(lean_object* v_data_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_nbuckets_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_732_ = lean_array_get_size(v_data_731_);
v___x_733_ = lean_unsigned_to_nat(2u);
v_nbuckets_734_ = lean_nat_mul(v___x_732_, v___x_733_);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_box(0);
v___x_737_ = lean_mk_array(v_nbuckets_734_, v___x_736_);
v___x_738_ = lean_array_propagate_mark(v_data_731_, v___x_737_);
v___x_739_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(v___x_735_, v_data_731_, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v_i_740_, lean_object* v_m_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_size_743_; lean_object* v_buckets_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_794_; 
v_size_743_ = lean_ctor_get(v_m_741_, 0);
v_buckets_744_ = lean_ctor_get(v_m_741_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_m_741_);
if (v_isSharedCheck_794_ == 0)
{
v___x_746_ = v_m_741_;
v_isShared_747_ = v_isSharedCheck_794_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_buckets_744_);
lean_inc(v_size_743_);
lean_dec(v_m_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_794_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; uint64_t v___x_749_; uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v_fold_752_; uint64_t v___x_753_; uint64_t v___x_754_; uint64_t v___x_755_; size_t v___x_756_; size_t v___x_757_; size_t v___x_758_; size_t v___x_759_; size_t v___x_760_; lean_object* v_bkt_761_; uint8_t v___x_762_; 
v___x_748_ = lean_array_get_size(v_buckets_744_);
v___x_749_ = lean_string_hash(v_a_742_);
v___x_750_ = 32ULL;
v___x_751_ = lean_uint64_shift_right(v___x_749_, v___x_750_);
v_fold_752_ = lean_uint64_xor(v___x_749_, v___x_751_);
v___x_753_ = 16ULL;
v___x_754_ = lean_uint64_shift_right(v_fold_752_, v___x_753_);
v___x_755_ = lean_uint64_xor(v_fold_752_, v___x_754_);
v___x_756_ = lean_uint64_to_usize(v___x_755_);
v___x_757_ = lean_usize_of_nat(v___x_748_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_sub(v___x_757_, v___x_758_);
v___x_760_ = lean_usize_land(v___x_756_, v___x_759_);
v_bkt_761_ = lean_array_uget_borrowed(v_buckets_744_, v___x_760_);
v___x_762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_742_, v_bkt_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_size_x27_766_; lean_object* v___x_767_; lean_object* v_buckets_x27_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_mk_empty_array_with_capacity(v___x_763_);
v___x_765_ = lean_array_push(v___x_764_, v_i_740_);
v_size_x27_766_ = lean_nat_add(v_size_743_, v___x_763_);
lean_dec(v_size_743_);
lean_inc(v_bkt_761_);
v___x_767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_767_, 0, v_a_742_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
lean_ctor_set(v___x_767_, 2, v_bkt_761_);
v_buckets_x27_768_ = lean_array_uset(v_buckets_744_, v___x_760_, v___x_767_);
v___x_769_ = lean_unsigned_to_nat(4u);
v___x_770_ = lean_nat_mul(v_size_x27_766_, v___x_769_);
v___x_771_ = lean_unsigned_to_nat(3u);
v___x_772_ = lean_nat_div(v___x_770_, v___x_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_array_get_size(v_buckets_x27_768_);
v___x_774_ = lean_nat_dec_le(v___x_772_, v___x_773_);
lean_dec(v___x_772_);
if (v___x_774_ == 0)
{
lean_object* v_val_775_; lean_object* v___x_777_; 
v_val_775_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(v_buckets_x27_768_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_val_775_);
lean_ctor_set(v___x_746_, 0, v_size_x27_766_);
v___x_777_ = v___x_746_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_size_x27_766_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_val_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_object* v___x_780_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_buckets_x27_768_);
lean_ctor_set(v___x_746_, 0, v_size_x27_766_);
v___x_780_ = v___x_746_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_size_x27_766_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_buckets_x27_768_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v___x_782_; lean_object* v_buckets_x27_783_; lean_object* v_bkt_x27_784_; lean_object* v___y_786_; uint8_t v___x_791_; 
lean_inc(v_bkt_761_);
v___x_782_ = lean_box(0);
v_buckets_x27_783_ = lean_array_uset(v_buckets_744_, v___x_760_, v___x_782_);
lean_inc_ref(v_a_742_);
v_bkt_x27_784_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(v_i_740_, v_a_742_, v_bkt_761_);
v___x_791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_742_, v_bkt_x27_784_);
lean_dec_ref(v_a_742_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_sub(v_size_743_, v___x_792_);
lean_dec(v_size_743_);
v___y_786_ = v___x_793_;
goto v___jp_785_;
}
else
{
v___y_786_ = v_size_743_;
goto v___jp_785_;
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_array_uset(v_buckets_x27_783_, v___x_760_, v_bkt_x27_784_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_787_);
lean_ctor_set(v___x_746_, 0, v___y_786_);
v___x_789_ = v___x_746_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___y_786_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_a_795_, lean_object* v_as_796_, size_t v_i_797_, size_t v_stop_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_usize_dec_eq(v_i_797_, v_stop_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_array_uget_borrowed(v_as_796_, v_i_797_);
v___x_801_ = lean_string_dec_eq(v_a_795_, v___x_800_);
if (v___x_801_ == 0)
{
size_t v___x_802_; size_t v___x_803_; 
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_797_, v___x_802_);
v_i_797_ = v___x_803_;
goto _start;
}
else
{
return v___x_801_;
}
}
else
{
uint8_t v___x_805_; 
v___x_805_ = 0;
return v___x_805_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_795_ = stack[0].m_obj;
lean_object* v_as_796_ = stack[1].m_obj;
size_t v_i_797_ = stack[2].m_num;
size_t v_stop_798_ = stack[3].m_num;
uint8_t v_res_806_;
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_795_, v_as_796_, v_i_797_, v_stop_798_);
stack->m_num = v_res_806_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_a_807_, lean_object* v_as_808_, lean_object* v_i_809_, lean_object* v_stop_810_){
_start:
{
size_t v_i_boxed_811_; size_t v_stop_boxed_812_; uint8_t v_res_813_; lean_object* v_r_814_; 
v_i_boxed_811_ = lean_unbox_usize(v_i_809_);
lean_dec(v_i_809_);
v_stop_boxed_812_ = lean_unbox_usize(v_stop_810_);
lean_dec(v_stop_810_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_807_, v_as_808_, v_i_boxed_811_, v_stop_boxed_812_);
lean_dec_ref(v_as_808_);
lean_dec_ref(v_a_807_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_as_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_array_get_size(v_as_815_);
v___x_819_ = lean_nat_dec_lt(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
return v___x_819_;
}
else
{
if (v___x_819_ == 0)
{
return v___x_819_;
}
else
{
size_t v___x_820_; size_t v___x_821_; uint8_t v___x_822_; 
v___x_820_ = ((size_t)0ULL);
v___x_821_ = lean_usize_of_nat(v___x_818_);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_816_, v_as_815_, v___x_820_, v___x_821_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_815_ = stack[0].m_obj;
lean_object* v_a_816_ = stack[1].m_obj;
uint8_t v_res_823_;
v_res_823_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_as_815_, v_a_816_);
stack->m_num = v_res_823_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object* v_as_824_, lean_object* v_a_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_as_824_, v_a_825_);
lean_dec_ref(v_a_825_);
lean_dec_ref(v_as_824_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object* v___y_828_, lean_object* v_as_829_, size_t v_i_830_, size_t v_stop_831_, lean_object* v_b_832_){
_start:
{
lean_object* v___y_834_; uint8_t v___x_838_; 
v___x_838_ = lean_usize_dec_eq(v_i_830_, v_stop_831_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v_fst_840_; uint8_t v___x_854_; 
v___x_839_ = lean_array_uget_borrowed(v_as_829_, v_i_830_);
v_fst_840_ = lean_ctor_get(v___x_839_, 0);
v___x_854_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_828_, v_fst_840_);
if (v___x_854_ == 0)
{
goto v___jp_841_;
}
else
{
if (v___x_838_ == 0)
{
v___y_834_ = v_b_832_;
goto v___jp_833_;
}
else
{
goto v___jp_841_;
}
}
v___jp_841_:
{
lean_object* v_entries_842_; lean_object* v_indexes_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_853_; 
v_entries_842_ = lean_ctor_get(v_b_832_, 0);
v_indexes_843_ = lean_ctor_get(v_b_832_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_b_832_);
if (v_isSharedCheck_853_ == 0)
{
v___x_845_ = v_b_832_;
v_isShared_846_ = v_isSharedCheck_853_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_indexes_843_);
lean_inc(v_entries_842_);
lean_dec(v_b_832_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_853_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_i_847_; lean_object* v_entries_848_; lean_object* v_indexes_849_; lean_object* v___x_851_; 
v_i_847_ = lean_array_get_size(v_entries_842_);
lean_inc(v___x_839_);
v_entries_848_ = lean_array_push(v_entries_842_, v___x_839_);
lean_inc(v_fst_840_);
v_indexes_849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v_i_847_, v_indexes_843_, v_fst_840_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_indexes_849_);
lean_ctor_set(v___x_845_, 0, v_entries_848_);
v___x_851_ = v___x_845_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_entries_848_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_indexes_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v___y_834_ = v___x_851_;
goto v___jp_833_;
}
}
}
}
else
{
return v_b_832_;
}
v___jp_833_:
{
size_t v___x_835_; size_t v___x_836_; 
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_830_, v___x_835_);
v_i_830_ = v___x_836_;
v_b_832_ = v___y_834_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_828_ = stack[0].m_obj;
lean_object* v_as_829_ = stack[1].m_obj;
size_t v_i_830_ = stack[2].m_num;
size_t v_stop_831_ = stack[3].m_num;
lean_object* v_b_832_ = stack[4].m_obj;
lean_object* v_res_855_;
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_828_, v_as_829_, v_i_830_, v_stop_831_, v_b_832_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object* v___y_856_, lean_object* v_as_857_, lean_object* v_i_858_, lean_object* v_stop_859_, lean_object* v_b_860_){
_start:
{
size_t v_i_boxed_861_; size_t v_stop_boxed_862_; lean_object* v_res_863_; 
v_i_boxed_861_ = lean_unbox_usize(v_i_858_);
lean_dec(v_i_858_);
v_stop_boxed_862_ = lean_unbox_usize(v_stop_859_);
lean_dec(v_stop_859_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_856_, v_as_857_, v_i_boxed_861_, v_stop_boxed_862_, v_b_860_);
lean_dec_ref(v_as_857_);
lean_dec_ref(v___y_856_);
return v_res_863_;
}
}
lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_864_, uint8_t v_isCrossOrigin_865_, uint8_t v_methodChanged_866_){
_start:
{
lean_object* v___y_868_; lean_object* v___y_878_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_afterConnection_885_; 
v___x_883_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_884_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_864_);
v_afterConnection_885_ = l_Array_append___redArg(v___x_883_, v___x_884_);
lean_dec_ref(v___x_884_);
if (v_isCrossOrigin_865_ == 0)
{
v___y_878_ = v_afterConnection_885_;
goto v___jp_877_;
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_886_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_887_ = l_Array_append___redArg(v_afterConnection_885_, v___x_886_);
v___x_888_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_889_ = l_Array_append___redArg(v___x_887_, v___x_888_);
v___x_890_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_891_ = l_Array_append___redArg(v___x_889_, v___x_890_);
v___y_878_ = v___x_891_;
goto v___jp_877_;
}
v___jp_867_:
{
lean_object* v_entries_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_entries_869_ = lean_ctor_get(v_headers_864_, 0);
v___x_870_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_get_size(v_entries_869_);
v___x_873_ = lean_nat_dec_lt(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_dec_ref(v___y_868_);
return v___x_870_;
}
else
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)0ULL);
v___x_875_ = lean_usize_of_nat(v___x_872_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_868_, v_entries_869_, v___x_874_, v___x_875_, v___x_870_);
lean_dec_ref(v___y_868_);
return v___x_876_;
}
}
v___jp_877_:
{
if (v_methodChanged_866_ == 0)
{
v___y_868_ = v___y_878_;
goto v___jp_867_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_880_ = l_Array_append___redArg(v___y_878_, v___x_879_);
v___x_881_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_882_ = l_Array_append___redArg(v___x_880_, v___x_881_);
v___y_868_ = v___x_882_;
goto v___jp_867_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_0interp(lean_interpreter_value* stack)
{
lean_object* v_headers_864_ = stack[0].m_obj;
uint8_t v_isCrossOrigin_865_ = stack[1].m_num;
uint8_t v_methodChanged_866_ = stack[2].m_num;
lean_object* v_res_892_;
v_res_892_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_864_, v_isCrossOrigin_865_, v_methodChanged_866_);
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_893_, lean_object* v_isCrossOrigin_894_, lean_object* v_methodChanged_895_){
_start:
{
uint8_t v_isCrossOrigin_boxed_896_; uint8_t v_methodChanged_boxed_897_; lean_object* v_res_898_; 
v_isCrossOrigin_boxed_896_ = lean_unbox(v_isCrossOrigin_894_);
v_methodChanged_boxed_897_ = lean_unbox(v_methodChanged_895_);
v_res_898_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_893_, v_isCrossOrigin_boxed_896_, v_methodChanged_boxed_897_);
lean_dec_ref(v_headers_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(lean_object* v_00_u03b2_899_, lean_object* v_data_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(v_data_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_902_, lean_object* v_i_903_, lean_object* v_source_904_, lean_object* v_target_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(v_i_903_, v_source_904_, v_target_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_911_, lean_object* v_origin_912_){
_start:
{
lean_object* v_entries_913_; lean_object* v_indexes_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_entries_913_ = lean_ctor_get(v_headers_911_, 0);
v_indexes_914_ = lean_ctor_get(v_headers_911_, 1);
v___x_915_ = l_Std_Http_Header_Name_host;
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec_ref(v_origin_912_);
return v_headers_911_;
}
else
{
if (v___x_916_ == 0)
{
lean_dec_ref(v_origin_912_);
return v_headers_911_;
}
else
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_932_; 
lean_inc_ref(v_indexes_914_);
lean_inc_ref(v_entries_913_);
v_isSharedCheck_932_ = !lean_is_exclusive(v_headers_911_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; lean_object* v_unused_934_; 
v_unused_933_ = lean_ctor_get(v_headers_911_, 1);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_headers_911_, 0);
lean_dec(v_unused_934_);
v___x_918_ = v_headers_911_;
v_isShared_919_ = v_isSharedCheck_932_;
goto v_resetjp_917_;
}
else
{
lean_dec(v_headers_911_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_932_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_idxs_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_lastIdx_926_; lean_object* v___x_927_; lean_object* v_entries_928_; lean_object* v___x_930_; 
v___x_920_ = l_Std_Http_URI_Origin_hostHeader(v_origin_912_);
v___x_921_ = l_Std_Http_Header_Value_ofString_x21(v___x_920_);
v_idxs_922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_914_, v___x_915_);
v___x_923_ = lean_array_get_size(v_idxs_922_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_sub(v___x_923_, v___x_924_);
v_lastIdx_926_ = lean_array_fget(v_idxs_922_, v___x_925_);
lean_dec(v___x_925_);
lean_dec(v_idxs_922_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_915_);
lean_ctor_set(v___x_927_, 1, v___x_921_);
v_entries_928_ = lean_array_fset(v_entries_913_, v_lastIdx_926_, v___x_927_);
lean_dec(v_lastIdx_926_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v_entries_928_);
v___x_930_ = v___x_918_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_entries_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_indexes_914_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_935_){
_start:
{
switch(lean_obj_tag(v_x_935_))
{
case 0:
{
lean_object* v_query_936_; 
v_query_936_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_query_936_);
return v_query_936_;
}
case 1:
{
lean_object* v_uri_937_; lean_object* v_query_938_; 
v_uri_937_ = lean_ctor_get(v_x_935_, 0);
v_query_938_ = lean_ctor_get(v_uri_937_, 3);
lean_inc(v_query_938_);
return v_query_938_;
}
default: 
{
lean_object* v___x_939_; 
v___x_939_ = lean_box(0);
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_940_);
lean_dec(v_x_940_);
return v_res_941_;
}
}
lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_942_, uint8_t v_isCrossOrigin_943_, lean_object* v_basePath_944_, lean_object* v_baseQuery_945_, lean_object* v_currentScheme_946_){
_start:
{
lean_object* v___y_948_; lean_object* v___y_949_; 
if (lean_obj_tag(v_ref_942_) == 0)
{
lean_object* v_uri_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v_currentScheme_946_);
lean_dec(v_baseQuery_945_);
lean_dec_ref(v_basePath_944_);
v_uri_952_ = lean_ctor_get(v_ref_942_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_ref_942_);
if (v_isSharedCheck_994_ == 0)
{
v___x_954_ = v_ref_942_;
v_isShared_955_ = v_isSharedCheck_994_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_uri_952_);
lean_dec(v_ref_942_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_994_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_scheme_956_; lean_object* v_authority_957_; lean_object* v_path_958_; lean_object* v_query_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_992_; 
v_scheme_956_ = lean_ctor_get(v_uri_952_, 0);
v_authority_957_ = lean_ctor_get(v_uri_952_, 1);
v_path_958_ = lean_ctor_get(v_uri_952_, 2);
v_query_959_ = lean_ctor_get(v_uri_952_, 3);
v_isSharedCheck_992_ = !lean_is_exclusive(v_uri_952_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_uri_952_, 4);
lean_dec(v_unused_993_);
v___x_961_ = v_uri_952_;
v_isShared_962_ = v_isSharedCheck_992_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_query_959_);
lean_inc(v_path_958_);
lean_inc(v_authority_957_);
lean_inc(v_scheme_956_);
lean_dec(v_uri_952_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_992_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___y_964_; 
if (lean_obj_tag(v_authority_957_) == 0)
{
v___y_964_ = v_authority_957_;
goto v___jp_963_;
}
else
{
lean_object* v_val_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_991_; 
v_val_973_ = lean_ctor_get(v_authority_957_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_authority_957_);
if (v_isSharedCheck_991_ == 0)
{
v___x_975_ = v_authority_957_;
v_isShared_976_ = v_isSharedCheck_991_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_val_973_);
lean_dec(v_authority_957_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_991_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_host_977_; lean_object* v_port_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_989_; 
v_host_977_ = lean_ctor_get(v_val_973_, 1);
v_port_978_ = lean_ctor_get(v_val_973_, 2);
v_isSharedCheck_989_ = !lean_is_exclusive(v_val_973_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_val_973_, 0);
lean_dec(v_unused_990_);
v___x_980_ = v_val_973_;
v_isShared_981_ = v_isSharedCheck_989_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_port_978_);
lean_inc(v_host_977_);
lean_dec(v_val_973_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_989_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_host_977_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_port_978_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_984_);
v___x_986_ = v___x_975_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
v___y_964_ = v___x_986_;
goto v___jp_963_;
}
}
}
}
}
v___jp_963_:
{
if (v_isCrossOrigin_943_ == 0)
{
lean_object* v___x_965_; 
lean_dec(v___y_964_);
lean_del_object(v___x_961_);
lean_dec_ref(v_scheme_956_);
lean_del_object(v___x_954_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_path_958_);
lean_ctor_set(v___x_965_, 1, v_query_959_);
return v___x_965_;
}
else
{
lean_object* v___x_966_; lean_object* v_stripped_968_; 
v___x_966_ = lean_box(0);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 4, v___x_966_);
lean_ctor_set(v___x_961_, 1, v___y_964_);
v_stripped_968_ = v___x_961_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_scheme_956_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___y_964_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_path_958_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_query_959_);
lean_ctor_set(v_reuseFailAlloc_972_, 4, v___x_966_);
v_stripped_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 1);
lean_ctor_set(v___x_954_, 0, v_stripped_968_);
v___x_970_ = v___x_954_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_stripped_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
}
else
{
lean_object* v_ref_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1036_; 
v_ref_995_ = lean_ctor_get(v_ref_942_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_ref_942_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_997_ = v_ref_942_;
v_isShared_998_ = v_isSharedCheck_1036_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_ref_995_);
lean_dec(v_ref_942_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1036_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_authority_999_; lean_object* v_path_1000_; lean_object* v_query_1001_; lean_object* v___y_1003_; uint8_t v___y_1004_; 
v_authority_999_ = lean_ctor_get(v_ref_995_, 0);
lean_inc(v_authority_999_);
v_path_1000_ = lean_ctor_get(v_ref_995_, 1);
lean_inc_ref(v_path_1000_);
v_query_1001_ = lean_ctor_get(v_ref_995_, 2);
lean_inc(v_query_1001_);
lean_dec_ref(v_ref_995_);
if (lean_obj_tag(v_authority_999_) == 0)
{
uint8_t v___x_1005_; lean_object* v___y_1007_; 
lean_del_object(v___x_997_);
lean_dec_ref(v_currentScheme_946_);
v___x_1005_ = l_Std_Http_URI_Path_isEmpty(v_path_1000_);
if (v___x_1005_ == 0)
{
uint8_t v_absolute_1008_; 
v_absolute_1008_ = lean_ctor_get_uint8(v_path_1000_, sizeof(void*)*1);
if (v_absolute_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = l_Std_Http_URI_Path_parent(v_basePath_944_);
v___x_1010_ = l_Std_Http_URI_Path_join(v___x_1009_, v_path_1000_);
lean_dec_ref(v_path_1000_);
v___y_1007_ = v___x_1010_;
goto v___jp_1006_;
}
else
{
lean_dec_ref(v_basePath_944_);
v___y_1007_ = v_path_1000_;
goto v___jp_1006_;
}
}
else
{
lean_dec_ref(v_path_1000_);
v___y_1007_ = v_basePath_944_;
goto v___jp_1006_;
}
v___jp_1006_:
{
if (v___x_1005_ == 0)
{
v___y_1003_ = v___y_1007_;
v___y_1004_ = v___x_1005_;
goto v___jp_1002_;
}
else
{
if (lean_obj_tag(v_query_1001_) == 0)
{
v___y_1003_ = v___y_1007_;
v___y_1004_ = v___x_1005_;
goto v___jp_1002_;
}
else
{
lean_dec(v_baseQuery_945_);
v___y_948_ = v___y_1007_;
v___y_949_ = v_query_1001_;
goto v___jp_947_;
}
}
}
}
else
{
lean_dec(v_baseQuery_945_);
lean_dec_ref(v_basePath_944_);
if (v_isCrossOrigin_943_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref_known(v_authority_999_, 1);
lean_del_object(v___x_997_);
lean_dec_ref(v_currentScheme_946_);
v___x_1011_ = l_Std_Http_URI_Path_normalize(v_path_1000_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_query_1001_);
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1035_; 
v_val_1013_ = lean_ctor_get(v_authority_999_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_authority_999_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1015_ = v_authority_999_;
v_isShared_1016_ = v_isSharedCheck_1035_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_val_1013_);
lean_dec(v_authority_999_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1035_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v_host_1017_; lean_object* v_port_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1033_; 
v_host_1017_ = lean_ctor_get(v_val_1013_, 1);
v_port_1018_ = lean_ctor_get(v_val_1013_, 2);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_val_1013_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_val_1013_, 0);
lean_dec(v_unused_1034_);
v___x_1020_ = v_val_1013_;
v_isShared_1021_ = v_isSharedCheck_1033_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_port_1018_);
lean_inc(v_host_1017_);
lean_dec(v_val_1013_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1033_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v_stripped_1024_; 
v___x_1022_ = lean_box(0);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1022_);
v_stripped_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_host_1017_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_port_1018_);
v_stripped_1024_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v_stripped_1024_);
v___x_1026_ = v___x_1015_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_stripped_1024_);
v___x_1026_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v_af_1027_; lean_object* v___x_1029_; 
v_af_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_1027_, 0, v_currentScheme_946_);
lean_ctor_set(v_af_1027_, 1, v___x_1026_);
lean_ctor_set(v_af_1027_, 2, v_path_1000_);
lean_ctor_set(v_af_1027_, 3, v_query_1001_);
lean_ctor_set(v_af_1027_, 4, v___x_1022_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_af_1027_);
v___x_1029_ = v___x_997_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_af_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
}
v___jp_1002_:
{
if (v___y_1004_ == 0)
{
lean_dec(v_baseQuery_945_);
v___y_948_ = v___y_1003_;
v___y_949_ = v_query_1001_;
goto v___jp_947_;
}
else
{
lean_dec(v_query_1001_);
v___y_948_ = v___y_1003_;
v___y_949_ = v_baseQuery_945_;
goto v___jp_947_;
}
}
}
}
v___jp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = l_Std_Http_URI_Path_normalize(v___y_948_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___y_949_);
return v___x_951_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_942_ = stack[0].m_obj;
uint8_t v_isCrossOrigin_943_ = stack[1].m_num;
lean_object* v_basePath_944_ = stack[2].m_obj;
lean_object* v_baseQuery_945_ = stack[3].m_obj;
lean_object* v_currentScheme_946_ = stack[4].m_obj;
lean_object* v_res_1037_;
v_res_1037_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_942_, v_isCrossOrigin_943_, v_basePath_944_, v_baseQuery_945_, v_currentScheme_946_);
stack->m_obj
 = v_res_1037_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_1038_, lean_object* v_isCrossOrigin_1039_, lean_object* v_basePath_1040_, lean_object* v_baseQuery_1041_, lean_object* v_currentScheme_1042_){
_start:
{
uint8_t v_isCrossOrigin_boxed_1043_; lean_object* v_res_1044_; 
v_isCrossOrigin_boxed_1043_ = lean_unbox(v_isCrossOrigin_1039_);
v_res_1044_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_1038_, v_isCrossOrigin_boxed_1043_, v_basePath_1040_, v_baseQuery_1041_, v_currentScheme_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_Http_URI_Parser_parseURIReference(v___x_1048_, v___y_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_pos_1051_; lean_object* v_array_1052_; lean_object* v_idx_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_pos_1051_ = lean_ctor_get(v___x_1050_, 0);
v_array_1052_ = lean_ctor_get(v_pos_1051_, 0);
v_idx_1053_ = lean_ctor_get(v_pos_1051_, 1);
v___x_1054_ = lean_byte_array_size(v_array_1052_);
v___x_1055_ = lean_nat_dec_lt(v_idx_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
return v___x_1050_;
}
else
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1063_; 
lean_inc(v_pos_1051_);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; lean_object* v_unused_1065_; 
v_unused_1064_ = lean_ctor_get(v___x_1050_, 1);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v___x_1050_, 0);
lean_dec(v_unused_1065_);
v___x_1057_ = v___x_1050_;
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v___x_1050_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 1);
lean_ctor_set(v___x_1057_, 1, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_pos_1051_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
return v___x_1050_;
}
}
}
lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_1078_, lean_object* v_request_1079_, uint8_t v_bodyReplayable_1080_, uint8_t v_onlySafeRedirects_1081_, uint8_t v_responseVersion_1082_, lean_object* v_status_1083_, lean_object* v_responseHeaders_1084_){
_start:
{
lean_object* v___y_1086_; uint8_t v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1100_; uint8_t v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; uint8_t v___y_1105_; lean_object* v___y_1108_; uint8_t v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; uint8_t v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1121_; uint8_t v___y_1122_; uint8_t v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; uint8_t v___y_1127_; uint8_t v___y_1128_; uint8_t v___y_1129_; lean_object* v___y_1133_; uint8_t v___y_1134_; uint8_t v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; uint8_t v___y_1139_; uint8_t v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1145_; uint8_t v___y_1146_; uint8_t v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; uint8_t v___y_1151_; uint8_t v___y_1152_; uint8_t v___y_1153_; uint8_t v___y_1154_; lean_object* v___y_1157_; uint8_t v___y_1158_; uint8_t v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; uint8_t v___y_1162_; uint8_t v___y_1163_; uint8_t v___y_1164_; uint8_t v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1168_; uint8_t v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; uint8_t v___y_1173_; lean_object* v___y_1174_; uint8_t v___y_1175_; uint8_t v___y_1176_; uint8_t v___y_1177_; lean_object* v___y_1181_; uint8_t v___y_1182_; uint8_t v___y_1183_; uint8_t v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1188_; uint8_t v___y_1189_; uint8_t v___y_1190_; uint8_t v___y_1191_; uint8_t v___y_1192_; lean_object* v___y_1196_; uint8_t v___y_1197_; uint8_t v___y_1198_; uint8_t v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; uint8_t v___y_1203_; lean_object* v___y_1204_; uint8_t v___y_1205_; uint8_t v___y_1206_; uint8_t v___y_1207_; lean_object* v___y_1209_; uint8_t v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; uint8_t v___y_1215_; uint8_t v___y_1216_; uint8_t v___y_1217_; uint8_t v___y_1218_; uint8_t v___y_1219_; lean_object* v___y_1223_; uint8_t v___y_1224_; uint8_t v___y_1225_; uint8_t v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; uint8_t v___y_1232_; uint8_t v___y_1233_; lean_object* v___y_1235_; uint8_t v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1238_; uint8_t v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; uint8_t v___y_1243_; uint8_t v___y_1244_; uint8_t v___y_1245_; uint8_t v___y_1246_; uint16_t v___x_1249_; uint16_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = 300;
v___x_1250_ = l_Std_Http_Status_toCode(v_status_1083_);
v___x_1251_ = lean_uint16_dec_le(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v_current_1078_);
v___x_1252_ = lean_box(0);
return v___x_1252_;
}
else
{
uint16_t v___x_1253_; uint8_t v___x_1254_; lean_object* v___y_1256_; uint8_t v___y_1257_; uint8_t v___y_1258_; lean_object* v___y_1259_; uint8_t v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; uint8_t v___y_1263_; uint8_t v___y_1264_; uint8_t v___y_1265_; lean_object* v___y_1271_; uint8_t v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; uint8_t v___y_1277_; uint8_t v___y_1278_; uint8_t v___y_1279_; lean_object* v___y_1282_; lean_object* v___y_1283_; uint8_t v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; uint8_t v___y_1287_; uint8_t v___y_1288_; uint8_t v___y_1289_; 
v___x_1253_ = 400;
v___x_1254_ = lean_uint16_dec_lt(v___x_1250_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1291_; 
lean_dec_ref(v_current_1078_);
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
else
{
uint8_t v___x_1292_; lean_object* v___y_1294_; uint8_t v___y_1295_; lean_object* v___y_1296_; uint8_t v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; uint8_t v___y_1300_; uint8_t v___y_1301_; uint8_t v___y_1302_; uint8_t v___y_1309_; uint8_t v___x_1352_; uint8_t v___x_1353_; 
v___x_1292_ = 0;
v___x_1352_ = 0;
v___x_1353_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_1082_, v___x_1352_);
if (v___x_1353_ == 0)
{
goto v___jp_1335_;
}
else
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = lean_box(15);
v___x_1355_ = l_Std_Http_instBEqStatus_beq(v_status_1083_, v___x_1354_);
if (v___x_1355_ == 0)
{
if (v___x_1353_ == 0)
{
goto v___jp_1335_;
}
else
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = lean_box(16);
v___x_1357_ = l_Std_Http_instBEqStatus_beq(v_status_1083_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref(v_current_1078_);
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
else
{
goto v___jp_1335_;
}
}
}
else
{
goto v___jp_1335_;
}
}
v___jp_1293_:
{
if (v___y_1302_ == 0)
{
v___y_1282_ = v___y_1294_;
v___y_1283_ = v___y_1296_;
v___y_1284_ = v___y_1297_;
v___y_1285_ = v___y_1298_;
v___y_1286_ = v___y_1299_;
v___y_1287_ = v___y_1301_;
v___y_1288_ = v___y_1300_;
v___y_1289_ = v___x_1292_;
goto v___jp_1281_;
}
else
{
lean_object* v_scheme_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_scheme_1303_ = lean_ctor_get(v___y_1294_, 0);
v___x_1304_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__0));
v___x_1305_ = lean_string_dec_eq(v_scheme_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec_ref(v___y_1296_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_current_1078_);
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
else
{
if (v___y_1295_ == 0)
{
v___y_1282_ = v___y_1294_;
v___y_1283_ = v___y_1296_;
v___y_1284_ = v___y_1297_;
v___y_1285_ = v___y_1298_;
v___y_1286_ = v___y_1299_;
v___y_1287_ = v___y_1301_;
v___y_1288_ = v___y_1300_;
v___y_1289_ = v___y_1295_;
goto v___jp_1281_;
}
else
{
lean_object* v___x_1307_; 
lean_dec_ref(v___y_1296_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_current_1078_);
v___x_1307_ = lean_box(0);
return v___x_1307_;
}
}
}
}
v___jp_1308_:
{
lean_object* v_entries_1310_; lean_object* v_indexes_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_entries_1310_ = lean_ctor_get(v_responseHeaders_1084_, 0);
v_indexes_1311_ = lean_ctor_get(v_responseHeaders_1084_, 1);
v___x_1312_ = l_Std_Http_Header_Name_location;
v___x_1313_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v_current_1078_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_entry_1317_; lean_object* v___x_1318_; lean_object* v_snd_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_1311_, v___x_1312_);
v___x_1316_ = lean_unsigned_to_nat(0u);
v_entry_1317_ = lean_array_fget(v___x_1315_, v___x_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_array_fget_borrowed(v_entries_1310_, v_entry_1317_);
lean_dec(v_entry_1317_);
v_snd_1319_ = lean_ctor_get(v___x_1318_, 1);
v___f_1320_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
v___x_1321_ = lean_string_to_utf8(v_snd_1319_);
v___x_1322_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1320_, v___x_1321_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1323_; 
lean_dec_ref_known(v___x_1322_, 1);
lean_dec_ref(v_current_1078_);
v___x_1323_ = lean_box(0);
return v___x_1323_;
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1325_; 
v_a_1324_ = lean_ctor_get(v___x_1322_, 0);
lean_inc_n(v_a_1324_, 2);
lean_dec_ref_known(v___x_1322_, 1);
lean_inc_ref(v_current_1078_);
v___x_1325_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_1078_, v_a_1324_);
if (lean_obj_tag(v___x_1325_) == 1)
{
lean_object* v_val_1326_; uint8_t v_method_1327_; lean_object* v_uri_1328_; lean_object* v_headers_1329_; lean_object* v_scheme_1330_; uint8_t v_newMethod_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_val_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v_method_1327_ = lean_ctor_get_uint8(v_request_1079_, sizeof(void*)*2);
v_uri_1328_ = lean_ctor_get(v_request_1079_, 0);
v_headers_1329_ = lean_ctor_get(v_request_1079_, 1);
v_scheme_1330_ = lean_ctor_get(v_val_1326_, 0);
v_newMethod_1331_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_1327_, v_responseVersion_1082_, v_status_1083_);
v___x_1332_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_1333_ = lean_string_dec_eq(v_scheme_1330_, v___x_1332_);
if (v___x_1333_ == 0)
{
v___y_1294_ = v_val_1326_;
v___y_1295_ = v___y_1309_;
v___y_1296_ = v_a_1324_;
v___y_1297_ = v_method_1327_;
v___y_1298_ = v_uri_1328_;
v___y_1299_ = v_headers_1329_;
v___y_1300_ = v___x_1313_;
v___y_1301_ = v_newMethod_1331_;
v___y_1302_ = v___x_1313_;
goto v___jp_1293_;
}
else
{
v___y_1294_ = v_val_1326_;
v___y_1295_ = v___y_1309_;
v___y_1296_ = v_a_1324_;
v___y_1297_ = v_method_1327_;
v___y_1298_ = v_uri_1328_;
v___y_1299_ = v_headers_1329_;
v___y_1300_ = v___x_1313_;
v___y_1301_ = v_newMethod_1331_;
v___y_1302_ = v___y_1309_;
goto v___jp_1293_;
}
}
else
{
lean_object* v___x_1334_; 
lean_dec(v___x_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_current_1078_);
v___x_1334_ = lean_box(0);
return v___x_1334_;
}
}
}
}
v___jp_1335_:
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_box(19);
v___x_1337_ = l_Std_Http_instBEqStatus_beq(v_status_1083_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = lean_box(20);
v___x_1339_ = l_Std_Http_instBEqStatus_beq(v_status_1083_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_box(18);
v___x_1341_ = l_Std_Http_instBEqStatus_beq(v_status_1083_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = lean_box(14);
v___x_1343_ = l_Std_Http_instBEqStatus_beq(v_status_1083_, v___x_1342_);
if (v___x_1343_ == 0)
{
if (v_onlySafeRedirects_1081_ == 0)
{
v___y_1309_ = v___x_1292_;
goto v___jp_1308_;
}
else
{
uint8_t v_method_1344_; uint8_t v___x_1345_; 
v_method_1344_ = lean_ctor_get_uint8(v_request_1079_, sizeof(void*)*2);
v___x_1345_ = l_Std_Http_Method_isSafe(v_method_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref(v_current_1078_);
v___x_1346_ = lean_box(0);
return v___x_1346_;
}
else
{
if (v___x_1343_ == 0)
{
v___y_1309_ = v___x_1343_;
goto v___jp_1308_;
}
else
{
lean_object* v___x_1347_; 
lean_dec_ref(v_current_1078_);
v___x_1347_ = lean_box(0);
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v_current_1078_);
v___x_1348_ = lean_box(0);
return v___x_1348_;
}
}
else
{
lean_object* v___x_1349_; 
lean_dec_ref(v_current_1078_);
v___x_1349_ = lean_box(0);
return v___x_1349_;
}
}
else
{
lean_object* v___x_1350_; 
lean_dec_ref(v_current_1078_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
}
else
{
lean_object* v___x_1351_; 
lean_dec_ref(v_current_1078_);
v___x_1351_ = lean_box(0);
return v___x_1351_;
}
}
}
v___jp_1255_:
{
uint8_t v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = 8;
v___x_1267_ = l_Std_Http_instBEqMethod_beq(v___y_1260_, v___x_1266_);
if (v___x_1267_ == 0)
{
uint8_t v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = 9;
v___x_1269_ = l_Std_Http_instBEqMethod_beq(v___y_1260_, v___x_1268_);
v___y_1235_ = v___y_1256_;
v___y_1236_ = v___y_1257_;
v___y_1237_ = v___y_1258_;
v___y_1238_ = v___y_1259_;
v___y_1239_ = v___y_1260_;
v___y_1240_ = v___y_1261_;
v___y_1241_ = v___y_1262_;
v___y_1242_ = v___x_1266_;
v___y_1243_ = v___y_1265_;
v___y_1244_ = v___y_1264_;
v___y_1245_ = v___y_1263_;
v___y_1246_ = v___x_1269_;
goto v___jp_1234_;
}
else
{
v___y_1235_ = v___y_1256_;
v___y_1236_ = v___y_1257_;
v___y_1237_ = v___y_1258_;
v___y_1238_ = v___y_1259_;
v___y_1239_ = v___y_1260_;
v___y_1240_ = v___y_1261_;
v___y_1241_ = v___y_1262_;
v___y_1242_ = v___x_1266_;
v___y_1243_ = v___y_1265_;
v___y_1244_ = v___y_1264_;
v___y_1245_ = v___y_1263_;
v___y_1246_ = v___x_1254_;
goto v___jp_1234_;
}
}
v___jp_1270_:
{
uint8_t v___x_1280_; 
v___x_1280_ = l_Std_Http_instBEqMethod_beq(v___y_1278_, v___y_1274_);
if (v___x_1280_ == 0)
{
v___y_1256_ = v___y_1271_;
v___y_1257_ = v___y_1279_;
v___y_1258_ = v___y_1272_;
v___y_1259_ = v___y_1273_;
v___y_1260_ = v___y_1274_;
v___y_1261_ = v___y_1275_;
v___y_1262_ = v___y_1276_;
v___y_1263_ = v___y_1278_;
v___y_1264_ = v___y_1277_;
v___y_1265_ = v___y_1277_;
goto v___jp_1255_;
}
else
{
v___y_1256_ = v___y_1271_;
v___y_1257_ = v___y_1279_;
v___y_1258_ = v___y_1272_;
v___y_1259_ = v___y_1273_;
v___y_1260_ = v___y_1274_;
v___y_1261_ = v___y_1275_;
v___y_1262_ = v___y_1276_;
v___y_1263_ = v___y_1278_;
v___y_1264_ = v___y_1277_;
v___y_1265_ = v___y_1272_;
goto v___jp_1255_;
}
}
v___jp_1281_:
{
uint8_t v___x_1290_; 
v___x_1290_ = l_Std_Http_URI_instBEqOrigin_beq(v___y_1282_, v_current_1078_);
if (v___x_1290_ == 0)
{
v___y_1271_ = v___y_1282_;
v___y_1272_ = v___y_1289_;
v___y_1273_ = v___y_1283_;
v___y_1274_ = v___y_1284_;
v___y_1275_ = v___y_1285_;
v___y_1276_ = v___y_1286_;
v___y_1277_ = v___y_1288_;
v___y_1278_ = v___y_1287_;
v___y_1279_ = v___y_1288_;
goto v___jp_1270_;
}
else
{
v___y_1271_ = v___y_1282_;
v___y_1272_ = v___y_1289_;
v___y_1273_ = v___y_1283_;
v___y_1274_ = v___y_1284_;
v___y_1275_ = v___y_1285_;
v___y_1276_ = v___y_1286_;
v___y_1277_ = v___y_1288_;
v___y_1278_ = v___y_1287_;
v___y_1279_ = v___y_1289_;
goto v___jp_1270_;
}
}
}
v___jp_1085_:
{
lean_object* v_scheme_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_rewrittenTarget_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_scheme_1093_ = lean_ctor_get(v_current_1078_, 0);
lean_inc_ref(v_scheme_1093_);
lean_dec_ref(v_current_1078_);
v___x_1094_ = l_Std_Http_RequestTarget_pathOrRoot(v___y_1090_);
v___x_1095_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v___y_1090_);
v_rewrittenTarget_1096_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v___y_1088_, v___y_1087_, v___x_1094_, v___x_1095_, v_scheme_1093_);
v___x_1097_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1097_, 0, v___y_1086_);
lean_ctor_set(v___x_1097_, 1, v_rewrittenTarget_1096_);
lean_ctor_set(v___x_1097_, 2, v___y_1089_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*3, v___y_1091_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*3 + 1, v___y_1092_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*3 + 2, v___y_1087_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
v___jp_1099_:
{
uint8_t v___x_1106_; 
v___x_1106_ = 0;
v___y_1086_ = v___y_1100_;
v___y_1087_ = v___y_1101_;
v___y_1088_ = v___y_1102_;
v___y_1089_ = v___y_1104_;
v___y_1090_ = v___y_1103_;
v___y_1091_ = v___y_1105_;
v___y_1092_ = v___x_1106_;
goto v___jp_1085_;
}
v___jp_1107_:
{
uint8_t v___x_1116_; 
v___x_1116_ = l_Std_Http_instBEqMethod_beq(v___y_1115_, v___y_1113_);
if (v___x_1116_ == 0)
{
uint8_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = 9;
v___x_1118_ = l_Std_Http_instBEqMethod_beq(v___y_1115_, v___x_1117_);
if (v___x_1118_ == 0)
{
if (v___y_1114_ == 0)
{
uint8_t v___x_1119_; 
v___x_1119_ = 1;
v___y_1086_ = v___y_1108_;
v___y_1087_ = v___y_1109_;
v___y_1088_ = v___y_1110_;
v___y_1089_ = v___y_1112_;
v___y_1090_ = v___y_1111_;
v___y_1091_ = v___y_1115_;
v___y_1092_ = v___x_1119_;
goto v___jp_1085_;
}
else
{
v___y_1100_ = v___y_1108_;
v___y_1101_ = v___y_1109_;
v___y_1102_ = v___y_1110_;
v___y_1103_ = v___y_1111_;
v___y_1104_ = v___y_1112_;
v___y_1105_ = v___y_1115_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___y_1108_;
v___y_1101_ = v___y_1109_;
v___y_1102_ = v___y_1110_;
v___y_1103_ = v___y_1111_;
v___y_1104_ = v___y_1112_;
v___y_1105_ = v___y_1115_;
goto v___jp_1099_;
}
}
else
{
v___y_1100_ = v___y_1108_;
v___y_1101_ = v___y_1109_;
v___y_1102_ = v___y_1110_;
v___y_1103_ = v___y_1111_;
v___y_1104_ = v___y_1112_;
v___y_1105_ = v___y_1115_;
goto v___jp_1099_;
}
}
v___jp_1120_:
{
if (v_bodyReplayable_1080_ == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v_current_1078_);
v___x_1130_ = lean_box(0);
return v___x_1130_;
}
else
{
if (v___y_1123_ == 0)
{
v___y_1108_ = v___y_1121_;
v___y_1109_ = v___y_1122_;
v___y_1110_ = v___y_1124_;
v___y_1111_ = v___y_1126_;
v___y_1112_ = v___y_1125_;
v___y_1113_ = v___y_1127_;
v___y_1114_ = v___y_1128_;
v___y_1115_ = v___y_1129_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1131_; 
lean_dec_ref(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v_current_1078_);
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
}
}
v___jp_1132_:
{
uint8_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = 9;
v___x_1143_ = l_Std_Http_instBEqMethod_beq(v___y_1141_, v___x_1142_);
if (v___x_1143_ == 0)
{
v___y_1121_ = v___y_1133_;
v___y_1122_ = v___y_1134_;
v___y_1123_ = v___y_1135_;
v___y_1124_ = v___y_1136_;
v___y_1125_ = v___y_1138_;
v___y_1126_ = v___y_1137_;
v___y_1127_ = v___y_1139_;
v___y_1128_ = v___y_1140_;
v___y_1129_ = v___y_1141_;
goto v___jp_1120_;
}
else
{
if (v___y_1135_ == 0)
{
v___y_1108_ = v___y_1133_;
v___y_1109_ = v___y_1134_;
v___y_1110_ = v___y_1136_;
v___y_1111_ = v___y_1137_;
v___y_1112_ = v___y_1138_;
v___y_1113_ = v___y_1139_;
v___y_1114_ = v___y_1140_;
v___y_1115_ = v___y_1141_;
goto v___jp_1107_;
}
else
{
v___y_1121_ = v___y_1133_;
v___y_1122_ = v___y_1134_;
v___y_1123_ = v___y_1135_;
v___y_1124_ = v___y_1136_;
v___y_1125_ = v___y_1138_;
v___y_1126_ = v___y_1137_;
v___y_1127_ = v___y_1139_;
v___y_1128_ = v___y_1140_;
v___y_1129_ = v___y_1141_;
goto v___jp_1120_;
}
}
}
v___jp_1144_:
{
if (v___y_1154_ == 0)
{
v___y_1108_ = v___y_1145_;
v___y_1109_ = v___y_1146_;
v___y_1110_ = v___y_1148_;
v___y_1111_ = v___y_1150_;
v___y_1112_ = v___y_1149_;
v___y_1113_ = v___y_1151_;
v___y_1114_ = v___y_1152_;
v___y_1115_ = v___y_1153_;
goto v___jp_1107_;
}
else
{
uint8_t v___x_1155_; 
v___x_1155_ = l_Std_Http_instBEqMethod_beq(v___y_1153_, v___y_1151_);
if (v___x_1155_ == 0)
{
v___y_1133_ = v___y_1145_;
v___y_1134_ = v___y_1146_;
v___y_1135_ = v___y_1147_;
v___y_1136_ = v___y_1148_;
v___y_1137_ = v___y_1150_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1151_;
v___y_1140_ = v___y_1152_;
v___y_1141_ = v___y_1153_;
goto v___jp_1132_;
}
else
{
if (v___y_1147_ == 0)
{
v___y_1108_ = v___y_1145_;
v___y_1109_ = v___y_1146_;
v___y_1110_ = v___y_1148_;
v___y_1111_ = v___y_1150_;
v___y_1112_ = v___y_1149_;
v___y_1113_ = v___y_1151_;
v___y_1114_ = v___y_1152_;
v___y_1115_ = v___y_1153_;
goto v___jp_1107_;
}
else
{
v___y_1133_ = v___y_1145_;
v___y_1134_ = v___y_1146_;
v___y_1135_ = v___y_1147_;
v___y_1136_ = v___y_1148_;
v___y_1137_ = v___y_1150_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1151_;
v___y_1140_ = v___y_1152_;
v___y_1141_ = v___y_1153_;
goto v___jp_1132_;
}
}
}
}
v___jp_1156_:
{
if (v___y_1163_ == 0)
{
v___y_1145_ = v___y_1157_;
v___y_1146_ = v___y_1158_;
v___y_1147_ = v___y_1159_;
v___y_1148_ = v___y_1160_;
v___y_1149_ = v___y_1166_;
v___y_1150_ = v___y_1161_;
v___y_1151_ = v___y_1162_;
v___y_1152_ = v___y_1163_;
v___y_1153_ = v___y_1165_;
v___y_1154_ = v___y_1164_;
goto v___jp_1144_;
}
else
{
v___y_1145_ = v___y_1157_;
v___y_1146_ = v___y_1158_;
v___y_1147_ = v___y_1159_;
v___y_1148_ = v___y_1160_;
v___y_1149_ = v___y_1166_;
v___y_1150_ = v___y_1161_;
v___y_1151_ = v___y_1162_;
v___y_1152_ = v___y_1163_;
v___y_1153_ = v___y_1165_;
v___y_1154_ = v___y_1159_;
goto v___jp_1144_;
}
}
v___jp_1167_:
{
lean_object* v_scrubbed_1178_; 
v_scrubbed_1178_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v___y_1174_, v___y_1169_, v___y_1175_);
if (v___y_1169_ == 0)
{
v___y_1157_ = v___y_1168_;
v___y_1158_ = v___y_1169_;
v___y_1159_ = v___y_1170_;
v___y_1160_ = v___y_1171_;
v___y_1161_ = v___y_1172_;
v___y_1162_ = v___y_1173_;
v___y_1163_ = v___y_1175_;
v___y_1164_ = v___y_1177_;
v___y_1165_ = v___y_1176_;
v___y_1166_ = v_scrubbed_1178_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1179_; 
lean_inc_ref(v___y_1168_);
v___x_1179_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_1178_, v___y_1168_);
v___y_1157_ = v___y_1168_;
v___y_1158_ = v___y_1169_;
v___y_1159_ = v___y_1170_;
v___y_1160_ = v___y_1171_;
v___y_1161_ = v___y_1172_;
v___y_1162_ = v___y_1173_;
v___y_1163_ = v___y_1175_;
v___y_1164_ = v___y_1177_;
v___y_1165_ = v___y_1176_;
v___y_1166_ = v___x_1179_;
goto v___jp_1156_;
}
}
v___jp_1180_:
{
if (v___y_1192_ == 0)
{
v___y_1168_ = v___y_1181_;
v___y_1169_ = v___y_1183_;
v___y_1170_ = v___y_1184_;
v___y_1171_ = v___y_1185_;
v___y_1172_ = v___y_1186_;
v___y_1173_ = v___y_1188_;
v___y_1174_ = v___y_1187_;
v___y_1175_ = v___y_1189_;
v___y_1176_ = v___y_1191_;
v___y_1177_ = v___y_1190_;
goto v___jp_1167_;
}
else
{
if (v___y_1182_ == 0)
{
lean_object* v___x_1193_; 
lean_dec_ref(v___y_1185_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_current_1078_);
v___x_1193_ = lean_box(0);
return v___x_1193_;
}
else
{
if (v___y_1184_ == 0)
{
v___y_1168_ = v___y_1181_;
v___y_1169_ = v___y_1183_;
v___y_1170_ = v___y_1184_;
v___y_1171_ = v___y_1185_;
v___y_1172_ = v___y_1186_;
v___y_1173_ = v___y_1188_;
v___y_1174_ = v___y_1187_;
v___y_1175_ = v___y_1189_;
v___y_1176_ = v___y_1191_;
v___y_1177_ = v___y_1190_;
goto v___jp_1167_;
}
else
{
lean_object* v___x_1194_; 
lean_dec_ref(v___y_1185_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_current_1078_);
v___x_1194_ = lean_box(0);
return v___x_1194_;
}
}
}
}
v___jp_1195_:
{
if (v___y_1197_ == 0)
{
v___y_1181_ = v___y_1196_;
v___y_1182_ = v___y_1198_;
v___y_1183_ = v___y_1199_;
v___y_1184_ = v___y_1200_;
v___y_1185_ = v___y_1201_;
v___y_1186_ = v___y_1202_;
v___y_1187_ = v___y_1204_;
v___y_1188_ = v___y_1203_;
v___y_1189_ = v___y_1205_;
v___y_1190_ = v___y_1207_;
v___y_1191_ = v___y_1206_;
v___y_1192_ = v___y_1207_;
goto v___jp_1180_;
}
else
{
v___y_1181_ = v___y_1196_;
v___y_1182_ = v___y_1198_;
v___y_1183_ = v___y_1199_;
v___y_1184_ = v___y_1200_;
v___y_1185_ = v___y_1201_;
v___y_1186_ = v___y_1202_;
v___y_1187_ = v___y_1204_;
v___y_1188_ = v___y_1203_;
v___y_1189_ = v___y_1205_;
v___y_1190_ = v___y_1207_;
v___y_1191_ = v___y_1206_;
v___y_1192_ = v___y_1200_;
goto v___jp_1180_;
}
}
v___jp_1208_:
{
if (v___y_1219_ == 0)
{
v___y_1168_ = v___y_1209_;
v___y_1169_ = v___y_1210_;
v___y_1170_ = v___y_1211_;
v___y_1171_ = v___y_1212_;
v___y_1172_ = v___y_1213_;
v___y_1173_ = v___y_1215_;
v___y_1174_ = v___y_1214_;
v___y_1175_ = v___y_1216_;
v___y_1176_ = v___y_1218_;
v___y_1177_ = v___y_1217_;
goto v___jp_1167_;
}
else
{
if (v_bodyReplayable_1080_ == 0)
{
lean_object* v___x_1220_; 
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v_current_1078_);
v___x_1220_ = lean_box(0);
return v___x_1220_;
}
else
{
if (v___y_1211_ == 0)
{
v___y_1168_ = v___y_1209_;
v___y_1169_ = v___y_1210_;
v___y_1170_ = v___y_1211_;
v___y_1171_ = v___y_1212_;
v___y_1172_ = v___y_1213_;
v___y_1173_ = v___y_1215_;
v___y_1174_ = v___y_1214_;
v___y_1175_ = v___y_1216_;
v___y_1176_ = v___y_1218_;
v___y_1177_ = v___y_1217_;
goto v___jp_1167_;
}
else
{
lean_object* v___x_1221_; 
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v_current_1078_);
v___x_1221_ = lean_box(0);
return v___x_1221_;
}
}
}
}
v___jp_1222_:
{
if (v___y_1224_ == 0)
{
v___y_1209_ = v___y_1223_;
v___y_1210_ = v___y_1225_;
v___y_1211_ = v___y_1226_;
v___y_1212_ = v___y_1227_;
v___y_1213_ = v___y_1228_;
v___y_1214_ = v___y_1230_;
v___y_1215_ = v___y_1229_;
v___y_1216_ = v___y_1231_;
v___y_1217_ = v___y_1233_;
v___y_1218_ = v___y_1232_;
v___y_1219_ = v___y_1233_;
goto v___jp_1208_;
}
else
{
v___y_1209_ = v___y_1223_;
v___y_1210_ = v___y_1225_;
v___y_1211_ = v___y_1226_;
v___y_1212_ = v___y_1227_;
v___y_1213_ = v___y_1228_;
v___y_1214_ = v___y_1230_;
v___y_1215_ = v___y_1229_;
v___y_1216_ = v___y_1231_;
v___y_1217_ = v___y_1233_;
v___y_1218_ = v___y_1232_;
v___y_1219_ = v___y_1226_;
goto v___jp_1208_;
}
}
v___jp_1234_:
{
uint8_t v___x_1247_; uint8_t v_isPost_1248_; 
v___x_1247_ = 23;
v_isPost_1248_ = l_Std_Http_instBEqMethod_beq(v___y_1239_, v___x_1247_);
switch(lean_obj_tag(v_status_1083_))
{
case 15:
{
v___y_1196_ = v___y_1235_;
v___y_1197_ = v___y_1246_;
v___y_1198_ = v_isPost_1248_;
v___y_1199_ = v___y_1236_;
v___y_1200_ = v___y_1237_;
v___y_1201_ = v___y_1238_;
v___y_1202_ = v___y_1240_;
v___y_1203_ = v___y_1242_;
v___y_1204_ = v___y_1241_;
v___y_1205_ = v___y_1243_;
v___y_1206_ = v___y_1245_;
v___y_1207_ = v___y_1244_;
goto v___jp_1195_;
}
case 16:
{
v___y_1196_ = v___y_1235_;
v___y_1197_ = v___y_1246_;
v___y_1198_ = v_isPost_1248_;
v___y_1199_ = v___y_1236_;
v___y_1200_ = v___y_1237_;
v___y_1201_ = v___y_1238_;
v___y_1202_ = v___y_1240_;
v___y_1203_ = v___y_1242_;
v___y_1204_ = v___y_1241_;
v___y_1205_ = v___y_1243_;
v___y_1206_ = v___y_1245_;
v___y_1207_ = v___y_1244_;
goto v___jp_1195_;
}
case 21:
{
v___y_1223_ = v___y_1235_;
v___y_1224_ = v___y_1246_;
v___y_1225_ = v___y_1236_;
v___y_1226_ = v___y_1237_;
v___y_1227_ = v___y_1238_;
v___y_1228_ = v___y_1240_;
v___y_1229_ = v___y_1242_;
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1243_;
v___y_1232_ = v___y_1245_;
v___y_1233_ = v___y_1244_;
goto v___jp_1222_;
}
case 22:
{
v___y_1223_ = v___y_1235_;
v___y_1224_ = v___y_1246_;
v___y_1225_ = v___y_1236_;
v___y_1226_ = v___y_1237_;
v___y_1227_ = v___y_1238_;
v___y_1228_ = v___y_1240_;
v___y_1229_ = v___y_1242_;
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1243_;
v___y_1232_ = v___y_1245_;
v___y_1233_ = v___y_1244_;
goto v___jp_1222_;
}
default: 
{
v___y_1168_ = v___y_1235_;
v___y_1169_ = v___y_1236_;
v___y_1170_ = v___y_1237_;
v___y_1171_ = v___y_1238_;
v___y_1172_ = v___y_1240_;
v___y_1173_ = v___y_1242_;
v___y_1174_ = v___y_1241_;
v___y_1175_ = v___y_1243_;
v___y_1176_ = v___y_1245_;
v___y_1177_ = v___y_1244_;
goto v___jp_1167_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_decideRedirect_0interp(lean_interpreter_value* stack)
{
lean_object* v_current_1078_ = stack[0].m_obj;
lean_object* v_request_1079_ = stack[1].m_obj;
uint8_t v_bodyReplayable_1080_ = stack[2].m_num;
uint8_t v_onlySafeRedirects_1081_ = stack[3].m_num;
uint8_t v_responseVersion_1082_ = stack[4].m_num;
lean_object* v_status_1083_ = stack[5].m_obj;
lean_object* v_responseHeaders_1084_ = stack[6].m_obj;
lean_object* v_res_1359_;
v_res_1359_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1078_, v_request_1079_, v_bodyReplayable_1080_, v_onlySafeRedirects_1081_, v_responseVersion_1082_, v_status_1083_, v_responseHeaders_1084_);
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_1360_, lean_object* v_request_1361_, lean_object* v_bodyReplayable_1362_, lean_object* v_onlySafeRedirects_1363_, lean_object* v_responseVersion_1364_, lean_object* v_status_1365_, lean_object* v_responseHeaders_1366_){
_start:
{
uint8_t v_bodyReplayable_boxed_1367_; uint8_t v_onlySafeRedirects_boxed_1368_; uint8_t v_responseVersion_boxed_1369_; lean_object* v_res_1370_; 
v_bodyReplayable_boxed_1367_ = lean_unbox(v_bodyReplayable_1362_);
v_onlySafeRedirects_boxed_1368_ = lean_unbox(v_onlySafeRedirects_1363_);
v_responseVersion_boxed_1369_ = lean_unbox(v_responseVersion_1364_);
v_res_1370_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1360_, v_request_1361_, v_bodyReplayable_boxed_1367_, v_onlySafeRedirects_boxed_1368_, v_responseVersion_boxed_1369_, v_status_1365_, v_responseHeaders_1366_);
lean_dec_ref(v_responseHeaders_1366_);
lean_dec(v_status_1365_);
lean_dec_ref(v_request_1361_);
return v_res_1370_;
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
