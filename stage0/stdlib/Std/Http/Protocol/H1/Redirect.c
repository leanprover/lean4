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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(v_x_4__boxed_5_);
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
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_58_ = lean_box(v_x_56_);
v___x_59_ = lean_obj_tag_nat(v___x_58_);
lean_dec(v___x_58_);
v___x_60_ = lean_box(v_y_57_);
v___x_61_ = lean_obj_tag_nat(v___x_60_);
lean_dec(v___x_60_);
v___x_62_ = lean_nat_dec_eq(v___x_59_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction___boxed(lean_object* v_x_63_, lean_object* v_y_64_){
_start:
{
uint8_t v_x_23__boxed_65_; uint8_t v_y_24__boxed_66_; uint8_t v_res_67_; lean_object* v_r_68_; 
v_x_23__boxed_65_ = lean_unbox(v_x_63_);
v_y_24__boxed_66_ = lean_unbox(v_y_64_);
v_res_67_ = l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(v_x_23__boxed_65_, v_y_24__boxed_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(uint8_t v_x_79_, lean_object* v_prec_80_){
_start:
{
lean_object* v___y_82_; lean_object* v___y_89_; 
if (v_x_79_ == 0)
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1024u);
v___x_96_ = lean_nat_dec_le(v___x_95_, v_prec_80_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_82_ = v___x_97_;
goto v___jp_81_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_82_ = v___x_98_;
goto v___jp_81_;
}
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1024u);
v___x_100_ = lean_nat_dec_le(v___x_99_, v_prec_80_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_89_ = v___x_101_;
goto v___jp_88_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_89_ = v___x_102_;
goto v___jp_88_;
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1));
lean_inc(v___y_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = l_Repr_addAppParen(v___x_86_, v_prec_80_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3));
lean_inc(v___y_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
v___x_94_ = l_Repr_addAppParen(v___x_93_, v_prec_80_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed(lean_object* v_x_103_, lean_object* v_prec_104_){
_start:
{
uint8_t v_x_117__boxed_105_; lean_object* v_res_106_; 
v_x_117__boxed_105_ = lean_unbox(v_x_103_);
v_res_106_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_x_117__boxed_105_, v_prec_104_);
lean_dec(v_prec_104_);
return v_res_106_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default(void){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction(void){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Protocol_H1_instReprRedirectPlan_repr_spec__0(lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_nat_to_int(v_a_111_);
return v___x_112_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(10u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(11u);
v___x_141_ = lean_nat_to_int(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(14u);
v___x_146_ = lean_nat_to_int(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(17u);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0));
v___x_154_ = lean_string_length(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(lean_object* v_x_161_){
_start:
{
lean_object* v_origin_162_; lean_object* v_target_163_; uint8_t v_method_164_; lean_object* v_headers_165_; uint8_t v_bodyAction_166_; uint8_t v_isCrossOrigin_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_origin_162_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_origin_162_);
v_target_163_ = lean_ctor_get(v_x_161_, 1);
lean_inc(v_target_163_);
v_method_164_ = lean_ctor_get_uint8(v_x_161_, sizeof(void*)*3);
v_headers_165_ = lean_ctor_get(v_x_161_, 2);
lean_inc_ref(v_headers_165_);
v_bodyAction_166_ = lean_ctor_get_uint8(v_x_161_, sizeof(void*)*3 + 1);
v_isCrossOrigin_167_ = lean_ctor_get_uint8(v_x_161_, sizeof(void*)*3 + 2);
lean_dec_ref(v_x_161_);
v___x_168_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5));
v___x_169_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6));
v___x_170_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_origin_162_);
v___x_173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_170_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = 0;
v___x_175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_174_);
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_169_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9));
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_box(1);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11));
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_168_);
v___x_184_ = l_Std_Http_instReprRequestTarget_repr(v_target_163_, v___x_171_);
v___x_185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_170_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_174_);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_183_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_177_);
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_179_);
v___x_190_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13));
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_168_);
v___x_193_ = l_Std_Http_instReprMethod_repr(v_method_164_, v___x_171_);
v___x_194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_170_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_174_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_192_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_177_);
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_179_);
v___x_199_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15));
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_168_);
v___x_202_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16);
v___x_203_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_165_);
v___x_204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_174_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_201_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_177_);
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_179_);
v___x_209_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18));
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_168_);
v___x_212_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19);
v___x_213_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_bodyAction_166_, v___x_171_);
v___x_214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*1, v___x_174_);
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_211_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_177_);
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_179_);
v___x_219_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21));
v___x_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_168_);
v___x_222_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22);
v___x_223_ = l_Bool_repr___redArg(v_isCrossOrigin_167_);
v___x_224_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_174_);
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_221_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25);
v___x_228_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_226_);
v___x_230_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27));
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_227_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_174_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(lean_object* v_x_234_, lean_object* v_prec_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(v_x_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed(lean_object* v_x_237_, lean_object* v_prec_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(v_x_237_, v_prec_238_);
lean_dec(v_prec_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl(lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_tag_nat(v_x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl___boxed(lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl(v_x_244_);
lean_dec(v_x_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(lean_object* v_t_246_, lean_object* v_k_247_){
_start:
{
if (lean_obj_tag(v_t_246_) == 0)
{
return v_k_247_;
}
else
{
lean_object* v_plan_248_; lean_object* v___x_249_; 
v_plan_248_ = lean_ctor_get(v_t_246_, 0);
lean_inc_ref(v_plan_248_);
lean_dec_ref_known(v_t_246_, 1);
v___x_249_ = lean_apply_1(v_k_247_, v_plan_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_252_, v_k_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___boxed(lean_object* v_motive_256_, lean_object* v_ctorIdx_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_k_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(v_motive_256_, v_ctorIdx_257_, v_t_258_, v_h_259_, v_k_260_);
lean_dec(v_ctorIdx_257_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim___redArg(lean_object* v_t_262_, lean_object* v_done_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_262_, v_done_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_done_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_266_, v_done_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim___redArg(lean_object* v_t_270_, lean_object* v_follow_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_270_, v_follow_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_follow_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_274_, v_follow_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_box(0);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(lean_object* v_current_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_uri_282_; lean_object* v_authority_283_; 
lean_dec_ref(v_current_280_);
v_uri_282_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_uri_282_);
lean_dec_ref_known(v_x_281_, 1);
v_authority_283_ = lean_ctor_get(v_uri_282_, 1);
lean_inc(v_authority_283_);
if (lean_obj_tag(v_authority_283_) == 0)
{
lean_object* v___x_284_; 
lean_dec_ref(v_uri_282_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_300_; 
v_val_285_ = lean_ctor_get(v_authority_283_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_authority_283_);
if (v_isSharedCheck_300_ == 0)
{
v___x_287_ = v_authority_283_;
v_isShared_288_ = v_isSharedCheck_300_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v_authority_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_300_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_scheme_289_; lean_object* v_host_290_; lean_object* v_port_291_; uint16_t v___y_293_; 
v_scheme_289_ = lean_ctor_get(v_uri_282_, 0);
lean_inc_ref(v_scheme_289_);
lean_dec_ref(v_uri_282_);
v_host_290_ = lean_ctor_get(v_val_285_, 1);
lean_inc_ref(v_host_290_);
v_port_291_ = lean_ctor_get(v_val_285_, 2);
lean_inc(v_port_291_);
lean_dec(v_val_285_);
if (lean_obj_tag(v_port_291_) == 2)
{
uint16_t v_port_298_; 
v_port_298_ = lean_ctor_get_uint16(v_port_291_, 0);
lean_dec_ref_known(v_port_291_, 0);
v___y_293_ = v_port_298_;
goto v___jp_292_;
}
else
{
uint16_t v___x_299_; 
lean_dec(v_port_291_);
v___x_299_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_289_);
v___y_293_ = v___x_299_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_294_, 0, v_scheme_289_);
lean_ctor_set(v___x_294_, 1, v_host_290_);
lean_ctor_set_uint16(v___x_294_, sizeof(void*)*2, v___y_293_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_294_);
v___x_296_ = v___x_287_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
else
{
lean_object* v_ref_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_333_; 
v_ref_301_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_333_ == 0)
{
v___x_303_ = v_x_281_;
v_isShared_304_ = v_isSharedCheck_333_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_ref_301_);
lean_dec(v_x_281_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_333_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_authority_305_; 
v_authority_305_ = lean_ctor_get(v_ref_301_, 0);
lean_inc(v_authority_305_);
lean_dec_ref(v_ref_301_);
if (lean_obj_tag(v_authority_305_) == 1)
{
lean_object* v_val_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_329_; 
lean_del_object(v___x_303_);
v_val_306_ = lean_ctor_get(v_authority_305_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_authority_305_);
if (v_isSharedCheck_329_ == 0)
{
v___x_308_ = v_authority_305_;
v_isShared_309_ = v_isSharedCheck_329_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_val_306_);
lean_dec(v_authority_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_329_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_host_310_; lean_object* v_port_311_; uint16_t v___y_313_; 
v_host_310_ = lean_ctor_get(v_val_306_, 1);
lean_inc_ref(v_host_310_);
v_port_311_ = lean_ctor_get(v_val_306_, 2);
lean_inc(v_port_311_);
lean_dec(v_val_306_);
if (lean_obj_tag(v_port_311_) == 2)
{
uint16_t v_port_326_; 
v_port_326_ = lean_ctor_get_uint16(v_port_311_, 0);
lean_dec_ref_known(v_port_311_, 0);
v___y_313_ = v_port_326_;
goto v___jp_312_;
}
else
{
lean_object* v_scheme_327_; uint16_t v___x_328_; 
lean_dec(v_port_311_);
v_scheme_327_ = lean_ctor_get(v_current_280_, 0);
v___x_328_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_327_);
v___y_313_ = v___x_328_;
goto v___jp_312_;
}
v___jp_312_:
{
lean_object* v_scheme_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_324_; 
v_scheme_314_ = lean_ctor_get(v_current_280_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_current_280_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v_current_280_, 1);
lean_dec(v_unused_325_);
v___x_316_ = v_current_280_;
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_scheme_314_);
lean_dec(v_current_280_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v_host_310_);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_scheme_314_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_host_310_);
v___x_319_ = v_reuseFailAlloc_323_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; 
lean_ctor_set_uint16(v___x_319_, sizeof(void*)*2, v___y_313_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_319_);
v___x_321_ = v___x_308_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
}
else
{
lean_object* v___x_331_; 
lean_dec(v_authority_305_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v_current_280_);
v___x_331_ = v___x_303_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_current_280_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t v_originalMethod_334_, uint8_t v_responseVersion_335_, lean_object* v_x_336_){
_start:
{
uint8_t v___y_338_; 
switch(lean_obj_tag(v_x_336_))
{
case 17:
{
uint8_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 9;
v___x_346_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_334_, v___x_345_);
if (v___x_346_ == 0)
{
uint8_t v___x_347_; 
v___x_347_ = 8;
return v___x_347_;
}
else
{
return v___x_345_;
}
}
case 15:
{
goto v___jp_340_;
}
case 16:
{
goto v___jp_340_;
}
default: 
{
return v_originalMethod_334_;
}
}
v___jp_337_:
{
if (v___y_338_ == 0)
{
return v_originalMethod_334_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = 8;
return v___x_339_;
}
}
v___jp_340_:
{
uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = 23;
v___x_342_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_334_, v___x_341_);
if (v___x_342_ == 0)
{
v___y_338_ = v___x_342_;
goto v___jp_337_;
}
else
{
uint8_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 0;
v___x_344_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_335_, v___x_343_);
if (v___x_344_ == 0)
{
v___y_338_ = v___x_342_;
goto v___jp_337_;
}
else
{
return v_originalMethod_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_348_, lean_object* v_responseVersion_349_, lean_object* v_x_350_){
_start:
{
uint8_t v_originalMethod_boxed_351_; uint8_t v_responseVersion_boxed_352_; uint8_t v_res_353_; lean_object* v_r_354_; 
v_originalMethod_boxed_351_ = lean_unbox(v_originalMethod_348_);
v_responseVersion_boxed_352_ = lean_unbox(v_responseVersion_349_);
v_res_353_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_351_, v_responseVersion_boxed_352_, v_x_350_);
lean_dec(v_x_350_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_355_ = l_Std_Http_Header_Name_transferEncoding;
v___x_356_ = l_Std_Http_Header_Name_keepAlive;
v___x_357_ = l_Std_Http_Header_Name_connection;
v___x_358_ = lean_unsigned_to_nat(3u);
v___x_359_ = lean_mk_empty_array_with_capacity(v___x_358_);
v___x_360_ = lean_array_push(v___x_359_, v___x_357_);
v___x_361_ = lean_array_push(v___x_360_, v___x_356_);
v___x_362_ = lean_array_push(v___x_361_, v___x_355_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_363_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object* v_a_364_, lean_object* v_x_365_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
uint8_t v___x_366_; 
v___x_366_ = 0;
return v___x_366_;
}
else
{
lean_object* v_key_367_; lean_object* v_tail_368_; uint8_t v___x_369_; 
v_key_367_ = lean_ctor_get(v_x_365_, 0);
v_tail_368_ = lean_ctor_get(v_x_365_, 2);
v___x_369_ = lean_string_dec_eq(v_key_367_, v_a_364_);
if (v___x_369_ == 0)
{
v_x_365_ = v_tail_368_;
goto _start;
}
else
{
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object* v_a_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec_ref(v_a_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object* v_m_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_buckets_377_; lean_object* v___x_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v___x_381_; uint64_t v_fold_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_buckets_377_ = lean_ctor_get(v_m_375_, 1);
v___x_378_ = lean_array_get_size(v_buckets_377_);
v___x_379_ = lean_string_hash(v_a_376_);
v___x_380_ = 32ULL;
v___x_381_ = lean_uint64_shift_right(v___x_379_, v___x_380_);
v_fold_382_ = lean_uint64_xor(v___x_379_, v___x_381_);
v___x_383_ = 16ULL;
v___x_384_ = lean_uint64_shift_right(v_fold_382_, v___x_383_);
v___x_385_ = lean_uint64_xor(v_fold_382_, v___x_384_);
v___x_386_ = lean_uint64_to_usize(v___x_385_);
v___x_387_ = lean_usize_of_nat(v___x_378_);
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_sub(v___x_387_, v___x_388_);
v___x_390_ = lean_usize_land(v___x_386_, v___x_389_);
v___x_391_ = lean_array_uget_borrowed(v_buckets_377_, v___x_390_);
v___x_392_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_376_, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object* v_m_393_, lean_object* v_a_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_393_, v_a_394_);
lean_dec_ref(v_a_394_);
lean_dec_ref(v_m_393_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(lean_object* v_a_397_, lean_object* v_x_398_){
_start:
{
lean_object* v_key_399_; lean_object* v_value_400_; lean_object* v_tail_401_; uint8_t v___x_402_; 
v_key_399_ = lean_ctor_get(v_x_398_, 0);
v_value_400_ = lean_ctor_get(v_x_398_, 1);
v_tail_401_ = lean_ctor_get(v_x_398_, 2);
v___x_402_ = lean_string_dec_eq(v_key_399_, v_a_397_);
if (v___x_402_ == 0)
{
v_x_398_ = v_tail_401_;
goto _start;
}
else
{
lean_inc(v_value_400_);
return v_value_400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg___boxed(lean_object* v_a_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_404_, v_x_405_);
lean_dec(v_x_405_);
lean_dec_ref(v_a_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object* v_m_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_buckets_409_; lean_object* v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v_fold_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_buckets_409_ = lean_ctor_get(v_m_407_, 1);
v___x_410_ = lean_array_get_size(v_buckets_409_);
v___x_411_ = lean_string_hash(v_a_408_);
v___x_412_ = 32ULL;
v___x_413_ = lean_uint64_shift_right(v___x_411_, v___x_412_);
v_fold_414_ = lean_uint64_xor(v___x_411_, v___x_413_);
v___x_415_ = 16ULL;
v___x_416_ = lean_uint64_shift_right(v_fold_414_, v___x_415_);
v___x_417_ = lean_uint64_xor(v_fold_414_, v___x_416_);
v___x_418_ = lean_uint64_to_usize(v___x_417_);
v___x_419_ = lean_usize_of_nat(v___x_410_);
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_sub(v___x_419_, v___x_420_);
v___x_422_ = lean_usize_land(v___x_418_, v___x_421_);
v___x_423_ = lean_array_uget_borrowed(v_buckets_409_, v___x_422_);
v___x_424_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_408_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object* v_m_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_m_425_, v_a_426_);
lean_dec_ref(v_a_426_);
lean_dec_ref(v_m_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_, lean_object* v_b_431_){
_start:
{
lean_object* v___y_433_; uint8_t v___x_437_; 
v___x_437_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
lean_inc(v___x_438_);
v___x_439_ = l_Std_Http_Header_Name_ofString_x3f(v___x_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
v___y_433_ = v_b_431_;
goto v___jp_432_;
}
else
{
lean_object* v_val_440_; lean_object* v___x_441_; 
v_val_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = lean_array_push(v_b_431_, v_val_440_);
v___y_433_ = v___x_441_;
goto v___jp_432_;
}
}
else
{
return v_b_431_;
}
v___jp_432_:
{
size_t v___x_434_; size_t v___x_435_; 
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_429_, v___x_434_);
v_i_429_ = v___x_435_;
v_b_431_ = v___y_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_442_, lean_object* v_i_443_, lean_object* v_stop_444_, lean_object* v_b_445_){
_start:
{
size_t v_i_boxed_446_; size_t v_stop_boxed_447_; lean_object* v_res_448_; 
v_i_boxed_446_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_stop_boxed_447_ = lean_unbox_usize(v_stop_444_);
lean_dec(v_stop_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_442_, v_i_boxed_446_, v_stop_boxed_447_, v_b_445_);
lean_dec_ref(v_as_442_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(lean_object* v_as_449_, size_t v_i_450_, size_t v_stop_451_, lean_object* v_b_452_){
_start:
{
lean_object* v___y_454_; uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_eq(v_i_450_, v_stop_451_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_array_uget_borrowed(v_as_449_, v_i_450_);
lean_inc(v___x_459_);
v___x_460_ = l_Std_Http_Header_Connection_parse(v___x_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
v___y_454_ = v_b_452_;
goto v___jp_453_;
}
else
{
lean_object* v_val_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_val_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_array_get_size(v_val_461_);
v___x_464_ = lean_nat_dec_lt(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_dec(v_val_461_);
v___y_454_ = v_b_452_;
goto v___jp_453_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = lean_nat_dec_le(v___x_463_, v___x_463_);
if (v___x_465_ == 0)
{
if (v___x_464_ == 0)
{
lean_dec(v_val_461_);
v___y_454_ = v_b_452_;
goto v___jp_453_;
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_463_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_461_, v___x_466_, v___x_467_, v_b_452_);
lean_dec(v_val_461_);
v___y_454_ = v___x_468_;
goto v___jp_453_;
}
}
else
{
size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((size_t)0ULL);
v___x_470_ = lean_usize_of_nat(v___x_463_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_461_, v___x_469_, v___x_470_, v_b_452_);
lean_dec(v_val_461_);
v___y_454_ = v___x_471_;
goto v___jp_453_;
}
}
}
}
else
{
return v_b_452_;
}
v___jp_453_:
{
size_t v___x_455_; size_t v___x_456_; 
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_add(v_i_450_, v___x_455_);
v_i_450_ = v___x_456_;
v_b_452_ = v___y_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4___boxed(lean_object* v_as_472_, lean_object* v_i_473_, lean_object* v_stop_474_, lean_object* v_b_475_){
_start:
{
size_t v_i_boxed_476_; size_t v_stop_boxed_477_; lean_object* v_res_478_; 
v_i_boxed_476_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_stop_boxed_477_ = lean_unbox_usize(v_stop_474_);
lean_dec(v_stop_474_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_as_472_, v_i_boxed_476_, v_stop_boxed_477_, v_b_475_);
lean_dec_ref(v_as_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(lean_object* v___x_479_, lean_object* v___x_480_, size_t v_sz_481_, size_t v_i_482_, lean_object* v_bs_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_lt(v_i_482_, v_sz_481_);
if (v___x_484_ == 0)
{
return v_bs_483_;
}
else
{
lean_object* v_entries_485_; lean_object* v___x_486_; lean_object* v_bs_x27_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_snd_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v_entries_485_ = lean_ctor_get(v___x_479_, 0);
v___x_486_ = lean_unsigned_to_nat(0u);
v_bs_x27_487_ = lean_array_uset(v_bs_483_, v_i_482_, v___x_486_);
v___x_488_ = lean_usize_to_nat(v_i_482_);
v___x_489_ = lean_array_fget_borrowed(v___x_480_, v___x_488_);
lean_dec(v___x_488_);
v___x_490_ = lean_array_fget_borrowed(v_entries_485_, v___x_489_);
v_snd_491_ = lean_ctor_get(v___x_490_, 1);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_482_, v___x_492_);
lean_inc(v_snd_491_);
v___x_494_ = lean_array_uset(v_bs_x27_487_, v_i_482_, v_snd_491_);
v_i_482_ = v___x_493_;
v_bs_483_ = v___x_494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg___boxed(lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v_sz_498_, lean_object* v_i_499_, lean_object* v_bs_500_){
_start:
{
size_t v_sz_boxed_501_; size_t v_i_boxed_502_; lean_object* v_res_503_; 
v_sz_boxed_501_ = lean_unbox_usize(v_sz_498_);
lean_dec(v_sz_498_);
v_i_boxed_502_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_496_, v___x_497_, v_sz_boxed_501_, v_i_boxed_502_, v_bs_500_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v___x_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_506_){
_start:
{
lean_object* v_indexes_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_indexes_507_ = lean_ctor_get(v_headers_506_, 1);
v___x_508_ = l_Std_Http_Header_Name_connection;
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
return v___x_510_;
}
else
{
lean_object* v___x_511_; size_t v_sz_512_; size_t v___x_513_; lean_object* v_entries_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_507_, v___x_508_);
v_sz_512_ = lean_array_size(v___x_511_);
v___x_513_ = ((size_t)0ULL);
lean_inc(v___x_511_);
v_entries_514_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v_headers_506_, v___x_511_, v_sz_512_, v___x_513_, v___x_511_);
lean_dec(v___x_511_);
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_517_ = lean_array_get_size(v_entries_514_);
v___x_518_ = lean_nat_dec_lt(v___x_515_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec_ref(v_entries_514_);
return v___x_516_;
}
else
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_le(v___x_517_, v___x_517_);
if (v___x_519_ == 0)
{
if (v___x_518_ == 0)
{
lean_dec_ref(v_entries_514_);
return v___x_516_;
}
else
{
size_t v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_usize_of_nat(v___x_517_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_entries_514_, v___x_513_, v___x_520_, v___x_516_);
lean_dec_ref(v_entries_514_);
return v___x_521_;
}
}
else
{
size_t v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_usize_of_nat(v___x_517_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_entries_514_, v___x_513_, v___x_522_, v___x_516_);
lean_dec_ref(v_entries_514_);
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_524_);
lean_dec_ref(v_headers_524_);
return v_res_525_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_527_, v_a_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_00_u03b2_530_, lean_object* v_m_531_, lean_object* v_a_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_00_u03b2_530_, v_m_531_, v_a_532_);
lean_dec_ref(v_a_532_);
lean_dec_ref(v_m_531_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v_00_u03b2_535_, lean_object* v_m_536_, lean_object* v_a_537_, lean_object* v_hma_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_m_536_, v_a_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v_00_u03b2_540_, lean_object* v_m_541_, lean_object* v_a_542_, lean_object* v_hma_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_00_u03b2_540_, v_m_541_, v_a_542_, v_hma_543_);
lean_dec_ref(v_a_542_);
lean_dec_ref(v_m_541_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v_as_547_, size_t v_sz_548_, size_t v_i_549_, lean_object* v_bs_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_545_, v___x_546_, v_sz_548_, v_i_549_, v_bs_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object* v___x_552_, lean_object* v___x_553_, lean_object* v_as_554_, lean_object* v_sz_555_, lean_object* v_i_556_, lean_object* v_bs_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_555_);
lean_dec(v_sz_555_);
v_i_boxed_559_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v___x_552_, v___x_553_, v_as_554_, v_sz_boxed_558_, v_i_boxed_559_, v_bs_557_);
lean_dec_ref(v_as_554_);
lean_dec_ref(v___x_553_);
lean_dec_ref(v___x_552_);
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object* v_00_u03b2_561_, lean_object* v_a_562_, lean_object* v_x_563_){
_start:
{
uint8_t v___x_564_; 
v___x_564_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_562_, v_x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object* v_00_u03b2_565_, lean_object* v_a_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(v_00_u03b2_565_, v_a_566_, v_x_567_);
lean_dec(v_x_567_);
lean_dec_ref(v_a_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(lean_object* v_00_u03b2_570_, lean_object* v_a_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_571_, v_x_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___boxed(lean_object* v_00_u03b2_575_, lean_object* v_a_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(v_00_u03b2_575_, v_a_576_, v_x_577_, v_x_578_);
lean_dec(v_x_577_);
lean_dec_ref(v_a_576_);
return v_res_579_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_580_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_mk_empty_array_with_capacity(v___x_581_);
v___x_583_ = lean_array_push(v___x_582_, v___x_580_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_584_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_585_ = l_Std_Http_Header_Name_referer;
v___x_586_ = l_Std_Http_Header_Name_cookie;
v___x_587_ = l_Std_Http_Header_Name_authorization;
v___x_588_ = lean_unsigned_to_nat(3u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
v___x_590_ = lean_array_push(v___x_589_, v___x_587_);
v___x_591_ = lean_array_push(v___x_590_, v___x_586_);
v___x_592_ = lean_array_push(v___x_591_, v___x_585_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_593_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_595_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_596_ = lean_unsigned_to_nat(2u);
v___x_597_ = lean_mk_empty_array_with_capacity(v___x_596_);
v___x_598_ = lean_array_push(v___x_597_, v___x_595_);
v___x_599_ = lean_array_push(v___x_598_, v___x_594_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_600_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_601_ = l_Std_Http_Header_Name_lastModified;
v___x_602_ = l_Std_Http_Header_Name_contentLocation;
v___x_603_ = l_Std_Http_Header_Name_contentLanguage;
v___x_604_ = l_Std_Http_Header_Name_contentEncoding;
v___x_605_ = l_Std_Http_Header_Name_contentLength;
v___x_606_ = l_Std_Http_Header_Name_contentType;
v___x_607_ = lean_unsigned_to_nat(6u);
v___x_608_ = lean_mk_empty_array_with_capacity(v___x_607_);
v___x_609_ = lean_array_push(v___x_608_, v___x_606_);
v___x_610_ = lean_array_push(v___x_609_, v___x_605_);
v___x_611_ = lean_array_push(v___x_610_, v___x_604_);
v___x_612_ = lean_array_push(v___x_611_, v___x_603_);
v___x_613_ = lean_array_push(v___x_612_, v___x_602_);
v___x_614_ = lean_array_push(v___x_613_, v___x_601_);
return v___x_614_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_615_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_box(0);
v___x_619_ = lean_unsigned_to_nat(16u);
v___x_620_ = lean_mk_array(v___x_619_, v___x_618_);
return v___x_620_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
return v___x_623_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2);
v___x_625_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0));
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg(){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___boxed(lean_object* v___dummy_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
return v_res_630_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v_00_u03b2_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(lean_object* v_i_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_mk_empty_array_with_capacity(v___x_636_);
v___x_638_ = lean_array_push(v___x_637_, v_i_634_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v_val_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_val_640_ = lean_ctor_get(v_x_635_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v_x_635_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_val_640_);
lean_dec(v_x_635_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_array_push(v_val_640_, v_i_634_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(lean_object* v_i_649_, lean_object* v_a_650_, lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_651_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_val_654_; lean_object* v___x_655_; 
v___x_652_ = lean_box(0);
v___x_653_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(v_i_649_, v___x_652_);
v_val_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_654_);
lean_dec(v___x_653_);
v___x_655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_655_, 0, v_a_650_);
lean_ctor_set(v___x_655_, 1, v_val_654_);
lean_ctor_set(v___x_655_, 2, v_x_651_);
return v___x_655_;
}
else
{
lean_object* v_key_656_; lean_object* v_value_657_; lean_object* v_tail_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_673_; 
v_key_656_ = lean_ctor_get(v_x_651_, 0);
v_value_657_ = lean_ctor_get(v_x_651_, 1);
v_tail_658_ = lean_ctor_get(v_x_651_, 2);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_651_);
if (v_isSharedCheck_673_ == 0)
{
v___x_660_ = v_x_651_;
v_isShared_661_ = v_isSharedCheck_673_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_tail_658_);
lean_inc(v_value_657_);
lean_inc(v_key_656_);
lean_dec(v_x_651_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_673_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
uint8_t v___x_662_; 
v___x_662_ = lean_string_dec_eq(v_key_656_, v_a_650_);
if (v___x_662_ == 0)
{
lean_object* v_tail_663_; lean_object* v___x_665_; 
v_tail_663_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(v_i_649_, v_a_650_, v_tail_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 2, v_tail_663_);
v___x_665_ = v___x_660_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_key_656_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_value_657_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_tail_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_val_669_; lean_object* v___x_671_; 
lean_dec(v_key_656_);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v_value_657_);
v___x_668_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(v_i_649_, v___x_667_);
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec(v___x_668_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v_val_669_);
lean_ctor_set(v___x_660_, 0, v_a_650_);
v___x_671_ = v___x_660_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_650_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_val_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_tail_658_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_675_) == 0)
{
return v_x_674_;
}
else
{
lean_object* v_key_676_; lean_object* v_value_677_; lean_object* v_tail_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_701_; 
v_key_676_ = lean_ctor_get(v_x_675_, 0);
v_value_677_ = lean_ctor_get(v_x_675_, 1);
v_tail_678_ = lean_ctor_get(v_x_675_, 2);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_701_ == 0)
{
v___x_680_ = v_x_675_;
v_isShared_681_ = v_isSharedCheck_701_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_tail_678_);
lean_inc(v_value_677_);
lean_inc(v_key_676_);
lean_dec(v_x_675_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_701_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v_fold_686_; uint64_t v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; size_t v___x_690_; size_t v___x_691_; size_t v___x_692_; size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_682_ = lean_array_get_size(v_x_674_);
v___x_683_ = lean_string_hash(v_key_676_);
v___x_684_ = 32ULL;
v___x_685_ = lean_uint64_shift_right(v___x_683_, v___x_684_);
v_fold_686_ = lean_uint64_xor(v___x_683_, v___x_685_);
v___x_687_ = 16ULL;
v___x_688_ = lean_uint64_shift_right(v_fold_686_, v___x_687_);
v___x_689_ = lean_uint64_xor(v_fold_686_, v___x_688_);
v___x_690_ = lean_uint64_to_usize(v___x_689_);
v___x_691_ = lean_usize_of_nat(v___x_682_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_sub(v___x_691_, v___x_692_);
v___x_694_ = lean_usize_land(v___x_690_, v___x_693_);
v___x_695_ = lean_array_uget_borrowed(v_x_674_, v___x_694_);
lean_inc(v___x_695_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 2, v___x_695_);
v___x_697_ = v___x_680_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_key_676_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_value_677_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v___x_695_);
v___x_697_ = v_reuseFailAlloc_700_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; 
v___x_698_ = lean_array_uset(v_x_674_, v___x_694_, v___x_697_);
v_x_674_ = v___x_698_;
v_x_675_ = v_tail_678_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(lean_object* v_i_702_, lean_object* v_source_703_, lean_object* v_target_704_){
_start:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_array_get_size(v_source_703_);
v___x_706_ = lean_nat_dec_lt(v_i_702_, v___x_705_);
if (v___x_706_ == 0)
{
lean_dec_ref(v_source_703_);
lean_dec(v_i_702_);
return v_target_704_;
}
else
{
lean_object* v_es_707_; lean_object* v___x_708_; lean_object* v_source_709_; lean_object* v_target_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_es_707_ = lean_array_fget(v_source_703_, v_i_702_);
v___x_708_ = lean_box(0);
v_source_709_ = lean_array_fset(v_source_703_, v_i_702_, v___x_708_);
v_target_710_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(v_target_704_, v_es_707_);
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_add(v_i_702_, v___x_711_);
lean_dec(v_i_702_);
v_i_702_ = v___x_712_;
v_source_703_ = v_source_709_;
v_target_704_ = v_target_710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(lean_object* v_data_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_nbuckets_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_715_ = lean_array_get_size(v_data_714_);
v___x_716_ = lean_unsigned_to_nat(2u);
v_nbuckets_717_ = lean_nat_mul(v___x_715_, v___x_716_);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_box(0);
v___x_720_ = lean_mk_array(v_nbuckets_717_, v___x_719_);
v___x_721_ = lean_array_propagate_mark(v_data_714_, v___x_720_);
v___x_722_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(v___x_718_, v_data_714_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v_i_723_, lean_object* v_m_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_size_726_; lean_object* v_buckets_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_777_; 
v_size_726_ = lean_ctor_get(v_m_724_, 0);
v_buckets_727_ = lean_ctor_get(v_m_724_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_m_724_);
if (v_isSharedCheck_777_ == 0)
{
v___x_729_ = v_m_724_;
v_isShared_730_ = v_isSharedCheck_777_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_buckets_727_);
lean_inc(v_size_726_);
lean_dec(v_m_724_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_777_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; uint64_t v___x_732_; uint64_t v___x_733_; uint64_t v___x_734_; uint64_t v_fold_735_; uint64_t v___x_736_; uint64_t v___x_737_; uint64_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v___x_743_; lean_object* v_bkt_744_; uint8_t v___x_745_; 
v___x_731_ = lean_array_get_size(v_buckets_727_);
v___x_732_ = lean_string_hash(v_a_725_);
v___x_733_ = 32ULL;
v___x_734_ = lean_uint64_shift_right(v___x_732_, v___x_733_);
v_fold_735_ = lean_uint64_xor(v___x_732_, v___x_734_);
v___x_736_ = 16ULL;
v___x_737_ = lean_uint64_shift_right(v_fold_735_, v___x_736_);
v___x_738_ = lean_uint64_xor(v_fold_735_, v___x_737_);
v___x_739_ = lean_uint64_to_usize(v___x_738_);
v___x_740_ = lean_usize_of_nat(v___x_731_);
v___x_741_ = ((size_t)1ULL);
v___x_742_ = lean_usize_sub(v___x_740_, v___x_741_);
v___x_743_ = lean_usize_land(v___x_739_, v___x_742_);
v_bkt_744_ = lean_array_uget_borrowed(v_buckets_727_, v___x_743_);
v___x_745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_725_, v_bkt_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_size_x27_749_; lean_object* v___x_750_; lean_object* v_buckets_x27_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_mk_empty_array_with_capacity(v___x_746_);
v___x_748_ = lean_array_push(v___x_747_, v_i_723_);
v_size_x27_749_ = lean_nat_add(v_size_726_, v___x_746_);
lean_dec(v_size_726_);
lean_inc(v_bkt_744_);
v___x_750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_750_, 0, v_a_725_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
lean_ctor_set(v___x_750_, 2, v_bkt_744_);
v_buckets_x27_751_ = lean_array_uset(v_buckets_727_, v___x_743_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(4u);
v___x_753_ = lean_nat_mul(v_size_x27_749_, v___x_752_);
v___x_754_ = lean_unsigned_to_nat(3u);
v___x_755_ = lean_nat_div(v___x_753_, v___x_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_array_get_size(v_buckets_x27_751_);
v___x_757_ = lean_nat_dec_le(v___x_755_, v___x_756_);
lean_dec(v___x_755_);
if (v___x_757_ == 0)
{
lean_object* v_val_758_; lean_object* v___x_760_; 
v_val_758_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(v_buckets_x27_751_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_val_758_);
lean_ctor_set(v___x_729_, 0, v_size_x27_749_);
v___x_760_ = v___x_729_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_size_x27_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_val_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
lean_object* v___x_763_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_buckets_x27_751_);
lean_ctor_set(v___x_729_, 0, v_size_x27_749_);
v___x_763_ = v___x_729_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_size_x27_749_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_buckets_x27_751_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v___x_765_; lean_object* v_buckets_x27_766_; lean_object* v_bkt_x27_767_; lean_object* v___y_769_; uint8_t v___x_774_; 
lean_inc(v_bkt_744_);
v___x_765_ = lean_box(0);
v_buckets_x27_766_ = lean_array_uset(v_buckets_727_, v___x_743_, v___x_765_);
lean_inc_ref(v_a_725_);
v_bkt_x27_767_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(v_i_723_, v_a_725_, v_bkt_744_);
v___x_774_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_725_, v_bkt_x27_767_);
lean_dec_ref(v_a_725_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_sub(v_size_726_, v___x_775_);
lean_dec(v_size_726_);
v___y_769_ = v___x_776_;
goto v___jp_768_;
}
else
{
v___y_769_ = v_size_726_;
goto v___jp_768_;
}
v___jp_768_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_770_ = lean_array_uset(v_buckets_x27_766_, v___x_743_, v_bkt_x27_767_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_770_);
lean_ctor_set(v___x_729_, 0, v___y_769_);
v___x_772_ = v___x_729_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___y_769_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_a_778_, lean_object* v_as_779_, size_t v_i_780_, size_t v_stop_781_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = lean_usize_dec_eq(v_i_780_, v_stop_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_array_uget_borrowed(v_as_779_, v_i_780_);
v___x_784_ = lean_string_dec_eq(v_a_778_, v___x_783_);
if (v___x_784_ == 0)
{
size_t v___x_785_; size_t v___x_786_; 
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_add(v_i_780_, v___x_785_);
v_i_780_ = v___x_786_;
goto _start;
}
else
{
return v___x_784_;
}
}
else
{
uint8_t v___x_788_; 
v___x_788_ = 0;
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_a_789_, lean_object* v_as_790_, lean_object* v_i_791_, lean_object* v_stop_792_){
_start:
{
size_t v_i_boxed_793_; size_t v_stop_boxed_794_; uint8_t v_res_795_; lean_object* v_r_796_; 
v_i_boxed_793_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_stop_boxed_794_ = lean_unbox_usize(v_stop_792_);
lean_dec(v_stop_792_);
v_res_795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_789_, v_as_790_, v_i_boxed_793_, v_stop_boxed_794_);
lean_dec_ref(v_as_790_);
lean_dec_ref(v_a_789_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_as_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_array_get_size(v_as_797_);
v___x_801_ = lean_nat_dec_lt(v___x_799_, v___x_800_);
if (v___x_801_ == 0)
{
return v___x_801_;
}
else
{
if (v___x_801_ == 0)
{
return v___x_801_;
}
else
{
size_t v___x_802_; size_t v___x_803_; uint8_t v___x_804_; 
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_of_nat(v___x_800_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_798_, v_as_797_, v___x_802_, v___x_803_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object* v_as_805_, lean_object* v_a_806_){
_start:
{
uint8_t v_res_807_; lean_object* v_r_808_; 
v_res_807_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_as_805_, v_a_806_);
lean_dec_ref(v_a_806_);
lean_dec_ref(v_as_805_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object* v___y_809_, lean_object* v_as_810_, size_t v_i_811_, size_t v_stop_812_, lean_object* v_b_813_){
_start:
{
lean_object* v___y_815_; uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_eq(v_i_811_, v_stop_812_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v_fst_821_; uint8_t v___x_835_; 
v___x_820_ = lean_array_uget_borrowed(v_as_810_, v_i_811_);
v_fst_821_ = lean_ctor_get(v___x_820_, 0);
v___x_835_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_809_, v_fst_821_);
if (v___x_835_ == 0)
{
goto v___jp_822_;
}
else
{
if (v___x_819_ == 0)
{
v___y_815_ = v_b_813_;
goto v___jp_814_;
}
else
{
goto v___jp_822_;
}
}
v___jp_822_:
{
lean_object* v_entries_823_; lean_object* v_indexes_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_834_; 
v_entries_823_ = lean_ctor_get(v_b_813_, 0);
v_indexes_824_ = lean_ctor_get(v_b_813_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_b_813_);
if (v_isSharedCheck_834_ == 0)
{
v___x_826_ = v_b_813_;
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_indexes_824_);
lean_inc(v_entries_823_);
lean_dec(v_b_813_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_i_828_; lean_object* v_entries_829_; lean_object* v_indexes_830_; lean_object* v___x_832_; 
v_i_828_ = lean_array_get_size(v_entries_823_);
lean_inc(v___x_820_);
v_entries_829_ = lean_array_push(v_entries_823_, v___x_820_);
lean_inc(v_fst_821_);
v_indexes_830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v_i_828_, v_indexes_824_, v_fst_821_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v_indexes_830_);
lean_ctor_set(v___x_826_, 0, v_entries_829_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_entries_829_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_indexes_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
v___y_815_ = v___x_832_;
goto v___jp_814_;
}
}
}
}
else
{
return v_b_813_;
}
v___jp_814_:
{
size_t v___x_816_; size_t v___x_817_; 
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_811_, v___x_816_);
v_i_811_ = v___x_817_;
v_b_813_ = v___y_815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object* v___y_836_, lean_object* v_as_837_, lean_object* v_i_838_, lean_object* v_stop_839_, lean_object* v_b_840_){
_start:
{
size_t v_i_boxed_841_; size_t v_stop_boxed_842_; lean_object* v_res_843_; 
v_i_boxed_841_ = lean_unbox_usize(v_i_838_);
lean_dec(v_i_838_);
v_stop_boxed_842_ = lean_unbox_usize(v_stop_839_);
lean_dec(v_stop_839_);
v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_836_, v_as_837_, v_i_boxed_841_, v_stop_boxed_842_, v_b_840_);
lean_dec_ref(v_as_837_);
lean_dec_ref(v___y_836_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_844_, uint8_t v_isCrossOrigin_845_, uint8_t v_methodChanged_846_){
_start:
{
lean_object* v___y_848_; lean_object* v___y_858_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_afterConnection_865_; 
v___x_863_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_864_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_844_);
v_afterConnection_865_ = l_Array_append___redArg(v___x_863_, v___x_864_);
lean_dec_ref(v___x_864_);
if (v_isCrossOrigin_845_ == 0)
{
v___y_858_ = v_afterConnection_865_;
goto v___jp_857_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_866_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_867_ = l_Array_append___redArg(v_afterConnection_865_, v___x_866_);
v___x_868_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_869_ = l_Array_append___redArg(v___x_867_, v___x_868_);
v___x_870_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_871_ = l_Array_append___redArg(v___x_869_, v___x_870_);
v___y_858_ = v___x_871_;
goto v___jp_857_;
}
v___jp_847_:
{
lean_object* v_entries_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_entries_849_ = lean_ctor_get(v_headers_844_, 0);
v___x_850_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_array_get_size(v_entries_849_);
v___x_853_ = lean_nat_dec_lt(v___x_851_, v___x_852_);
if (v___x_853_ == 0)
{
lean_dec_ref(v___y_848_);
return v___x_850_;
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((size_t)0ULL);
v___x_855_ = lean_usize_of_nat(v___x_852_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_848_, v_entries_849_, v___x_854_, v___x_855_, v___x_850_);
lean_dec_ref(v___y_848_);
return v___x_856_;
}
}
v___jp_857_:
{
if (v_methodChanged_846_ == 0)
{
v___y_848_ = v___y_858_;
goto v___jp_847_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_859_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_860_ = l_Array_append___redArg(v___y_858_, v___x_859_);
v___x_861_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_862_ = l_Array_append___redArg(v___x_860_, v___x_861_);
v___y_848_ = v___x_862_;
goto v___jp_847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_872_, lean_object* v_isCrossOrigin_873_, lean_object* v_methodChanged_874_){
_start:
{
uint8_t v_isCrossOrigin_boxed_875_; uint8_t v_methodChanged_boxed_876_; lean_object* v_res_877_; 
v_isCrossOrigin_boxed_875_ = lean_unbox(v_isCrossOrigin_873_);
v_methodChanged_boxed_876_ = lean_unbox(v_methodChanged_874_);
v_res_877_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_872_, v_isCrossOrigin_boxed_875_, v_methodChanged_boxed_876_);
lean_dec_ref(v_headers_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(lean_object* v_00_u03b2_878_, lean_object* v_data_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(v_data_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_881_, lean_object* v_i_882_, lean_object* v_source_883_, lean_object* v_target_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(v_i_882_, v_source_883_, v_target_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(v_x_887_, v_x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_890_, lean_object* v_origin_891_){
_start:
{
lean_object* v_entries_892_; lean_object* v_indexes_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_entries_892_ = lean_ctor_get(v_headers_890_, 0);
v_indexes_893_ = lean_ctor_get(v_headers_890_, 1);
v___x_894_ = l_Std_Http_Header_Name_host;
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_dec_ref(v_origin_891_);
return v_headers_890_;
}
else
{
if (v___x_895_ == 0)
{
lean_dec_ref(v_origin_891_);
return v_headers_890_;
}
else
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_911_; 
lean_inc_ref(v_indexes_893_);
lean_inc_ref(v_entries_892_);
v_isSharedCheck_911_ = !lean_is_exclusive(v_headers_890_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_912_ = lean_ctor_get(v_headers_890_, 1);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_headers_890_, 0);
lean_dec(v_unused_913_);
v___x_897_ = v_headers_890_;
v_isShared_898_ = v_isSharedCheck_911_;
goto v_resetjp_896_;
}
else
{
lean_dec(v_headers_890_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_911_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_idxs_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v_lastIdx_905_; lean_object* v___x_906_; lean_object* v_entries_907_; lean_object* v___x_909_; 
v___x_899_ = l_Std_Http_URI_Origin_hostHeader(v_origin_891_);
v___x_900_ = l_Std_Http_Header_Value_ofString_x21(v___x_899_);
v_idxs_901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_893_, v___x_894_);
v___x_902_ = lean_array_get_size(v_idxs_901_);
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_sub(v___x_902_, v___x_903_);
v_lastIdx_905_ = lean_array_fget(v_idxs_901_, v___x_904_);
lean_dec(v___x_904_);
lean_dec(v_idxs_901_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_894_);
lean_ctor_set(v___x_906_, 1, v___x_900_);
v_entries_907_ = lean_array_fset(v_entries_892_, v_lastIdx_905_, v___x_906_);
lean_dec(v_lastIdx_905_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_entries_907_);
v___x_909_ = v___x_897_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_entries_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_indexes_893_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_914_){
_start:
{
switch(lean_obj_tag(v_x_914_))
{
case 0:
{
lean_object* v_query_915_; 
v_query_915_ = lean_ctor_get(v_x_914_, 1);
lean_inc(v_query_915_);
return v_query_915_;
}
case 1:
{
lean_object* v_uri_916_; lean_object* v_query_917_; 
v_uri_916_ = lean_ctor_get(v_x_914_, 0);
v_query_917_ = lean_ctor_get(v_uri_916_, 3);
lean_inc(v_query_917_);
return v_query_917_;
}
default: 
{
lean_object* v___x_918_; 
v___x_918_ = lean_box(0);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_919_);
lean_dec(v_x_919_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_921_, uint8_t v_isCrossOrigin_922_, lean_object* v_basePath_923_, lean_object* v_baseQuery_924_, lean_object* v_currentScheme_925_){
_start:
{
lean_object* v___y_927_; lean_object* v___y_928_; 
if (lean_obj_tag(v_ref_921_) == 0)
{
lean_object* v_uri_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_973_; 
lean_dec_ref(v_currentScheme_925_);
lean_dec(v_baseQuery_924_);
lean_dec_ref(v_basePath_923_);
v_uri_931_ = lean_ctor_get(v_ref_921_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v_ref_921_);
if (v_isSharedCheck_973_ == 0)
{
v___x_933_ = v_ref_921_;
v_isShared_934_ = v_isSharedCheck_973_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_uri_931_);
lean_dec(v_ref_921_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_973_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_scheme_935_; lean_object* v_authority_936_; lean_object* v_path_937_; lean_object* v_query_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_971_; 
v_scheme_935_ = lean_ctor_get(v_uri_931_, 0);
v_authority_936_ = lean_ctor_get(v_uri_931_, 1);
v_path_937_ = lean_ctor_get(v_uri_931_, 2);
v_query_938_ = lean_ctor_get(v_uri_931_, 3);
v_isSharedCheck_971_ = !lean_is_exclusive(v_uri_931_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v_uri_931_, 4);
lean_dec(v_unused_972_);
v___x_940_ = v_uri_931_;
v_isShared_941_ = v_isSharedCheck_971_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_query_938_);
lean_inc(v_path_937_);
lean_inc(v_authority_936_);
lean_inc(v_scheme_935_);
lean_dec(v_uri_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_971_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___y_943_; 
if (lean_obj_tag(v_authority_936_) == 0)
{
v___y_943_ = v_authority_936_;
goto v___jp_942_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_970_; 
v_val_952_ = lean_ctor_get(v_authority_936_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v_authority_936_);
if (v_isSharedCheck_970_ == 0)
{
v___x_954_ = v_authority_936_;
v_isShared_955_ = v_isSharedCheck_970_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v_authority_936_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_970_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_host_956_; lean_object* v_port_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_968_; 
v_host_956_ = lean_ctor_get(v_val_952_, 1);
v_port_957_ = lean_ctor_get(v_val_952_, 2);
v_isSharedCheck_968_ = !lean_is_exclusive(v_val_952_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_val_952_, 0);
lean_dec(v_unused_969_);
v___x_959_ = v_val_952_;
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_port_957_);
lean_inc(v_host_956_);
lean_dec(v_val_952_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_host_956_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_port_957_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_963_);
v___x_965_ = v___x_954_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v___y_943_ = v___x_965_;
goto v___jp_942_;
}
}
}
}
}
v___jp_942_:
{
if (v_isCrossOrigin_922_ == 0)
{
lean_object* v___x_944_; 
lean_dec(v___y_943_);
lean_del_object(v___x_940_);
lean_dec_ref(v_scheme_935_);
lean_del_object(v___x_933_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_path_937_);
lean_ctor_set(v___x_944_, 1, v_query_938_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v_stripped_947_; 
v___x_945_ = lean_box(0);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v___x_945_);
lean_ctor_set(v___x_940_, 1, v___y_943_);
v_stripped_947_ = v___x_940_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_scheme_935_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___y_943_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_path_937_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_query_938_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v___x_945_);
v_stripped_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
lean_ctor_set(v___x_933_, 0, v_stripped_947_);
v___x_949_ = v___x_933_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_stripped_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
}
else
{
lean_object* v_ref_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1015_; 
v_ref_974_ = lean_ctor_get(v_ref_921_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_ref_921_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_976_ = v_ref_921_;
v_isShared_977_ = v_isSharedCheck_1015_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_ref_974_);
lean_dec(v_ref_921_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1015_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_authority_978_; lean_object* v_path_979_; lean_object* v_query_980_; lean_object* v___y_982_; uint8_t v___y_983_; 
v_authority_978_ = lean_ctor_get(v_ref_974_, 0);
lean_inc(v_authority_978_);
v_path_979_ = lean_ctor_get(v_ref_974_, 1);
lean_inc_ref(v_path_979_);
v_query_980_ = lean_ctor_get(v_ref_974_, 2);
lean_inc(v_query_980_);
lean_dec_ref(v_ref_974_);
if (lean_obj_tag(v_authority_978_) == 0)
{
uint8_t v___x_984_; lean_object* v___y_986_; 
lean_del_object(v___x_976_);
lean_dec_ref(v_currentScheme_925_);
v___x_984_ = l_Std_Http_URI_Path_isEmpty(v_path_979_);
if (v___x_984_ == 0)
{
uint8_t v_absolute_987_; 
v_absolute_987_ = lean_ctor_get_uint8(v_path_979_, sizeof(void*)*1);
if (v_absolute_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = l_Std_Http_URI_Path_parent(v_basePath_923_);
v___x_989_ = l_Std_Http_URI_Path_join(v___x_988_, v_path_979_);
lean_dec_ref(v_path_979_);
v___y_986_ = v___x_989_;
goto v___jp_985_;
}
else
{
lean_dec_ref(v_basePath_923_);
v___y_986_ = v_path_979_;
goto v___jp_985_;
}
}
else
{
lean_dec_ref(v_path_979_);
v___y_986_ = v_basePath_923_;
goto v___jp_985_;
}
v___jp_985_:
{
if (v___x_984_ == 0)
{
v___y_982_ = v___y_986_;
v___y_983_ = v___x_984_;
goto v___jp_981_;
}
else
{
if (lean_obj_tag(v_query_980_) == 0)
{
v___y_982_ = v___y_986_;
v___y_983_ = v___x_984_;
goto v___jp_981_;
}
else
{
lean_dec(v_baseQuery_924_);
v___y_927_ = v___y_986_;
v___y_928_ = v_query_980_;
goto v___jp_926_;
}
}
}
}
else
{
lean_dec(v_baseQuery_924_);
lean_dec_ref(v_basePath_923_);
if (v_isCrossOrigin_922_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec_ref_known(v_authority_978_, 1);
lean_del_object(v___x_976_);
lean_dec_ref(v_currentScheme_925_);
v___x_990_ = l_Std_Http_URI_Path_normalize(v_path_979_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v_query_980_);
return v___x_991_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1014_; 
v_val_992_ = lean_ctor_get(v_authority_978_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_authority_978_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_994_ = v_authority_978_;
v_isShared_995_ = v_isSharedCheck_1014_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_val_992_);
lean_dec(v_authority_978_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1014_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_host_996_; lean_object* v_port_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1012_; 
v_host_996_ = lean_ctor_get(v_val_992_, 1);
v_port_997_ = lean_ctor_get(v_val_992_, 2);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_val_992_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_val_992_, 0);
lean_dec(v_unused_1013_);
v___x_999_ = v_val_992_;
v_isShared_1000_ = v_isSharedCheck_1012_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_port_997_);
lean_inc(v_host_996_);
lean_dec(v_val_992_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1012_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v_stripped_1003_; 
v___x_1001_ = lean_box(0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1001_);
v_stripped_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_host_996_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_port_997_);
v_stripped_1003_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v_stripped_1003_);
v___x_1005_ = v___x_994_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_stripped_1003_);
v___x_1005_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v_af_1006_; lean_object* v___x_1008_; 
v_af_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_1006_, 0, v_currentScheme_925_);
lean_ctor_set(v_af_1006_, 1, v___x_1005_);
lean_ctor_set(v_af_1006_, 2, v_path_979_);
lean_ctor_set(v_af_1006_, 3, v_query_980_);
lean_ctor_set(v_af_1006_, 4, v___x_1001_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v_af_1006_);
v___x_1008_ = v___x_976_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_af_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
}
v___jp_981_:
{
if (v___y_983_ == 0)
{
lean_dec(v_baseQuery_924_);
v___y_927_ = v___y_982_;
v___y_928_ = v_query_980_;
goto v___jp_926_;
}
else
{
lean_dec(v_query_980_);
v___y_927_ = v___y_982_;
v___y_928_ = v_baseQuery_924_;
goto v___jp_926_;
}
}
}
}
v___jp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = l_Std_Http_URI_Path_normalize(v___y_927_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___y_928_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_1016_, lean_object* v_isCrossOrigin_1017_, lean_object* v_basePath_1018_, lean_object* v_baseQuery_1019_, lean_object* v_currentScheme_1020_){
_start:
{
uint8_t v_isCrossOrigin_boxed_1021_; lean_object* v_res_1022_; 
v_isCrossOrigin_boxed_1021_ = lean_unbox(v_isCrossOrigin_1017_);
v_res_1022_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_1016_, v_isCrossOrigin_boxed_1021_, v_basePath_1018_, v_baseQuery_1019_, v_currentScheme_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Std_Http_URI_Parser_parseURIReference(v___x_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_pos_1029_; lean_object* v_array_1030_; lean_object* v_idx_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_pos_1029_ = lean_ctor_get(v___x_1028_, 0);
v_array_1030_ = lean_ctor_get(v_pos_1029_, 0);
v_idx_1031_ = lean_ctor_get(v_pos_1029_, 1);
v___x_1032_ = lean_byte_array_size(v_array_1030_);
v___x_1033_ = lean_nat_dec_lt(v_idx_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
return v___x_1028_;
}
else
{
lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1041_; 
lean_inc(v_pos_1029_);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; lean_object* v_unused_1043_; 
v_unused_1042_ = lean_ctor_get(v___x_1028_, 1);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v___x_1028_, 0);
lean_dec(v_unused_1043_);
v___x_1035_ = v___x_1028_;
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v___x_1028_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 1);
lean_ctor_set(v___x_1035_, 1, v___x_1037_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_pos_1029_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_1056_, lean_object* v_request_1057_, uint8_t v_bodyReplayable_1058_, uint8_t v_onlySafeRedirects_1059_, uint8_t v_responseVersion_1060_, lean_object* v_status_1061_, lean_object* v_responseHeaders_1062_){
_start:
{
lean_object* v___y_1064_; uint8_t v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1078_; uint8_t v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; uint8_t v___y_1083_; lean_object* v___y_1086_; uint8_t v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1092_; uint8_t v___y_1093_; lean_object* v___y_1099_; uint8_t v___y_1100_; uint8_t v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; uint8_t v___y_1105_; uint8_t v___y_1106_; uint8_t v___y_1107_; lean_object* v___y_1111_; uint8_t v___y_1112_; uint8_t v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; uint8_t v___y_1117_; uint8_t v___y_1118_; uint8_t v___y_1119_; lean_object* v___y_1123_; uint8_t v___y_1124_; uint8_t v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; uint8_t v___y_1129_; uint8_t v___y_1130_; uint8_t v___y_1131_; uint8_t v___y_1132_; lean_object* v___y_1135_; uint8_t v___y_1136_; uint8_t v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; uint8_t v___y_1141_; uint8_t v___y_1142_; uint8_t v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1146_; uint8_t v___y_1147_; uint8_t v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; uint8_t v___y_1151_; lean_object* v___y_1152_; uint8_t v___y_1153_; uint8_t v___y_1154_; uint8_t v___y_1155_; lean_object* v___y_1159_; uint8_t v___y_1160_; uint8_t v___y_1161_; uint8_t v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v___y_1166_; uint8_t v___y_1167_; uint8_t v___y_1168_; uint8_t v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1174_; uint8_t v___y_1175_; uint8_t v___y_1176_; uint8_t v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; uint8_t v___y_1181_; lean_object* v___y_1182_; uint8_t v___y_1183_; uint8_t v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1187_; uint8_t v___y_1188_; uint8_t v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; uint8_t v___y_1193_; uint8_t v___y_1194_; uint8_t v___y_1195_; uint8_t v___y_1196_; uint8_t v___y_1197_; lean_object* v___y_1201_; uint8_t v___y_1202_; uint8_t v___y_1203_; uint8_t v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; uint8_t v___y_1207_; lean_object* v___y_1208_; uint8_t v___y_1209_; uint8_t v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1213_; uint8_t v___y_1214_; uint8_t v___y_1215_; lean_object* v___y_1216_; uint8_t v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1220_; uint8_t v___y_1221_; uint8_t v___y_1222_; uint8_t v___y_1223_; uint8_t v___y_1224_; uint16_t v___x_1227_; uint16_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1227_ = 300;
v___x_1228_ = l_Std_Http_Status_toCode(v_status_1061_);
v___x_1229_ = lean_uint16_dec_le(v___x_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref(v_current_1056_);
v___x_1230_ = lean_box(0);
return v___x_1230_;
}
else
{
uint16_t v___x_1231_; uint8_t v___x_1232_; lean_object* v___y_1234_; uint8_t v___y_1235_; uint8_t v___y_1236_; lean_object* v___y_1237_; uint8_t v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v___y_1241_; uint8_t v___y_1242_; uint8_t v___y_1243_; lean_object* v___y_1249_; uint8_t v___y_1250_; lean_object* v___y_1251_; uint8_t v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; uint8_t v___y_1255_; uint8_t v___y_1256_; uint8_t v___y_1257_; lean_object* v___y_1260_; lean_object* v___y_1261_; uint8_t v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; uint8_t v___y_1265_; uint8_t v___y_1266_; uint8_t v___y_1267_; 
v___x_1231_ = 400;
v___x_1232_ = lean_uint16_dec_lt(v___x_1228_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1269_; 
lean_dec_ref(v_current_1056_);
v___x_1269_ = lean_box(0);
return v___x_1269_;
}
else
{
uint8_t v___x_1270_; lean_object* v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; uint8_t v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; uint8_t v___y_1278_; uint8_t v___y_1279_; uint8_t v___y_1280_; uint8_t v___y_1287_; uint8_t v___x_1330_; uint8_t v___x_1331_; 
v___x_1270_ = 0;
v___x_1330_ = 0;
v___x_1331_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_1060_, v___x_1330_);
if (v___x_1331_ == 0)
{
goto v___jp_1313_;
}
else
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_box(15);
v___x_1333_ = l_Std_Http_instBEqStatus_beq(v_status_1061_, v___x_1332_);
if (v___x_1333_ == 0)
{
if (v___x_1331_ == 0)
{
goto v___jp_1313_;
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_box(16);
v___x_1335_ = l_Std_Http_instBEqStatus_beq(v_status_1061_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref(v_current_1056_);
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
else
{
goto v___jp_1313_;
}
}
}
else
{
goto v___jp_1313_;
}
}
v___jp_1271_:
{
if (v___y_1280_ == 0)
{
v___y_1260_ = v___y_1272_;
v___y_1261_ = v___y_1274_;
v___y_1262_ = v___y_1275_;
v___y_1263_ = v___y_1276_;
v___y_1264_ = v___y_1277_;
v___y_1265_ = v___y_1279_;
v___y_1266_ = v___y_1278_;
v___y_1267_ = v___x_1270_;
goto v___jp_1259_;
}
else
{
lean_object* v_scheme_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_scheme_1281_ = lean_ctor_get(v___y_1272_, 0);
v___x_1282_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__0));
v___x_1283_ = lean_string_dec_eq(v_scheme_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_current_1056_);
v___x_1284_ = lean_box(0);
return v___x_1284_;
}
else
{
if (v___y_1273_ == 0)
{
v___y_1260_ = v___y_1272_;
v___y_1261_ = v___y_1274_;
v___y_1262_ = v___y_1275_;
v___y_1263_ = v___y_1276_;
v___y_1264_ = v___y_1277_;
v___y_1265_ = v___y_1279_;
v___y_1266_ = v___y_1278_;
v___y_1267_ = v___y_1273_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1285_; 
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_current_1056_);
v___x_1285_ = lean_box(0);
return v___x_1285_;
}
}
}
}
v___jp_1286_:
{
lean_object* v_entries_1288_; lean_object* v_indexes_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_entries_1288_ = lean_ctor_get(v_responseHeaders_1062_, 0);
v_indexes_1289_ = lean_ctor_get(v_responseHeaders_1062_, 1);
v___x_1290_ = l_Std_Http_Header_Name_location;
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_dec_ref(v_current_1056_);
v___x_1292_ = lean_box(0);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_entry_1295_; lean_object* v___x_1296_; lean_object* v_snd_1297_; lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_1289_, v___x_1290_);
v___x_1294_ = lean_unsigned_to_nat(0u);
v_entry_1295_ = lean_array_fget(v___x_1293_, v___x_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_array_fget_borrowed(v_entries_1288_, v_entry_1295_);
lean_dec(v_entry_1295_);
v_snd_1297_ = lean_ctor_get(v___x_1296_, 1);
v___f_1298_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
v___x_1299_ = lean_string_to_utf8(v_snd_1297_);
v___x_1300_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1298_, v___x_1299_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v___x_1301_; 
lean_dec_ref_known(v___x_1300_, 1);
lean_dec_ref(v_current_1056_);
v___x_1301_ = lean_box(0);
return v___x_1301_;
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1303_; 
v_a_1302_ = lean_ctor_get(v___x_1300_, 0);
lean_inc_n(v_a_1302_, 2);
lean_dec_ref_known(v___x_1300_, 1);
lean_inc_ref(v_current_1056_);
v___x_1303_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_1056_, v_a_1302_);
if (lean_obj_tag(v___x_1303_) == 1)
{
lean_object* v_val_1304_; uint8_t v_method_1305_; lean_object* v_uri_1306_; lean_object* v_headers_1307_; lean_object* v_scheme_1308_; uint8_t v_newMethod_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_val_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v_method_1305_ = lean_ctor_get_uint8(v_request_1057_, sizeof(void*)*2);
v_uri_1306_ = lean_ctor_get(v_request_1057_, 0);
v_headers_1307_ = lean_ctor_get(v_request_1057_, 1);
v_scheme_1308_ = lean_ctor_get(v_val_1304_, 0);
v_newMethod_1309_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_1305_, v_responseVersion_1060_, v_status_1061_);
v___x_1310_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_1311_ = lean_string_dec_eq(v_scheme_1308_, v___x_1310_);
if (v___x_1311_ == 0)
{
v___y_1272_ = v_val_1304_;
v___y_1273_ = v___y_1287_;
v___y_1274_ = v_a_1302_;
v___y_1275_ = v_method_1305_;
v___y_1276_ = v_uri_1306_;
v___y_1277_ = v_headers_1307_;
v___y_1278_ = v___x_1291_;
v___y_1279_ = v_newMethod_1309_;
v___y_1280_ = v___x_1291_;
goto v___jp_1271_;
}
else
{
v___y_1272_ = v_val_1304_;
v___y_1273_ = v___y_1287_;
v___y_1274_ = v_a_1302_;
v___y_1275_ = v_method_1305_;
v___y_1276_ = v_uri_1306_;
v___y_1277_ = v_headers_1307_;
v___y_1278_ = v___x_1291_;
v___y_1279_ = v_newMethod_1309_;
v___y_1280_ = v___y_1287_;
goto v___jp_1271_;
}
}
else
{
lean_object* v___x_1312_; 
lean_dec(v___x_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_current_1056_);
v___x_1312_ = lean_box(0);
return v___x_1312_;
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_box(19);
v___x_1315_ = l_Std_Http_instBEqStatus_beq(v_status_1061_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = lean_box(20);
v___x_1317_ = l_Std_Http_instBEqStatus_beq(v_status_1061_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = lean_box(18);
v___x_1319_ = l_Std_Http_instBEqStatus_beq(v_status_1061_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = lean_box(14);
v___x_1321_ = l_Std_Http_instBEqStatus_beq(v_status_1061_, v___x_1320_);
if (v___x_1321_ == 0)
{
if (v_onlySafeRedirects_1059_ == 0)
{
v___y_1287_ = v___x_1270_;
goto v___jp_1286_;
}
else
{
uint8_t v_method_1322_; uint8_t v___x_1323_; 
v_method_1322_ = lean_ctor_get_uint8(v_request_1057_, sizeof(void*)*2);
v___x_1323_ = l_Std_Http_Method_isSafe(v_method_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref(v_current_1056_);
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
else
{
if (v___x_1321_ == 0)
{
v___y_1287_ = v___x_1321_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1325_; 
lean_dec_ref(v_current_1056_);
v___x_1325_ = lean_box(0);
return v___x_1325_;
}
}
}
}
else
{
lean_object* v___x_1326_; 
lean_dec_ref(v_current_1056_);
v___x_1326_ = lean_box(0);
return v___x_1326_;
}
}
else
{
lean_object* v___x_1327_; 
lean_dec_ref(v_current_1056_);
v___x_1327_ = lean_box(0);
return v___x_1327_;
}
}
else
{
lean_object* v___x_1328_; 
lean_dec_ref(v_current_1056_);
v___x_1328_ = lean_box(0);
return v___x_1328_;
}
}
else
{
lean_object* v___x_1329_; 
lean_dec_ref(v_current_1056_);
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
}
}
v___jp_1233_:
{
uint8_t v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = 8;
v___x_1245_ = l_Std_Http_instBEqMethod_beq(v___y_1238_, v___x_1244_);
if (v___x_1245_ == 0)
{
uint8_t v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = 9;
v___x_1247_ = l_Std_Http_instBEqMethod_beq(v___y_1238_, v___x_1246_);
v___y_1213_ = v___y_1234_;
v___y_1214_ = v___y_1235_;
v___y_1215_ = v___y_1236_;
v___y_1216_ = v___y_1237_;
v___y_1217_ = v___y_1238_;
v___y_1218_ = v___y_1239_;
v___y_1219_ = v___y_1240_;
v___y_1220_ = v___x_1244_;
v___y_1221_ = v___y_1243_;
v___y_1222_ = v___y_1242_;
v___y_1223_ = v___y_1241_;
v___y_1224_ = v___x_1247_;
goto v___jp_1212_;
}
else
{
v___y_1213_ = v___y_1234_;
v___y_1214_ = v___y_1235_;
v___y_1215_ = v___y_1236_;
v___y_1216_ = v___y_1237_;
v___y_1217_ = v___y_1238_;
v___y_1218_ = v___y_1239_;
v___y_1219_ = v___y_1240_;
v___y_1220_ = v___x_1244_;
v___y_1221_ = v___y_1243_;
v___y_1222_ = v___y_1242_;
v___y_1223_ = v___y_1241_;
v___y_1224_ = v___x_1232_;
goto v___jp_1212_;
}
}
v___jp_1248_:
{
uint8_t v___x_1258_; 
v___x_1258_ = l_Std_Http_instBEqMethod_beq(v___y_1256_, v___y_1252_);
if (v___x_1258_ == 0)
{
v___y_1234_ = v___y_1249_;
v___y_1235_ = v___y_1257_;
v___y_1236_ = v___y_1250_;
v___y_1237_ = v___y_1251_;
v___y_1238_ = v___y_1252_;
v___y_1239_ = v___y_1253_;
v___y_1240_ = v___y_1254_;
v___y_1241_ = v___y_1256_;
v___y_1242_ = v___y_1255_;
v___y_1243_ = v___y_1255_;
goto v___jp_1233_;
}
else
{
v___y_1234_ = v___y_1249_;
v___y_1235_ = v___y_1257_;
v___y_1236_ = v___y_1250_;
v___y_1237_ = v___y_1251_;
v___y_1238_ = v___y_1252_;
v___y_1239_ = v___y_1253_;
v___y_1240_ = v___y_1254_;
v___y_1241_ = v___y_1256_;
v___y_1242_ = v___y_1255_;
v___y_1243_ = v___y_1250_;
goto v___jp_1233_;
}
}
v___jp_1259_:
{
uint8_t v___x_1268_; 
v___x_1268_ = l_Std_Http_URI_instBEqOrigin_beq(v___y_1260_, v_current_1056_);
if (v___x_1268_ == 0)
{
v___y_1249_ = v___y_1260_;
v___y_1250_ = v___y_1267_;
v___y_1251_ = v___y_1261_;
v___y_1252_ = v___y_1262_;
v___y_1253_ = v___y_1263_;
v___y_1254_ = v___y_1264_;
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___y_1265_;
v___y_1257_ = v___y_1266_;
goto v___jp_1248_;
}
else
{
v___y_1249_ = v___y_1260_;
v___y_1250_ = v___y_1267_;
v___y_1251_ = v___y_1261_;
v___y_1252_ = v___y_1262_;
v___y_1253_ = v___y_1263_;
v___y_1254_ = v___y_1264_;
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___y_1265_;
v___y_1257_ = v___y_1267_;
goto v___jp_1248_;
}
}
}
v___jp_1063_:
{
lean_object* v_scheme_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_rewrittenTarget_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_scheme_1071_ = lean_ctor_get(v_current_1056_, 0);
lean_inc_ref(v_scheme_1071_);
lean_dec_ref(v_current_1056_);
v___x_1072_ = l_Std_Http_RequestTarget_pathOrRoot(v___y_1068_);
v___x_1073_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v___y_1068_);
v_rewrittenTarget_1074_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v___y_1066_, v___y_1065_, v___x_1072_, v___x_1073_, v_scheme_1071_);
v___x_1075_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1075_, 0, v___y_1064_);
lean_ctor_set(v___x_1075_, 1, v_rewrittenTarget_1074_);
lean_ctor_set(v___x_1075_, 2, v___y_1067_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*3, v___y_1069_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*3 + 1, v___y_1070_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*3 + 2, v___y_1065_);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
v___jp_1077_:
{
uint8_t v___x_1084_; 
v___x_1084_ = 0;
v___y_1064_ = v___y_1078_;
v___y_1065_ = v___y_1079_;
v___y_1066_ = v___y_1080_;
v___y_1067_ = v___y_1082_;
v___y_1068_ = v___y_1081_;
v___y_1069_ = v___y_1083_;
v___y_1070_ = v___x_1084_;
goto v___jp_1063_;
}
v___jp_1085_:
{
uint8_t v___x_1094_; 
v___x_1094_ = l_Std_Http_instBEqMethod_beq(v___y_1093_, v___y_1091_);
if (v___x_1094_ == 0)
{
uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = 9;
v___x_1096_ = l_Std_Http_instBEqMethod_beq(v___y_1093_, v___x_1095_);
if (v___x_1096_ == 0)
{
if (v___y_1092_ == 0)
{
uint8_t v___x_1097_; 
v___x_1097_ = 1;
v___y_1064_ = v___y_1086_;
v___y_1065_ = v___y_1087_;
v___y_1066_ = v___y_1088_;
v___y_1067_ = v___y_1090_;
v___y_1068_ = v___y_1089_;
v___y_1069_ = v___y_1093_;
v___y_1070_ = v___x_1097_;
goto v___jp_1063_;
}
else
{
v___y_1078_ = v___y_1086_;
v___y_1079_ = v___y_1087_;
v___y_1080_ = v___y_1088_;
v___y_1081_ = v___y_1089_;
v___y_1082_ = v___y_1090_;
v___y_1083_ = v___y_1093_;
goto v___jp_1077_;
}
}
else
{
v___y_1078_ = v___y_1086_;
v___y_1079_ = v___y_1087_;
v___y_1080_ = v___y_1088_;
v___y_1081_ = v___y_1089_;
v___y_1082_ = v___y_1090_;
v___y_1083_ = v___y_1093_;
goto v___jp_1077_;
}
}
else
{
v___y_1078_ = v___y_1086_;
v___y_1079_ = v___y_1087_;
v___y_1080_ = v___y_1088_;
v___y_1081_ = v___y_1089_;
v___y_1082_ = v___y_1090_;
v___y_1083_ = v___y_1093_;
goto v___jp_1077_;
}
}
v___jp_1098_:
{
if (v_bodyReplayable_1058_ == 0)
{
lean_object* v___x_1108_; 
lean_dec_ref(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v___y_1099_);
lean_dec_ref(v_current_1056_);
v___x_1108_ = lean_box(0);
return v___x_1108_;
}
else
{
if (v___y_1101_ == 0)
{
v___y_1086_ = v___y_1099_;
v___y_1087_ = v___y_1100_;
v___y_1088_ = v___y_1102_;
v___y_1089_ = v___y_1104_;
v___y_1090_ = v___y_1103_;
v___y_1091_ = v___y_1105_;
v___y_1092_ = v___y_1106_;
v___y_1093_ = v___y_1107_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1109_; 
lean_dec_ref(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v___y_1099_);
lean_dec_ref(v_current_1056_);
v___x_1109_ = lean_box(0);
return v___x_1109_;
}
}
}
v___jp_1110_:
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 9;
v___x_1121_ = l_Std_Http_instBEqMethod_beq(v___y_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
v___y_1099_ = v___y_1111_;
v___y_1100_ = v___y_1112_;
v___y_1101_ = v___y_1113_;
v___y_1102_ = v___y_1114_;
v___y_1103_ = v___y_1116_;
v___y_1104_ = v___y_1115_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___y_1118_;
v___y_1107_ = v___y_1119_;
goto v___jp_1098_;
}
else
{
if (v___y_1113_ == 0)
{
v___y_1086_ = v___y_1111_;
v___y_1087_ = v___y_1112_;
v___y_1088_ = v___y_1114_;
v___y_1089_ = v___y_1115_;
v___y_1090_ = v___y_1116_;
v___y_1091_ = v___y_1117_;
v___y_1092_ = v___y_1118_;
v___y_1093_ = v___y_1119_;
goto v___jp_1085_;
}
else
{
v___y_1099_ = v___y_1111_;
v___y_1100_ = v___y_1112_;
v___y_1101_ = v___y_1113_;
v___y_1102_ = v___y_1114_;
v___y_1103_ = v___y_1116_;
v___y_1104_ = v___y_1115_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___y_1118_;
v___y_1107_ = v___y_1119_;
goto v___jp_1098_;
}
}
}
v___jp_1122_:
{
if (v___y_1132_ == 0)
{
v___y_1086_ = v___y_1123_;
v___y_1087_ = v___y_1124_;
v___y_1088_ = v___y_1126_;
v___y_1089_ = v___y_1128_;
v___y_1090_ = v___y_1127_;
v___y_1091_ = v___y_1129_;
v___y_1092_ = v___y_1130_;
v___y_1093_ = v___y_1131_;
goto v___jp_1085_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Std_Http_instBEqMethod_beq(v___y_1131_, v___y_1129_);
if (v___x_1133_ == 0)
{
v___y_1111_ = v___y_1123_;
v___y_1112_ = v___y_1124_;
v___y_1113_ = v___y_1125_;
v___y_1114_ = v___y_1126_;
v___y_1115_ = v___y_1128_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
v___y_1119_ = v___y_1131_;
goto v___jp_1110_;
}
else
{
if (v___y_1125_ == 0)
{
v___y_1086_ = v___y_1123_;
v___y_1087_ = v___y_1124_;
v___y_1088_ = v___y_1126_;
v___y_1089_ = v___y_1128_;
v___y_1090_ = v___y_1127_;
v___y_1091_ = v___y_1129_;
v___y_1092_ = v___y_1130_;
v___y_1093_ = v___y_1131_;
goto v___jp_1085_;
}
else
{
v___y_1111_ = v___y_1123_;
v___y_1112_ = v___y_1124_;
v___y_1113_ = v___y_1125_;
v___y_1114_ = v___y_1126_;
v___y_1115_ = v___y_1128_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
v___y_1119_ = v___y_1131_;
goto v___jp_1110_;
}
}
}
}
v___jp_1134_:
{
if (v___y_1141_ == 0)
{
v___y_1123_ = v___y_1135_;
v___y_1124_ = v___y_1136_;
v___y_1125_ = v___y_1137_;
v___y_1126_ = v___y_1138_;
v___y_1127_ = v___y_1144_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___y_1140_;
v___y_1130_ = v___y_1141_;
v___y_1131_ = v___y_1143_;
v___y_1132_ = v___y_1142_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v___y_1135_;
v___y_1124_ = v___y_1136_;
v___y_1125_ = v___y_1137_;
v___y_1126_ = v___y_1138_;
v___y_1127_ = v___y_1144_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___y_1140_;
v___y_1130_ = v___y_1141_;
v___y_1131_ = v___y_1143_;
v___y_1132_ = v___y_1137_;
goto v___jp_1122_;
}
}
v___jp_1145_:
{
lean_object* v_scrubbed_1156_; 
v_scrubbed_1156_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v___y_1152_, v___y_1147_, v___y_1153_);
if (v___y_1147_ == 0)
{
v___y_1135_ = v___y_1146_;
v___y_1136_ = v___y_1147_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1150_;
v___y_1140_ = v___y_1151_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1155_;
v___y_1143_ = v___y_1154_;
v___y_1144_ = v_scrubbed_1156_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1157_; 
lean_inc_ref(v___y_1146_);
v___x_1157_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_1156_, v___y_1146_);
v___y_1135_ = v___y_1146_;
v___y_1136_ = v___y_1147_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1150_;
v___y_1140_ = v___y_1151_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1155_;
v___y_1143_ = v___y_1154_;
v___y_1144_ = v___x_1157_;
goto v___jp_1134_;
}
}
v___jp_1158_:
{
if (v___y_1170_ == 0)
{
v___y_1146_ = v___y_1159_;
v___y_1147_ = v___y_1161_;
v___y_1148_ = v___y_1162_;
v___y_1149_ = v___y_1163_;
v___y_1150_ = v___y_1164_;
v___y_1151_ = v___y_1166_;
v___y_1152_ = v___y_1165_;
v___y_1153_ = v___y_1167_;
v___y_1154_ = v___y_1169_;
v___y_1155_ = v___y_1168_;
goto v___jp_1145_;
}
else
{
if (v___y_1160_ == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref(v___y_1163_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_current_1056_);
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
else
{
if (v___y_1162_ == 0)
{
v___y_1146_ = v___y_1159_;
v___y_1147_ = v___y_1161_;
v___y_1148_ = v___y_1162_;
v___y_1149_ = v___y_1163_;
v___y_1150_ = v___y_1164_;
v___y_1151_ = v___y_1166_;
v___y_1152_ = v___y_1165_;
v___y_1153_ = v___y_1167_;
v___y_1154_ = v___y_1169_;
v___y_1155_ = v___y_1168_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1172_; 
lean_dec_ref(v___y_1163_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_current_1056_);
v___x_1172_ = lean_box(0);
return v___x_1172_;
}
}
}
}
v___jp_1173_:
{
if (v___y_1175_ == 0)
{
v___y_1159_ = v___y_1174_;
v___y_1160_ = v___y_1176_;
v___y_1161_ = v___y_1177_;
v___y_1162_ = v___y_1178_;
v___y_1163_ = v___y_1179_;
v___y_1164_ = v___y_1180_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1181_;
v___y_1167_ = v___y_1183_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1185_;
goto v___jp_1158_;
}
else
{
v___y_1159_ = v___y_1174_;
v___y_1160_ = v___y_1176_;
v___y_1161_ = v___y_1177_;
v___y_1162_ = v___y_1178_;
v___y_1163_ = v___y_1179_;
v___y_1164_ = v___y_1180_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1181_;
v___y_1167_ = v___y_1183_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1178_;
goto v___jp_1158_;
}
}
v___jp_1186_:
{
if (v___y_1197_ == 0)
{
v___y_1146_ = v___y_1187_;
v___y_1147_ = v___y_1188_;
v___y_1148_ = v___y_1189_;
v___y_1149_ = v___y_1190_;
v___y_1150_ = v___y_1191_;
v___y_1151_ = v___y_1193_;
v___y_1152_ = v___y_1192_;
v___y_1153_ = v___y_1194_;
v___y_1154_ = v___y_1196_;
v___y_1155_ = v___y_1195_;
goto v___jp_1145_;
}
else
{
if (v_bodyReplayable_1058_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v___y_1190_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_current_1056_);
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
else
{
if (v___y_1189_ == 0)
{
v___y_1146_ = v___y_1187_;
v___y_1147_ = v___y_1188_;
v___y_1148_ = v___y_1189_;
v___y_1149_ = v___y_1190_;
v___y_1150_ = v___y_1191_;
v___y_1151_ = v___y_1193_;
v___y_1152_ = v___y_1192_;
v___y_1153_ = v___y_1194_;
v___y_1154_ = v___y_1196_;
v___y_1155_ = v___y_1195_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1199_; 
lean_dec_ref(v___y_1190_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_current_1056_);
v___x_1199_ = lean_box(0);
return v___x_1199_;
}
}
}
}
v___jp_1200_:
{
if (v___y_1202_ == 0)
{
v___y_1187_ = v___y_1201_;
v___y_1188_ = v___y_1203_;
v___y_1189_ = v___y_1204_;
v___y_1190_ = v___y_1205_;
v___y_1191_ = v___y_1206_;
v___y_1192_ = v___y_1208_;
v___y_1193_ = v___y_1207_;
v___y_1194_ = v___y_1209_;
v___y_1195_ = v___y_1211_;
v___y_1196_ = v___y_1210_;
v___y_1197_ = v___y_1211_;
goto v___jp_1186_;
}
else
{
v___y_1187_ = v___y_1201_;
v___y_1188_ = v___y_1203_;
v___y_1189_ = v___y_1204_;
v___y_1190_ = v___y_1205_;
v___y_1191_ = v___y_1206_;
v___y_1192_ = v___y_1208_;
v___y_1193_ = v___y_1207_;
v___y_1194_ = v___y_1209_;
v___y_1195_ = v___y_1211_;
v___y_1196_ = v___y_1210_;
v___y_1197_ = v___y_1204_;
goto v___jp_1186_;
}
}
v___jp_1212_:
{
uint8_t v___x_1225_; uint8_t v_isPost_1226_; 
v___x_1225_ = 23;
v_isPost_1226_ = l_Std_Http_instBEqMethod_beq(v___y_1217_, v___x_1225_);
switch(lean_obj_tag(v_status_1061_))
{
case 15:
{
v___y_1174_ = v___y_1213_;
v___y_1175_ = v___y_1224_;
v___y_1176_ = v_isPost_1226_;
v___y_1177_ = v___y_1214_;
v___y_1178_ = v___y_1215_;
v___y_1179_ = v___y_1216_;
v___y_1180_ = v___y_1218_;
v___y_1181_ = v___y_1220_;
v___y_1182_ = v___y_1219_;
v___y_1183_ = v___y_1221_;
v___y_1184_ = v___y_1223_;
v___y_1185_ = v___y_1222_;
goto v___jp_1173_;
}
case 16:
{
v___y_1174_ = v___y_1213_;
v___y_1175_ = v___y_1224_;
v___y_1176_ = v_isPost_1226_;
v___y_1177_ = v___y_1214_;
v___y_1178_ = v___y_1215_;
v___y_1179_ = v___y_1216_;
v___y_1180_ = v___y_1218_;
v___y_1181_ = v___y_1220_;
v___y_1182_ = v___y_1219_;
v___y_1183_ = v___y_1221_;
v___y_1184_ = v___y_1223_;
v___y_1185_ = v___y_1222_;
goto v___jp_1173_;
}
case 21:
{
v___y_1201_ = v___y_1213_;
v___y_1202_ = v___y_1224_;
v___y_1203_ = v___y_1214_;
v___y_1204_ = v___y_1215_;
v___y_1205_ = v___y_1216_;
v___y_1206_ = v___y_1218_;
v___y_1207_ = v___y_1220_;
v___y_1208_ = v___y_1219_;
v___y_1209_ = v___y_1221_;
v___y_1210_ = v___y_1223_;
v___y_1211_ = v___y_1222_;
goto v___jp_1200_;
}
case 22:
{
v___y_1201_ = v___y_1213_;
v___y_1202_ = v___y_1224_;
v___y_1203_ = v___y_1214_;
v___y_1204_ = v___y_1215_;
v___y_1205_ = v___y_1216_;
v___y_1206_ = v___y_1218_;
v___y_1207_ = v___y_1220_;
v___y_1208_ = v___y_1219_;
v___y_1209_ = v___y_1221_;
v___y_1210_ = v___y_1223_;
v___y_1211_ = v___y_1222_;
goto v___jp_1200_;
}
default: 
{
v___y_1146_ = v___y_1213_;
v___y_1147_ = v___y_1214_;
v___y_1148_ = v___y_1215_;
v___y_1149_ = v___y_1216_;
v___y_1150_ = v___y_1218_;
v___y_1151_ = v___y_1220_;
v___y_1152_ = v___y_1219_;
v___y_1153_ = v___y_1221_;
v___y_1154_ = v___y_1223_;
v___y_1155_ = v___y_1222_;
goto v___jp_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_1337_, lean_object* v_request_1338_, lean_object* v_bodyReplayable_1339_, lean_object* v_onlySafeRedirects_1340_, lean_object* v_responseVersion_1341_, lean_object* v_status_1342_, lean_object* v_responseHeaders_1343_){
_start:
{
uint8_t v_bodyReplayable_boxed_1344_; uint8_t v_onlySafeRedirects_boxed_1345_; uint8_t v_responseVersion_boxed_1346_; lean_object* v_res_1347_; 
v_bodyReplayable_boxed_1344_ = lean_unbox(v_bodyReplayable_1339_);
v_onlySafeRedirects_boxed_1345_ = lean_unbox(v_onlySafeRedirects_1340_);
v_responseVersion_boxed_1346_ = lean_unbox(v_responseVersion_1341_);
v_res_1347_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1337_, v_request_1338_, v_bodyReplayable_boxed_1344_, v_onlySafeRedirects_boxed_1345_, v_responseVersion_boxed_1346_, v_status_1342_, v_responseHeaders_1343_);
lean_dec_ref(v_responseHeaders_1343_);
lean_dec(v_status_1342_);
lean_dec_ref(v_request_1338_);
return v_res_1347_;
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
