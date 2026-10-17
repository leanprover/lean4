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
switch(lean_obj_tag(v_x_336_))
{
case 17:
{
uint8_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 9;
v___x_344_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_334_, v___x_343_);
if (v___x_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = 8;
return v___x_345_;
}
else
{
return v___x_343_;
}
}
case 15:
{
goto v___jp_337_;
}
case 16:
{
goto v___jp_337_;
}
default: 
{
return v_originalMethod_334_;
}
}
v___jp_337_:
{
uint8_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 23;
v___x_339_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_334_, v___x_338_);
if (v___x_339_ == 0)
{
return v_originalMethod_334_;
}
else
{
uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 0;
v___x_341_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_335_, v___x_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
v___x_342_ = 8;
return v___x_342_;
}
else
{
return v_originalMethod_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_346_, lean_object* v_responseVersion_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_originalMethod_boxed_349_; uint8_t v_responseVersion_boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_originalMethod_boxed_349_ = lean_unbox(v_originalMethod_346_);
v_responseVersion_boxed_350_ = lean_unbox(v_responseVersion_347_);
v_res_351_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_349_, v_responseVersion_boxed_350_, v_x_348_);
lean_dec(v_x_348_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_353_ = l_Std_Http_Header_Name_transferEncoding;
v___x_354_ = l_Std_Http_Header_Name_keepAlive;
v___x_355_ = l_Std_Http_Header_Name_connection;
v___x_356_ = lean_unsigned_to_nat(3u);
v___x_357_ = lean_mk_empty_array_with_capacity(v___x_356_);
v___x_358_ = lean_array_push(v___x_357_, v___x_355_);
v___x_359_ = lean_array_push(v___x_358_, v___x_354_);
v___x_360_ = lean_array_push(v___x_359_, v___x_353_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_361_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object* v_a_362_, lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
else
{
lean_object* v_key_365_; lean_object* v_tail_366_; uint8_t v___x_367_; 
v_key_365_ = lean_ctor_get(v_x_363_, 0);
v_tail_366_ = lean_ctor_get(v_x_363_, 2);
v___x_367_ = lean_string_dec_eq(v_key_365_, v_a_362_);
if (v___x_367_ == 0)
{
v_x_363_ = v_tail_366_;
goto _start;
}
else
{
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object* v_a_369_, lean_object* v_x_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_369_, v_x_370_);
lean_dec(v_x_370_);
lean_dec_ref(v_a_369_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object* v_m_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_buckets_375_; lean_object* v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; uint64_t v___x_379_; uint64_t v_fold_380_; uint64_t v___x_381_; uint64_t v___x_382_; uint64_t v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_buckets_375_ = lean_ctor_get(v_m_373_, 1);
v___x_376_ = lean_array_get_size(v_buckets_375_);
v___x_377_ = lean_string_hash(v_a_374_);
v___x_378_ = 32ULL;
v___x_379_ = lean_uint64_shift_right(v___x_377_, v___x_378_);
v_fold_380_ = lean_uint64_xor(v___x_377_, v___x_379_);
v___x_381_ = 16ULL;
v___x_382_ = lean_uint64_shift_right(v_fold_380_, v___x_381_);
v___x_383_ = lean_uint64_xor(v_fold_380_, v___x_382_);
v___x_384_ = lean_uint64_to_usize(v___x_383_);
v___x_385_ = lean_usize_of_nat(v___x_376_);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_sub(v___x_385_, v___x_386_);
v___x_388_ = lean_usize_land(v___x_384_, v___x_387_);
v___x_389_ = lean_array_uget_borrowed(v_buckets_375_, v___x_388_);
v___x_390_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_374_, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object* v_m_391_, lean_object* v_a_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_391_, v_a_392_);
lean_dec_ref(v_a_392_);
lean_dec_ref(v_m_391_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(lean_object* v_a_395_, lean_object* v_x_396_){
_start:
{
lean_object* v_key_397_; lean_object* v_value_398_; lean_object* v_tail_399_; uint8_t v___x_400_; 
v_key_397_ = lean_ctor_get(v_x_396_, 0);
v_value_398_ = lean_ctor_get(v_x_396_, 1);
v_tail_399_ = lean_ctor_get(v_x_396_, 2);
v___x_400_ = lean_string_dec_eq(v_key_397_, v_a_395_);
if (v___x_400_ == 0)
{
v_x_396_ = v_tail_399_;
goto _start;
}
else
{
lean_inc(v_value_398_);
return v_value_398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg___boxed(lean_object* v_a_402_, lean_object* v_x_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_402_, v_x_403_);
lean_dec(v_x_403_);
lean_dec_ref(v_a_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object* v_m_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_buckets_407_; lean_object* v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v_fold_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_buckets_407_ = lean_ctor_get(v_m_405_, 1);
v___x_408_ = lean_array_get_size(v_buckets_407_);
v___x_409_ = lean_string_hash(v_a_406_);
v___x_410_ = 32ULL;
v___x_411_ = lean_uint64_shift_right(v___x_409_, v___x_410_);
v_fold_412_ = lean_uint64_xor(v___x_409_, v___x_411_);
v___x_413_ = 16ULL;
v___x_414_ = lean_uint64_shift_right(v_fold_412_, v___x_413_);
v___x_415_ = lean_uint64_xor(v_fold_412_, v___x_414_);
v___x_416_ = lean_uint64_to_usize(v___x_415_);
v___x_417_ = lean_usize_of_nat(v___x_408_);
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_sub(v___x_417_, v___x_418_);
v___x_420_ = lean_usize_land(v___x_416_, v___x_419_);
v___x_421_ = lean_array_uget_borrowed(v_buckets_407_, v___x_420_);
v___x_422_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_406_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object* v_m_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_m_423_, v_a_424_);
lean_dec_ref(v_a_424_);
lean_dec_ref(v_m_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_426_, size_t v_i_427_, size_t v_stop_428_, lean_object* v_b_429_){
_start:
{
lean_object* v___y_431_; uint8_t v___x_435_; 
v___x_435_ = lean_usize_dec_eq(v_i_427_, v_stop_428_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_array_uget_borrowed(v_as_426_, v_i_427_);
lean_inc(v___x_436_);
v___x_437_ = l_Std_Http_Header_Name_ofString_x3f(v___x_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
v___y_431_ = v_b_429_;
goto v___jp_430_;
}
else
{
lean_object* v_val_438_; lean_object* v___x_439_; 
v_val_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_array_push(v_b_429_, v_val_438_);
v___y_431_ = v___x_439_;
goto v___jp_430_;
}
}
else
{
return v_b_429_;
}
v___jp_430_:
{
size_t v___x_432_; size_t v___x_433_; 
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_add(v_i_427_, v___x_432_);
v_i_427_ = v___x_433_;
v_b_429_ = v___y_431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_440_, lean_object* v_i_441_, lean_object* v_stop_442_, lean_object* v_b_443_){
_start:
{
size_t v_i_boxed_444_; size_t v_stop_boxed_445_; lean_object* v_res_446_; 
v_i_boxed_444_ = lean_unbox_usize(v_i_441_);
lean_dec(v_i_441_);
v_stop_boxed_445_ = lean_unbox_usize(v_stop_442_);
lean_dec(v_stop_442_);
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_440_, v_i_boxed_444_, v_stop_boxed_445_, v_b_443_);
lean_dec_ref(v_as_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(lean_object* v_as_447_, size_t v_i_448_, size_t v_stop_449_, lean_object* v_b_450_){
_start:
{
lean_object* v___y_452_; uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_eq(v_i_448_, v_stop_449_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_array_uget_borrowed(v_as_447_, v_i_448_);
lean_inc(v___x_457_);
v___x_458_ = l_Std_Http_Header_Connection_parse(v___x_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
v___y_452_ = v_b_450_;
goto v___jp_451_;
}
else
{
lean_object* v_val_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_val_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_array_get_size(v_val_459_);
v___x_462_ = lean_nat_dec_lt(v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_dec(v_val_459_);
v___y_452_ = v_b_450_;
goto v___jp_451_;
}
else
{
size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_461_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_459_, v___x_463_, v___x_464_, v_b_450_);
lean_dec(v_val_459_);
v___y_452_ = v___x_465_;
goto v___jp_451_;
}
}
}
else
{
return v_b_450_;
}
v___jp_451_:
{
size_t v___x_453_; size_t v___x_454_; 
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_add(v_i_448_, v___x_453_);
v_i_448_ = v___x_454_;
v_b_450_ = v___y_452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4___boxed(lean_object* v_as_466_, lean_object* v_i_467_, lean_object* v_stop_468_, lean_object* v_b_469_){
_start:
{
size_t v_i_boxed_470_; size_t v_stop_boxed_471_; lean_object* v_res_472_; 
v_i_boxed_470_ = lean_unbox_usize(v_i_467_);
lean_dec(v_i_467_);
v_stop_boxed_471_ = lean_unbox_usize(v_stop_468_);
lean_dec(v_stop_468_);
v_res_472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_as_466_, v_i_boxed_470_, v_stop_boxed_471_, v_b_469_);
lean_dec_ref(v_as_466_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(lean_object* v___x_473_, lean_object* v___x_474_, size_t v_sz_475_, size_t v_i_476_, lean_object* v_bs_477_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_lt(v_i_476_, v_sz_475_);
if (v___x_478_ == 0)
{
return v_bs_477_;
}
else
{
lean_object* v_entries_479_; lean_object* v___x_480_; lean_object* v_bs_x27_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_snd_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v_entries_479_ = lean_ctor_get(v___x_473_, 0);
v___x_480_ = lean_unsigned_to_nat(0u);
v_bs_x27_481_ = lean_array_uset(v_bs_477_, v_i_476_, v___x_480_);
v___x_482_ = lean_usize_to_nat(v_i_476_);
v___x_483_ = lean_array_fget_borrowed(v___x_474_, v___x_482_);
lean_dec(v___x_482_);
v___x_484_ = lean_array_fget_borrowed(v_entries_479_, v___x_483_);
v_snd_485_ = lean_ctor_get(v___x_484_, 1);
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_476_, v___x_486_);
lean_inc(v_snd_485_);
v___x_488_ = lean_array_uset(v_bs_x27_481_, v_i_476_, v_snd_485_);
v_i_476_ = v___x_487_;
v_bs_477_ = v___x_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg___boxed(lean_object* v___x_490_, lean_object* v___x_491_, lean_object* v_sz_492_, lean_object* v_i_493_, lean_object* v_bs_494_){
_start:
{
size_t v_sz_boxed_495_; size_t v_i_boxed_496_; lean_object* v_res_497_; 
v_sz_boxed_495_ = lean_unbox_usize(v_sz_492_);
lean_dec(v_sz_492_);
v_i_boxed_496_ = lean_unbox_usize(v_i_493_);
lean_dec(v_i_493_);
v_res_497_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_490_, v___x_491_, v_sz_boxed_495_, v_i_boxed_496_, v_bs_494_);
lean_dec_ref(v___x_491_);
lean_dec_ref(v___x_490_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_500_){
_start:
{
lean_object* v_indexes_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_indexes_501_ = lean_ctor_get(v_headers_500_, 1);
v___x_502_ = l_Std_Http_Header_Name_connection;
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
return v___x_504_;
}
else
{
lean_object* v___x_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v_entries_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_501_, v___x_502_);
v_sz_506_ = lean_array_size(v___x_505_);
v___x_507_ = ((size_t)0ULL);
lean_inc(v___x_505_);
v_entries_508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v_headers_500_, v___x_505_, v_sz_506_, v___x_507_, v___x_505_);
lean_dec(v___x_505_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_511_ = lean_array_get_size(v_entries_508_);
v___x_512_ = lean_nat_dec_lt(v___x_509_, v___x_511_);
if (v___x_512_ == 0)
{
lean_dec_ref(v_entries_508_);
return v___x_510_;
}
else
{
size_t v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_usize_of_nat(v___x_511_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_entries_508_, v___x_507_, v___x_513_, v___x_510_);
lean_dec_ref(v_entries_508_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_515_);
lean_dec_ref(v_headers_515_);
return v_res_516_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_00_u03b2_517_, lean_object* v_m_518_, lean_object* v_a_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_518_, v_a_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_00_u03b2_521_, lean_object* v_m_522_, lean_object* v_a_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_00_u03b2_521_, v_m_522_, v_a_523_);
lean_dec_ref(v_a_523_);
lean_dec_ref(v_m_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_a_528_, lean_object* v_hma_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_m_527_, v_a_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v_00_u03b2_531_, lean_object* v_m_532_, lean_object* v_a_533_, lean_object* v_hma_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_00_u03b2_531_, v_m_532_, v_a_533_, v_hma_534_);
lean_dec_ref(v_a_533_);
lean_dec_ref(v_m_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v_as_538_, size_t v_sz_539_, size_t v_i_540_, lean_object* v_bs_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_536_, v___x_537_, v_sz_539_, v_i_540_, v_bs_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v_as_545_, lean_object* v_sz_546_, lean_object* v_i_547_, lean_object* v_bs_548_){
_start:
{
size_t v_sz_boxed_549_; size_t v_i_boxed_550_; lean_object* v_res_551_; 
v_sz_boxed_549_ = lean_unbox_usize(v_sz_546_);
lean_dec(v_sz_546_);
v_i_boxed_550_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v___x_543_, v___x_544_, v_as_545_, v_sz_boxed_549_, v_i_boxed_550_, v_bs_548_);
lean_dec_ref(v_as_545_);
lean_dec_ref(v___x_544_);
lean_dec_ref(v___x_543_);
return v_res_551_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object* v_00_u03b2_552_, lean_object* v_a_553_, lean_object* v_x_554_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_553_, v_x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object* v_00_u03b2_556_, lean_object* v_a_557_, lean_object* v_x_558_){
_start:
{
uint8_t v_res_559_; lean_object* v_r_560_; 
v_res_559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(v_00_u03b2_556_, v_a_557_, v_x_558_);
lean_dec(v_x_558_);
lean_dec_ref(v_a_557_);
v_r_560_ = lean_box(v_res_559_);
return v_r_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(lean_object* v_00_u03b2_561_, lean_object* v_a_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_562_, v_x_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___boxed(lean_object* v_00_u03b2_566_, lean_object* v_a_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(v_00_u03b2_566_, v_a_567_, v_x_568_, v_x_569_);
lean_dec(v_x_568_);
lean_dec_ref(v_a_567_);
return v_res_570_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_571_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
v___x_574_ = lean_array_push(v___x_573_, v___x_571_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_575_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_576_ = l_Std_Http_Header_Name_referer;
v___x_577_ = l_Std_Http_Header_Name_cookie;
v___x_578_ = l_Std_Http_Header_Name_authorization;
v___x_579_ = lean_unsigned_to_nat(3u);
v___x_580_ = lean_mk_empty_array_with_capacity(v___x_579_);
v___x_581_ = lean_array_push(v___x_580_, v___x_578_);
v___x_582_ = lean_array_push(v___x_581_, v___x_577_);
v___x_583_ = lean_array_push(v___x_582_, v___x_576_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_584_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_585_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_586_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_587_ = lean_unsigned_to_nat(2u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_array_push(v___x_588_, v___x_586_);
v___x_590_ = lean_array_push(v___x_589_, v___x_585_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_591_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_592_ = l_Std_Http_Header_Name_lastModified;
v___x_593_ = l_Std_Http_Header_Name_contentLocation;
v___x_594_ = l_Std_Http_Header_Name_contentLanguage;
v___x_595_ = l_Std_Http_Header_Name_contentEncoding;
v___x_596_ = l_Std_Http_Header_Name_contentLength;
v___x_597_ = l_Std_Http_Header_Name_contentType;
v___x_598_ = lean_unsigned_to_nat(6u);
v___x_599_ = lean_mk_empty_array_with_capacity(v___x_598_);
v___x_600_ = lean_array_push(v___x_599_, v___x_597_);
v___x_601_ = lean_array_push(v___x_600_, v___x_596_);
v___x_602_ = lean_array_push(v___x_601_, v___x_595_);
v___x_603_ = lean_array_push(v___x_602_, v___x_594_);
v___x_604_ = lean_array_push(v___x_603_, v___x_593_);
v___x_605_ = lean_array_push(v___x_604_, v___x_592_);
return v___x_605_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_606_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
v___x_610_ = lean_unsigned_to_nat(16u);
v___x_611_ = lean_mk_array(v___x_610_, v___x_609_);
return v___x_611_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2);
v___x_616_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0));
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg(){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___boxed(lean_object* v___dummy_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
return v_res_621_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0(void){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v_00_u03b2_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(lean_object* v_i_625_, lean_object* v_x_626_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_mk_empty_array_with_capacity(v___x_627_);
v___x_629_ = lean_array_push(v___x_628_, v_i_625_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v_val_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
v_val_631_ = lean_ctor_get(v_x_626_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_626_);
if (v_isSharedCheck_639_ == 0)
{
v___x_633_ = v_x_626_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_val_631_);
lean_dec(v_x_626_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_array_push(v_val_631_, v_i_625_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_635_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(lean_object* v_i_640_, lean_object* v_a_641_, lean_object* v_x_642_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_val_645_; lean_object* v___x_646_; 
v___x_643_ = lean_box(0);
v___x_644_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(v_i_640_, v___x_643_);
v_val_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_val_645_);
lean_dec(v___x_644_);
v___x_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_646_, 0, v_a_641_);
lean_ctor_set(v___x_646_, 1, v_val_645_);
lean_ctor_set(v___x_646_, 2, v_x_642_);
return v___x_646_;
}
else
{
lean_object* v_key_647_; lean_object* v_value_648_; lean_object* v_tail_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_664_; 
v_key_647_ = lean_ctor_get(v_x_642_, 0);
v_value_648_ = lean_ctor_get(v_x_642_, 1);
v_tail_649_ = lean_ctor_get(v_x_642_, 2);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_642_);
if (v_isSharedCheck_664_ == 0)
{
v___x_651_ = v_x_642_;
v_isShared_652_ = v_isSharedCheck_664_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_tail_649_);
lean_inc(v_value_648_);
lean_inc(v_key_647_);
lean_dec(v_x_642_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_664_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
uint8_t v___x_653_; 
v___x_653_ = lean_string_dec_eq(v_key_647_, v_a_641_);
if (v___x_653_ == 0)
{
lean_object* v_tail_654_; lean_object* v___x_656_; 
v_tail_654_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(v_i_640_, v_a_641_, v_tail_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 2, v_tail_654_);
v___x_656_ = v___x_651_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_key_647_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_value_648_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_tail_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_val_660_; lean_object* v___x_662_; 
lean_dec(v_key_647_);
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v_value_648_);
v___x_659_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(v_i_640_, v___x_658_);
v_val_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_val_660_);
lean_dec(v___x_659_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v_val_660_);
lean_ctor_set(v___x_651_, 0, v_a_641_);
v___x_662_ = v___x_651_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_641_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_val_660_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_tail_649_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
return v_x_665_;
}
else
{
lean_object* v_key_667_; lean_object* v_value_668_; lean_object* v_tail_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_692_; 
v_key_667_ = lean_ctor_get(v_x_666_, 0);
v_value_668_ = lean_ctor_get(v_x_666_, 1);
v_tail_669_ = lean_ctor_get(v_x_666_, 2);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_666_);
if (v_isSharedCheck_692_ == 0)
{
v___x_671_ = v_x_666_;
v_isShared_672_ = v_isSharedCheck_692_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_tail_669_);
lean_inc(v_value_668_);
lean_inc(v_key_667_);
lean_dec(v_x_666_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_692_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; uint64_t v___x_674_; uint64_t v___x_675_; uint64_t v___x_676_; uint64_t v_fold_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v___x_680_; size_t v___x_681_; size_t v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_673_ = lean_array_get_size(v_x_665_);
v___x_674_ = lean_string_hash(v_key_667_);
v___x_675_ = 32ULL;
v___x_676_ = lean_uint64_shift_right(v___x_674_, v___x_675_);
v_fold_677_ = lean_uint64_xor(v___x_674_, v___x_676_);
v___x_678_ = 16ULL;
v___x_679_ = lean_uint64_shift_right(v_fold_677_, v___x_678_);
v___x_680_ = lean_uint64_xor(v_fold_677_, v___x_679_);
v___x_681_ = lean_uint64_to_usize(v___x_680_);
v___x_682_ = lean_usize_of_nat(v___x_673_);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_sub(v___x_682_, v___x_683_);
v___x_685_ = lean_usize_land(v___x_681_, v___x_684_);
v___x_686_ = lean_array_uget_borrowed(v_x_665_, v___x_685_);
lean_inc(v___x_686_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 2, v___x_686_);
v___x_688_ = v___x_671_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_key_667_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_value_668_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v___x_686_);
v___x_688_ = v_reuseFailAlloc_691_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; 
v___x_689_ = lean_array_uset(v_x_665_, v___x_685_, v___x_688_);
v_x_665_ = v___x_689_;
v_x_666_ = v_tail_669_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(lean_object* v_i_693_, lean_object* v_source_694_, lean_object* v_target_695_){
_start:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_array_get_size(v_source_694_);
v___x_697_ = lean_nat_dec_lt(v_i_693_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec_ref(v_source_694_);
lean_dec(v_i_693_);
return v_target_695_;
}
else
{
lean_object* v_es_698_; lean_object* v___x_699_; lean_object* v_source_700_; lean_object* v_target_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_es_698_ = lean_array_fget(v_source_694_, v_i_693_);
v___x_699_ = lean_box(0);
v_source_700_ = lean_array_fset(v_source_694_, v_i_693_, v___x_699_);
v_target_701_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(v_target_695_, v_es_698_);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_add(v_i_693_, v___x_702_);
lean_dec(v_i_693_);
v_i_693_ = v___x_703_;
v_source_694_ = v_source_700_;
v_target_695_ = v_target_701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(lean_object* v_data_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_nbuckets_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_706_ = lean_array_get_size(v_data_705_);
v___x_707_ = lean_unsigned_to_nat(2u);
v_nbuckets_708_ = lean_nat_mul(v___x_706_, v___x_707_);
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_box(0);
v___x_711_ = lean_mk_array(v_nbuckets_708_, v___x_710_);
v___x_712_ = lean_array_propagate_mark(v_data_705_, v___x_711_);
v___x_713_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(v___x_709_, v_data_705_, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v_i_714_, lean_object* v_m_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_size_717_; lean_object* v_buckets_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_768_; 
v_size_717_ = lean_ctor_get(v_m_715_, 0);
v_buckets_718_ = lean_ctor_get(v_m_715_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_m_715_);
if (v_isSharedCheck_768_ == 0)
{
v___x_720_ = v_m_715_;
v_isShared_721_ = v_isSharedCheck_768_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_buckets_718_);
lean_inc(v_size_717_);
lean_dec(v_m_715_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_768_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; uint64_t v___x_723_; uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v_fold_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; size_t v___x_734_; lean_object* v_bkt_735_; uint8_t v___x_736_; 
v___x_722_ = lean_array_get_size(v_buckets_718_);
v___x_723_ = lean_string_hash(v_a_716_);
v___x_724_ = 32ULL;
v___x_725_ = lean_uint64_shift_right(v___x_723_, v___x_724_);
v_fold_726_ = lean_uint64_xor(v___x_723_, v___x_725_);
v___x_727_ = 16ULL;
v___x_728_ = lean_uint64_shift_right(v_fold_726_, v___x_727_);
v___x_729_ = lean_uint64_xor(v_fold_726_, v___x_728_);
v___x_730_ = lean_uint64_to_usize(v___x_729_);
v___x_731_ = lean_usize_of_nat(v___x_722_);
v___x_732_ = ((size_t)1ULL);
v___x_733_ = lean_usize_sub(v___x_731_, v___x_732_);
v___x_734_ = lean_usize_land(v___x_730_, v___x_733_);
v_bkt_735_ = lean_array_uget_borrowed(v_buckets_718_, v___x_734_);
v___x_736_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_716_, v_bkt_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_size_x27_740_; lean_object* v___x_741_; lean_object* v_buckets_x27_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_mk_empty_array_with_capacity(v___x_737_);
v___x_739_ = lean_array_push(v___x_738_, v_i_714_);
v_size_x27_740_ = lean_nat_add(v_size_717_, v___x_737_);
lean_dec(v_size_717_);
lean_inc(v_bkt_735_);
v___x_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_741_, 0, v_a_716_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
lean_ctor_set(v___x_741_, 2, v_bkt_735_);
v_buckets_x27_742_ = lean_array_uset(v_buckets_718_, v___x_734_, v___x_741_);
v___x_743_ = lean_unsigned_to_nat(4u);
v___x_744_ = lean_nat_mul(v_size_x27_740_, v___x_743_);
v___x_745_ = lean_unsigned_to_nat(3u);
v___x_746_ = lean_nat_div(v___x_744_, v___x_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_array_get_size(v_buckets_x27_742_);
v___x_748_ = lean_nat_dec_le(v___x_746_, v___x_747_);
lean_dec(v___x_746_);
if (v___x_748_ == 0)
{
lean_object* v_val_749_; lean_object* v___x_751_; 
v_val_749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(v_buckets_x27_742_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_val_749_);
lean_ctor_set(v___x_720_, 0, v_size_x27_740_);
v___x_751_ = v___x_720_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_size_x27_740_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_val_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_object* v___x_754_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_buckets_x27_742_);
lean_ctor_set(v___x_720_, 0, v_size_x27_740_);
v___x_754_ = v___x_720_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_size_x27_740_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_buckets_x27_742_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
else
{
lean_object* v___x_756_; lean_object* v_buckets_x27_757_; lean_object* v_bkt_x27_758_; lean_object* v___y_760_; uint8_t v___x_765_; 
lean_inc(v_bkt_735_);
v___x_756_ = lean_box(0);
v_buckets_x27_757_ = lean_array_uset(v_buckets_718_, v___x_734_, v___x_756_);
lean_inc_ref(v_a_716_);
v_bkt_x27_758_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(v_i_714_, v_a_716_, v_bkt_735_);
v___x_765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_716_, v_bkt_x27_758_);
lean_dec_ref(v_a_716_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_sub(v_size_717_, v___x_766_);
lean_dec(v_size_717_);
v___y_760_ = v___x_767_;
goto v___jp_759_;
}
else
{
v___y_760_ = v_size_717_;
goto v___jp_759_;
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_array_uset(v_buckets_x27_757_, v___x_734_, v_bkt_x27_758_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_761_);
lean_ctor_set(v___x_720_, 0, v___y_760_);
v___x_763_ = v___x_720_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___y_760_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_a_769_, lean_object* v_as_770_, size_t v_i_771_, size_t v_stop_772_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = lean_usize_dec_eq(v_i_771_, v_stop_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_uget_borrowed(v_as_770_, v_i_771_);
v___x_775_ = lean_string_dec_eq(v_a_769_, v___x_774_);
if (v___x_775_ == 0)
{
size_t v___x_776_; size_t v___x_777_; 
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_771_, v___x_776_);
v_i_771_ = v___x_777_;
goto _start;
}
else
{
return v___x_775_;
}
}
else
{
uint8_t v___x_779_; 
v___x_779_ = 0;
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_a_780_, lean_object* v_as_781_, lean_object* v_i_782_, lean_object* v_stop_783_){
_start:
{
size_t v_i_boxed_784_; size_t v_stop_boxed_785_; uint8_t v_res_786_; lean_object* v_r_787_; 
v_i_boxed_784_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_stop_boxed_785_ = lean_unbox_usize(v_stop_783_);
lean_dec(v_stop_783_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_780_, v_as_781_, v_i_boxed_784_, v_stop_boxed_785_);
lean_dec_ref(v_as_781_);
lean_dec_ref(v_a_780_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_as_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_array_get_size(v_as_788_);
v___x_792_ = lean_nat_dec_lt(v___x_790_, v___x_791_);
if (v___x_792_ == 0)
{
return v___x_792_;
}
else
{
size_t v___x_793_; size_t v___x_794_; uint8_t v___x_795_; 
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_of_nat(v___x_791_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_789_, v_as_788_, v___x_793_, v___x_794_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object* v_as_796_, lean_object* v_a_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_as_796_, v_a_797_);
lean_dec_ref(v_a_797_);
lean_dec_ref(v_as_796_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object* v___y_800_, lean_object* v_as_801_, size_t v_i_802_, size_t v_stop_803_, lean_object* v_b_804_){
_start:
{
lean_object* v___y_806_; uint8_t v___x_810_; 
v___x_810_ = lean_usize_dec_eq(v_i_802_, v_stop_803_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v_fst_812_; uint8_t v___x_813_; 
v___x_811_ = lean_array_uget_borrowed(v_as_801_, v_i_802_);
v_fst_812_ = lean_ctor_get(v___x_811_, 0);
v___x_813_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_800_, v_fst_812_);
if (v___x_813_ == 0)
{
lean_object* v_entries_814_; lean_object* v_indexes_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_825_; 
v_entries_814_ = lean_ctor_get(v_b_804_, 0);
v_indexes_815_ = lean_ctor_get(v_b_804_, 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v_b_804_);
if (v_isSharedCheck_825_ == 0)
{
v___x_817_ = v_b_804_;
v_isShared_818_ = v_isSharedCheck_825_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_indexes_815_);
lean_inc(v_entries_814_);
lean_dec(v_b_804_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_825_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_i_819_; lean_object* v_entries_820_; lean_object* v_indexes_821_; lean_object* v___x_823_; 
v_i_819_ = lean_array_get_size(v_entries_814_);
lean_inc(v___x_811_);
v_entries_820_ = lean_array_push(v_entries_814_, v___x_811_);
lean_inc(v_fst_812_);
v_indexes_821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v_i_819_, v_indexes_815_, v_fst_812_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v_indexes_821_);
lean_ctor_set(v___x_817_, 0, v_entries_820_);
v___x_823_ = v___x_817_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_entries_820_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_indexes_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
v___y_806_ = v___x_823_;
goto v___jp_805_;
}
}
}
else
{
v___y_806_ = v_b_804_;
goto v___jp_805_;
}
}
else
{
return v_b_804_;
}
v___jp_805_:
{
size_t v___x_807_; size_t v___x_808_; 
v___x_807_ = ((size_t)1ULL);
v___x_808_ = lean_usize_add(v_i_802_, v___x_807_);
v_i_802_ = v___x_808_;
v_b_804_ = v___y_806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object* v___y_826_, lean_object* v_as_827_, lean_object* v_i_828_, lean_object* v_stop_829_, lean_object* v_b_830_){
_start:
{
size_t v_i_boxed_831_; size_t v_stop_boxed_832_; lean_object* v_res_833_; 
v_i_boxed_831_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_stop_boxed_832_ = lean_unbox_usize(v_stop_829_);
lean_dec(v_stop_829_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_826_, v_as_827_, v_i_boxed_831_, v_stop_boxed_832_, v_b_830_);
lean_dec_ref(v_as_827_);
lean_dec_ref(v___y_826_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_834_, uint8_t v_isCrossOrigin_835_, uint8_t v_methodChanged_836_){
_start:
{
lean_object* v___y_838_; lean_object* v___y_848_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_afterConnection_855_; 
v___x_853_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_854_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_834_);
v_afterConnection_855_ = l_Array_append___redArg(v___x_853_, v___x_854_);
lean_dec_ref(v___x_854_);
if (v_isCrossOrigin_835_ == 0)
{
v___y_848_ = v_afterConnection_855_;
goto v___jp_847_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_856_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_857_ = l_Array_append___redArg(v_afterConnection_855_, v___x_856_);
v___x_858_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_859_ = l_Array_append___redArg(v___x_857_, v___x_858_);
v___x_860_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_861_ = l_Array_append___redArg(v___x_859_, v___x_860_);
v___y_848_ = v___x_861_;
goto v___jp_847_;
}
v___jp_837_:
{
lean_object* v_entries_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_entries_839_ = lean_ctor_get(v_headers_834_, 0);
v___x_840_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = lean_array_get_size(v_entries_839_);
v___x_843_ = lean_nat_dec_lt(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_dec_ref(v___y_838_);
return v___x_840_;
}
else
{
size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((size_t)0ULL);
v___x_845_ = lean_usize_of_nat(v___x_842_);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_838_, v_entries_839_, v___x_844_, v___x_845_, v___x_840_);
lean_dec_ref(v___y_838_);
return v___x_846_;
}
}
v___jp_847_:
{
if (v_methodChanged_836_ == 0)
{
v___y_838_ = v___y_848_;
goto v___jp_837_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_849_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_850_ = l_Array_append___redArg(v___y_848_, v___x_849_);
v___x_851_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_852_ = l_Array_append___redArg(v___x_850_, v___x_851_);
v___y_838_ = v___x_852_;
goto v___jp_837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_862_, lean_object* v_isCrossOrigin_863_, lean_object* v_methodChanged_864_){
_start:
{
uint8_t v_isCrossOrigin_boxed_865_; uint8_t v_methodChanged_boxed_866_; lean_object* v_res_867_; 
v_isCrossOrigin_boxed_865_ = lean_unbox(v_isCrossOrigin_863_);
v_methodChanged_boxed_866_ = lean_unbox(v_methodChanged_864_);
v_res_867_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_862_, v_isCrossOrigin_boxed_865_, v_methodChanged_boxed_866_);
lean_dec_ref(v_headers_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(lean_object* v_00_u03b2_868_, lean_object* v_data_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(v_data_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_871_, lean_object* v_i_872_, lean_object* v_source_873_, lean_object* v_target_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(v_i_872_, v_source_873_, v_target_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(v_x_877_, v_x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_880_, lean_object* v_origin_881_){
_start:
{
lean_object* v_entries_882_; lean_object* v_indexes_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_entries_882_ = lean_ctor_get(v_headers_880_, 0);
v_indexes_883_ = lean_ctor_get(v_headers_880_, 1);
v___x_884_ = l_Std_Http_Header_Name_host;
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_dec_ref(v_origin_881_);
return v_headers_880_;
}
else
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_901_; 
lean_inc_ref(v_indexes_883_);
lean_inc_ref(v_entries_882_);
v_isSharedCheck_901_ = !lean_is_exclusive(v_headers_880_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; lean_object* v_unused_903_; 
v_unused_902_ = lean_ctor_get(v_headers_880_, 1);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_headers_880_, 0);
lean_dec(v_unused_903_);
v___x_887_ = v_headers_880_;
v_isShared_888_ = v_isSharedCheck_901_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_headers_880_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_901_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_idxs_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_lastIdx_895_; lean_object* v___x_896_; lean_object* v_entries_897_; lean_object* v___x_899_; 
v___x_889_ = l_Std_Http_URI_Origin_hostHeader(v_origin_881_);
v___x_890_ = l_Std_Http_Header_Value_ofString_x21(v___x_889_);
v_idxs_891_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_883_, v___x_884_);
v___x_892_ = lean_array_get_size(v_idxs_891_);
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_sub(v___x_892_, v___x_893_);
v_lastIdx_895_ = lean_array_fget(v_idxs_891_, v___x_894_);
lean_dec(v___x_894_);
lean_dec(v_idxs_891_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_884_);
lean_ctor_set(v___x_896_, 1, v___x_890_);
v_entries_897_ = lean_array_fset(v_entries_882_, v_lastIdx_895_, v___x_896_);
lean_dec(v_lastIdx_895_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_entries_897_);
v___x_899_ = v___x_887_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_entries_897_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_indexes_883_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_904_){
_start:
{
switch(lean_obj_tag(v_x_904_))
{
case 0:
{
lean_object* v_query_905_; 
v_query_905_ = lean_ctor_get(v_x_904_, 1);
lean_inc(v_query_905_);
return v_query_905_;
}
case 1:
{
lean_object* v_uri_906_; lean_object* v_query_907_; 
v_uri_906_ = lean_ctor_get(v_x_904_, 0);
v_query_907_ = lean_ctor_get(v_uri_906_, 3);
lean_inc(v_query_907_);
return v_query_907_;
}
default: 
{
lean_object* v___x_908_; 
v___x_908_ = lean_box(0);
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_909_);
lean_dec(v_x_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_911_, uint8_t v_isCrossOrigin_912_, lean_object* v_basePath_913_, lean_object* v_baseQuery_914_, lean_object* v_currentScheme_915_){
_start:
{
lean_object* v___y_917_; lean_object* v___y_918_; 
if (lean_obj_tag(v_ref_911_) == 0)
{
lean_object* v_uri_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_currentScheme_915_);
lean_dec(v_baseQuery_914_);
lean_dec_ref(v_basePath_913_);
v_uri_921_ = lean_ctor_get(v_ref_911_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_ref_911_);
if (v_isSharedCheck_963_ == 0)
{
v___x_923_ = v_ref_911_;
v_isShared_924_ = v_isSharedCheck_963_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_uri_921_);
lean_dec(v_ref_911_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_963_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_scheme_925_; lean_object* v_authority_926_; lean_object* v_path_927_; lean_object* v_query_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_961_; 
v_scheme_925_ = lean_ctor_get(v_uri_921_, 0);
v_authority_926_ = lean_ctor_get(v_uri_921_, 1);
v_path_927_ = lean_ctor_get(v_uri_921_, 2);
v_query_928_ = lean_ctor_get(v_uri_921_, 3);
v_isSharedCheck_961_ = !lean_is_exclusive(v_uri_921_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v_uri_921_, 4);
lean_dec(v_unused_962_);
v___x_930_ = v_uri_921_;
v_isShared_931_ = v_isSharedCheck_961_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_query_928_);
lean_inc(v_path_927_);
lean_inc(v_authority_926_);
lean_inc(v_scheme_925_);
lean_dec(v_uri_921_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_961_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___y_933_; 
if (lean_obj_tag(v_authority_926_) == 0)
{
v___y_933_ = v_authority_926_;
goto v___jp_932_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_960_; 
v_val_942_ = lean_ctor_get(v_authority_926_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_authority_926_);
if (v_isSharedCheck_960_ == 0)
{
v___x_944_ = v_authority_926_;
v_isShared_945_ = v_isSharedCheck_960_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_authority_926_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_960_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_host_946_; lean_object* v_port_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_958_; 
v_host_946_ = lean_ctor_get(v_val_942_, 1);
v_port_947_ = lean_ctor_get(v_val_942_, 2);
v_isSharedCheck_958_ = !lean_is_exclusive(v_val_942_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v_val_942_, 0);
lean_dec(v_unused_959_);
v___x_949_ = v_val_942_;
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_port_947_);
lean_inc(v_host_946_);
lean_dec(v_val_942_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_box(0);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_host_946_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_port_947_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_953_);
v___x_955_ = v___x_944_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v___y_933_ = v___x_955_;
goto v___jp_932_;
}
}
}
}
}
v___jp_932_:
{
if (v_isCrossOrigin_912_ == 0)
{
lean_object* v___x_934_; 
lean_dec(v___y_933_);
lean_del_object(v___x_930_);
lean_dec_ref(v_scheme_925_);
lean_del_object(v___x_923_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_path_927_);
lean_ctor_set(v___x_934_, 1, v_query_928_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v_stripped_937_; 
v___x_935_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v___x_935_);
lean_ctor_set(v___x_930_, 1, v___y_933_);
v_stripped_937_ = v___x_930_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_scheme_925_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v___y_933_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_path_927_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_query_928_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v___x_935_);
v_stripped_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 1);
lean_ctor_set(v___x_923_, 0, v_stripped_937_);
v___x_939_ = v___x_923_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_stripped_937_);
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
}
}
}
else
{
lean_object* v_ref_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1006_; 
v_ref_964_ = lean_ctor_get(v_ref_911_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_ref_911_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_966_ = v_ref_911_;
v_isShared_967_ = v_isSharedCheck_1006_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_ref_964_);
lean_dec(v_ref_911_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1006_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_authority_968_; 
v_authority_968_ = lean_ctor_get(v_ref_964_, 0);
lean_inc(v_authority_968_);
if (lean_obj_tag(v_authority_968_) == 0)
{
lean_object* v_path_969_; lean_object* v_query_970_; uint8_t v___x_971_; lean_object* v___y_973_; 
lean_del_object(v___x_966_);
lean_dec_ref(v_currentScheme_915_);
v_path_969_ = lean_ctor_get(v_ref_964_, 1);
lean_inc_ref(v_path_969_);
v_query_970_ = lean_ctor_get(v_ref_964_, 2);
lean_inc(v_query_970_);
lean_dec_ref(v_ref_964_);
v___x_971_ = l_Std_Http_URI_Path_isEmpty(v_path_969_);
if (v___x_971_ == 0)
{
uint8_t v_absolute_974_; 
v_absolute_974_ = lean_ctor_get_uint8(v_path_969_, sizeof(void*)*1);
if (v_absolute_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = l_Std_Http_URI_Path_parent(v_basePath_913_);
v___x_976_ = l_Std_Http_URI_Path_join(v___x_975_, v_path_969_);
lean_dec_ref(v_path_969_);
v___y_973_ = v___x_976_;
goto v___jp_972_;
}
else
{
lean_dec_ref(v_basePath_913_);
v___y_973_ = v_path_969_;
goto v___jp_972_;
}
}
else
{
lean_dec_ref(v_path_969_);
v___y_973_ = v_basePath_913_;
goto v___jp_972_;
}
v___jp_972_:
{
if (v___x_971_ == 0)
{
lean_dec(v_baseQuery_914_);
v___y_917_ = v___y_973_;
v___y_918_ = v_query_970_;
goto v___jp_916_;
}
else
{
if (lean_obj_tag(v_query_970_) == 0)
{
v___y_917_ = v___y_973_;
v___y_918_ = v_baseQuery_914_;
goto v___jp_916_;
}
else
{
lean_dec(v_baseQuery_914_);
v___y_917_ = v___y_973_;
v___y_918_ = v_query_970_;
goto v___jp_916_;
}
}
}
}
else
{
lean_dec(v_baseQuery_914_);
lean_dec_ref(v_basePath_913_);
if (v_isCrossOrigin_912_ == 0)
{
lean_object* v_path_977_; lean_object* v_query_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref_known(v_authority_968_, 1);
lean_del_object(v___x_966_);
lean_dec_ref(v_currentScheme_915_);
v_path_977_ = lean_ctor_get(v_ref_964_, 1);
lean_inc_ref(v_path_977_);
v_query_978_ = lean_ctor_get(v_ref_964_, 2);
lean_inc(v_query_978_);
lean_dec_ref(v_ref_964_);
v___x_979_ = l_Std_Http_URI_Path_normalize(v_path_977_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v_query_978_);
return v___x_980_;
}
else
{
lean_object* v_val_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1005_; 
v_val_981_ = lean_ctor_get(v_authority_968_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_authority_968_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_983_ = v_authority_968_;
v_isShared_984_ = v_isSharedCheck_1005_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_val_981_);
lean_dec(v_authority_968_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1005_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_path_985_; lean_object* v_query_986_; lean_object* v_host_987_; lean_object* v_port_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1003_; 
v_path_985_ = lean_ctor_get(v_ref_964_, 1);
lean_inc_ref(v_path_985_);
v_query_986_ = lean_ctor_get(v_ref_964_, 2);
lean_inc(v_query_986_);
lean_dec_ref(v_ref_964_);
v_host_987_ = lean_ctor_get(v_val_981_, 1);
v_port_988_ = lean_ctor_get(v_val_981_, 2);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_val_981_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_val_981_, 0);
lean_dec(v_unused_1004_);
v___x_990_ = v_val_981_;
v_isShared_991_ = v_isSharedCheck_1003_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_port_988_);
lean_inc(v_host_987_);
lean_dec(v_val_981_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1003_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v_stripped_994_; 
v___x_992_ = lean_box(0);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_992_);
v_stripped_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_host_987_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_port_988_);
v_stripped_994_ = v_reuseFailAlloc_1002_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v_stripped_994_);
v___x_996_ = v___x_983_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_stripped_994_);
v___x_996_ = v_reuseFailAlloc_1001_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v_af_997_; lean_object* v___x_999_; 
v_af_997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_997_, 0, v_currentScheme_915_);
lean_ctor_set(v_af_997_, 1, v___x_996_);
lean_ctor_set(v_af_997_, 2, v_path_985_);
lean_ctor_set(v_af_997_, 3, v_query_986_);
lean_ctor_set(v_af_997_, 4, v___x_992_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v_af_997_);
v___x_999_ = v___x_966_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_af_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
}
}
}
v___jp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = l_Std_Http_URI_Path_normalize(v___y_917_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___y_918_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_1007_, lean_object* v_isCrossOrigin_1008_, lean_object* v_basePath_1009_, lean_object* v_baseQuery_1010_, lean_object* v_currentScheme_1011_){
_start:
{
uint8_t v_isCrossOrigin_boxed_1012_; lean_object* v_res_1013_; 
v_isCrossOrigin_boxed_1012_ = lean_unbox(v_isCrossOrigin_1008_);
v_res_1013_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_1007_, v_isCrossOrigin_boxed_1012_, v_basePath_1009_, v_baseQuery_1010_, v_currentScheme_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Std_Http_URI_Parser_parseURIReference(v___x_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_pos_1020_; lean_object* v_array_1021_; lean_object* v_idx_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_pos_1020_ = lean_ctor_get(v___x_1019_, 0);
v_array_1021_ = lean_ctor_get(v_pos_1020_, 0);
v_idx_1022_ = lean_ctor_get(v_pos_1020_, 1);
v___x_1023_ = lean_byte_array_size(v_array_1021_);
v___x_1024_ = lean_nat_dec_lt(v_idx_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
return v___x_1019_;
}
else
{
lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1032_; 
lean_inc(v_pos_1020_);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; lean_object* v_unused_1034_; 
v_unused_1033_ = lean_ctor_get(v___x_1019_, 1);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v___x_1019_, 0);
lean_dec(v_unused_1034_);
v___x_1026_ = v___x_1019_;
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
else
{
lean_dec(v___x_1019_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 1);
lean_ctor_set(v___x_1026_, 1, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_pos_1020_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_1047_, lean_object* v_request_1048_, uint8_t v_bodyReplayable_1049_, uint8_t v_onlySafeRedirects_1050_, uint8_t v_responseVersion_1051_, lean_object* v_status_1052_, lean_object* v_responseHeaders_1053_){
_start:
{
lean_object* v___y_1055_; uint8_t v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; uint8_t v___y_1060_; uint8_t v___y_1061_; lean_object* v___y_1069_; lean_object* v___y_1070_; uint8_t v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; uint8_t v___y_1074_; lean_object* v___y_1077_; uint8_t v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; uint8_t v___y_1083_; uint8_t v___y_1084_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1092_; uint8_t v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; uint8_t v___y_1097_; uint8_t v___y_1098_; lean_object* v___y_1102_; uint8_t v___y_1103_; uint8_t v___y_1104_; lean_object* v___y_1105_; uint8_t v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; uint8_t v___y_1110_; lean_object* v___y_1114_; uint8_t v___y_1115_; uint8_t v___y_1116_; lean_object* v___y_1117_; uint8_t v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; uint8_t v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1125_; uint8_t v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1128_; uint8_t v___y_1129_; lean_object* v___y_1130_; uint8_t v___y_1131_; uint8_t v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1135_; uint8_t v___y_1136_; uint8_t v___y_1137_; uint8_t v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___y_1142_; uint8_t v___y_1143_; lean_object* v___y_1147_; uint8_t v___y_1148_; uint8_t v___y_1149_; lean_object* v___y_1150_; uint8_t v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; uint8_t v___y_1154_; uint8_t v___y_1155_; uint8_t v___y_1156_; lean_object* v___y_1160_; uint8_t v___y_1161_; uint8_t v___y_1162_; uint8_t v___y_1163_; uint8_t v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1168_; uint8_t v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1172_; uint8_t v___y_1173_; uint8_t v___y_1174_; lean_object* v___y_1175_; uint8_t v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; uint8_t v___y_1179_; uint8_t v___y_1180_; lean_object* v___y_1184_; uint8_t v___y_1185_; uint8_t v___y_1186_; uint8_t v___y_1187_; uint8_t v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; uint8_t v___y_1192_; uint8_t v___y_1193_; uint8_t v___y_1195_; lean_object* v___y_1196_; uint8_t v___y_1197_; uint8_t v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; uint8_t v___y_1203_; uint8_t v___y_1204_; uint8_t v___y_1205_; uint16_t v___x_1208_; uint16_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = 300;
v___x_1209_ = l_Std_Http_Status_toCode(v_status_1052_);
v___x_1210_ = lean_uint16_dec_le(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec_ref(v_current_1047_);
v___x_1211_ = lean_box(0);
return v___x_1211_;
}
else
{
uint16_t v___x_1212_; uint8_t v___x_1213_; uint8_t v___y_1215_; lean_object* v___y_1216_; uint8_t v___y_1217_; uint8_t v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; uint8_t v___y_1223_; uint8_t v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1232_; uint8_t v___y_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; uint8_t v___y_1237_; uint8_t v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; uint8_t v___y_1246_; uint8_t v___y_1247_; uint8_t v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; uint8_t v___y_1253_; uint8_t v___y_1254_; uint8_t v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v_scheme_1258_; 
v___x_1212_ = 400;
v___x_1213_ = lean_uint16_dec_lt(v___x_1209_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref(v_current_1047_);
v___x_1263_ = lean_box(0);
return v___x_1263_;
}
else
{
uint8_t v___x_1264_; uint8_t v___y_1266_; uint8_t v___x_1308_; uint8_t v___x_1309_; 
v___x_1264_ = 0;
v___x_1308_ = 0;
v___x_1309_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_1051_, v___x_1308_);
if (v___x_1309_ == 0)
{
goto v___jp_1292_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = lean_box(15);
v___x_1311_ = l_Std_Http_instBEqStatus_beq(v_status_1052_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_box(16);
v___x_1313_ = l_Std_Http_instBEqStatus_beq(v_status_1052_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v_current_1047_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
else
{
goto v___jp_1292_;
}
}
else
{
goto v___jp_1292_;
}
}
v___jp_1265_:
{
lean_object* v_entries_1267_; lean_object* v_indexes_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_entries_1267_ = lean_ctor_get(v_responseHeaders_1053_, 0);
v_indexes_1268_ = lean_ctor_get(v_responseHeaders_1053_, 1);
v___x_1269_ = l_Std_Http_Header_Name_location;
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_dec_ref(v_current_1047_);
v___x_1271_ = lean_box(0);
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_entry_1274_; lean_object* v___x_1275_; lean_object* v_snd_1276_; lean_object* v___f_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_1268_, v___x_1269_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v_entry_1274_ = lean_array_fget(v___x_1272_, v___x_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_array_fget_borrowed(v_entries_1267_, v_entry_1274_);
lean_dec(v_entry_1274_);
v_snd_1276_ = lean_ctor_get(v___x_1275_, 1);
v___f_1277_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
lean_inc(v_snd_1276_);
v___x_1278_ = lean_string_to_utf8(v_snd_1276_);
v___x_1279_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1277_, v___x_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref_known(v___x_1279_, 1);
lean_dec_ref(v_current_1047_);
v___x_1280_ = lean_box(0);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1282_; 
v_a_1281_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_n(v_a_1281_, 2);
lean_dec_ref_known(v___x_1279_, 1);
lean_inc_ref(v_current_1047_);
v___x_1282_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_1047_, v_a_1281_);
if (lean_obj_tag(v___x_1282_) == 1)
{
lean_object* v_val_1283_; uint8_t v_method_1284_; lean_object* v_uri_1285_; lean_object* v_headers_1286_; lean_object* v_scheme_1287_; uint8_t v_newMethod_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v_method_1284_ = lean_ctor_get_uint8(v_request_1048_, sizeof(void*)*2);
v_uri_1285_ = lean_ctor_get(v_request_1048_, 0);
v_headers_1286_ = lean_ctor_get(v_request_1048_, 1);
v_scheme_1287_ = lean_ctor_get(v_val_1283_, 0);
v_newMethod_1288_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_1284_, v_responseVersion_1051_, v_status_1052_);
v___x_1289_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_1290_ = lean_string_dec_eq(v_scheme_1287_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_inc_ref(v_scheme_1287_);
v___y_1250_ = v_method_1284_;
v___y_1251_ = v_uri_1285_;
v___y_1252_ = v_a_1281_;
v___y_1253_ = v_newMethod_1288_;
v___y_1254_ = v___y_1266_;
v___y_1255_ = v___x_1270_;
v___y_1256_ = v_headers_1286_;
v___y_1257_ = v_val_1283_;
v_scheme_1258_ = v_scheme_1287_;
goto v___jp_1249_;
}
else
{
if (v___y_1266_ == 0)
{
v___y_1240_ = v_method_1284_;
v___y_1241_ = v_uri_1285_;
v___y_1242_ = v_newMethod_1288_;
v___y_1243_ = v_a_1281_;
v___y_1244_ = v_headers_1286_;
v___y_1245_ = v_val_1283_;
v___y_1246_ = v___x_1270_;
v___y_1247_ = v___x_1264_;
goto v___jp_1239_;
}
else
{
lean_inc_ref(v_scheme_1287_);
v___y_1250_ = v_method_1284_;
v___y_1251_ = v_uri_1285_;
v___y_1252_ = v_a_1281_;
v___y_1253_ = v_newMethod_1288_;
v___y_1254_ = v___y_1266_;
v___y_1255_ = v___x_1270_;
v___y_1256_ = v_headers_1286_;
v___y_1257_ = v_val_1283_;
v_scheme_1258_ = v_scheme_1287_;
goto v___jp_1249_;
}
}
}
else
{
lean_object* v___x_1291_; 
lean_dec(v___x_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_current_1047_);
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
}
}
}
v___jp_1292_:
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = lean_box(19);
v___x_1294_ = l_Std_Http_instBEqStatus_beq(v_status_1052_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = lean_box(20);
v___x_1296_ = l_Std_Http_instBEqStatus_beq(v_status_1052_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = lean_box(18);
v___x_1298_ = l_Std_Http_instBEqStatus_beq(v_status_1052_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_box(14);
v___x_1300_ = l_Std_Http_instBEqStatus_beq(v_status_1052_, v___x_1299_);
if (v___x_1300_ == 0)
{
if (v_onlySafeRedirects_1050_ == 0)
{
v___y_1266_ = v___x_1264_;
goto v___jp_1265_;
}
else
{
uint8_t v_method_1301_; uint8_t v___x_1302_; 
v_method_1301_ = lean_ctor_get_uint8(v_request_1048_, sizeof(void*)*2);
v___x_1302_ = l_Std_Http_Method_isSafe(v_method_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec_ref(v_current_1047_);
v___x_1303_ = lean_box(0);
return v___x_1303_;
}
else
{
v___y_1266_ = v___x_1300_;
goto v___jp_1265_;
}
}
}
else
{
lean_object* v___x_1304_; 
lean_dec_ref(v_current_1047_);
v___x_1304_ = lean_box(0);
return v___x_1304_;
}
}
else
{
lean_object* v___x_1305_; 
lean_dec_ref(v_current_1047_);
v___x_1305_ = lean_box(0);
return v___x_1305_;
}
}
else
{
lean_object* v___x_1306_; 
lean_dec_ref(v_current_1047_);
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
}
else
{
lean_object* v___x_1307_; 
lean_dec_ref(v_current_1047_);
v___x_1307_ = lean_box(0);
return v___x_1307_;
}
}
}
v___jp_1214_:
{
uint8_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = 8;
v___x_1225_ = l_Std_Http_instBEqMethod_beq(v___y_1215_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = 9;
v___x_1227_ = l_Std_Http_instBEqMethod_beq(v___y_1215_, v___x_1226_);
v___y_1195_ = v___y_1215_;
v___y_1196_ = v___y_1216_;
v___y_1197_ = v___x_1224_;
v___y_1198_ = v___y_1217_;
v___y_1199_ = v___y_1219_;
v___y_1200_ = v___y_1218_;
v___y_1201_ = v___y_1220_;
v___y_1202_ = v___y_1221_;
v___y_1203_ = v___y_1222_;
v___y_1204_ = v___y_1223_;
v___y_1205_ = v___x_1227_;
goto v___jp_1194_;
}
else
{
v___y_1195_ = v___y_1215_;
v___y_1196_ = v___y_1216_;
v___y_1197_ = v___x_1224_;
v___y_1198_ = v___y_1217_;
v___y_1199_ = v___y_1219_;
v___y_1200_ = v___y_1218_;
v___y_1201_ = v___y_1220_;
v___y_1202_ = v___y_1221_;
v___y_1203_ = v___y_1222_;
v___y_1204_ = v___y_1223_;
v___y_1205_ = v___x_1213_;
goto v___jp_1194_;
}
}
v___jp_1228_:
{
uint8_t v___x_1238_; 
v___x_1238_ = l_Std_Http_instBEqMethod_beq(v___y_1233_, v___y_1229_);
if (v___x_1238_ == 0)
{
v___y_1215_ = v___y_1229_;
v___y_1216_ = v___y_1230_;
v___y_1217_ = v___y_1231_;
v___y_1218_ = v___y_1233_;
v___y_1219_ = v___y_1232_;
v___y_1220_ = v___y_1236_;
v___y_1221_ = v___y_1235_;
v___y_1222_ = v___y_1237_;
v___y_1223_ = v___y_1234_;
goto v___jp_1214_;
}
else
{
v___y_1215_ = v___y_1229_;
v___y_1216_ = v___y_1230_;
v___y_1217_ = v___y_1231_;
v___y_1218_ = v___y_1233_;
v___y_1219_ = v___y_1232_;
v___y_1220_ = v___y_1236_;
v___y_1221_ = v___y_1235_;
v___y_1222_ = v___y_1237_;
v___y_1223_ = v___y_1231_;
goto v___jp_1214_;
}
}
v___jp_1239_:
{
uint8_t v___x_1248_; 
v___x_1248_ = l_Std_Http_URI_instBEqOrigin_beq(v___y_1245_, v_current_1047_);
if (v___x_1248_ == 0)
{
v___y_1229_ = v___y_1240_;
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1247_;
v___y_1232_ = v___y_1243_;
v___y_1233_ = v___y_1242_;
v___y_1234_ = v___y_1246_;
v___y_1235_ = v___y_1245_;
v___y_1236_ = v___y_1244_;
v___y_1237_ = v___y_1246_;
goto v___jp_1228_;
}
else
{
v___y_1229_ = v___y_1240_;
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1247_;
v___y_1232_ = v___y_1243_;
v___y_1233_ = v___y_1242_;
v___y_1234_ = v___y_1246_;
v___y_1235_ = v___y_1245_;
v___y_1236_ = v___y_1244_;
v___y_1237_ = v___y_1247_;
goto v___jp_1228_;
}
}
v___jp_1249_:
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__0));
v___x_1260_ = lean_string_dec_eq(v_scheme_1258_, v___x_1259_);
lean_dec_ref(v_scheme_1258_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_current_1047_);
v___x_1261_ = lean_box(0);
return v___x_1261_;
}
else
{
if (v___y_1254_ == 0)
{
v___y_1240_ = v___y_1250_;
v___y_1241_ = v___y_1251_;
v___y_1242_ = v___y_1253_;
v___y_1243_ = v___y_1252_;
v___y_1244_ = v___y_1256_;
v___y_1245_ = v___y_1257_;
v___y_1246_ = v___y_1255_;
v___y_1247_ = v___y_1254_;
goto v___jp_1239_;
}
else
{
lean_object* v___x_1262_; 
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_current_1047_);
v___x_1262_ = lean_box(0);
return v___x_1262_;
}
}
}
}
v___jp_1054_:
{
lean_object* v_scheme_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_rewrittenTarget_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_scheme_1062_ = lean_ctor_get(v_current_1047_, 0);
lean_inc_ref(v_scheme_1062_);
lean_dec_ref(v_current_1047_);
v___x_1063_ = l_Std_Http_RequestTarget_pathOrRoot(v___y_1055_);
v___x_1064_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v___y_1055_);
v_rewrittenTarget_1065_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v___y_1057_, v___y_1060_, v___x_1063_, v___x_1064_, v_scheme_1062_);
v___x_1066_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1066_, 0, v___y_1059_);
lean_ctor_set(v___x_1066_, 1, v_rewrittenTarget_1065_);
lean_ctor_set(v___x_1066_, 2, v___y_1058_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*3, v___y_1056_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*3 + 1, v___y_1061_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*3 + 2, v___y_1060_);
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
v___jp_1068_:
{
uint8_t v___x_1075_; 
v___x_1075_ = 0;
v___y_1055_ = v___y_1069_;
v___y_1056_ = v___y_1071_;
v___y_1057_ = v___y_1070_;
v___y_1058_ = v___y_1072_;
v___y_1059_ = v___y_1073_;
v___y_1060_ = v___y_1074_;
v___y_1061_ = v___x_1075_;
goto v___jp_1054_;
}
v___jp_1076_:
{
uint8_t v___x_1085_; 
v___x_1085_ = l_Std_Http_instBEqMethod_beq(v___y_1080_, v___y_1078_);
if (v___x_1085_ == 0)
{
uint8_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = 9;
v___x_1087_ = l_Std_Http_instBEqMethod_beq(v___y_1080_, v___x_1086_);
if (v___x_1087_ == 0)
{
if (v___y_1084_ == 0)
{
uint8_t v___x_1088_; 
v___x_1088_ = 1;
v___y_1055_ = v___y_1077_;
v___y_1056_ = v___y_1080_;
v___y_1057_ = v___y_1079_;
v___y_1058_ = v___y_1081_;
v___y_1059_ = v___y_1082_;
v___y_1060_ = v___y_1083_;
v___y_1061_ = v___x_1088_;
goto v___jp_1054_;
}
else
{
v___y_1069_ = v___y_1077_;
v___y_1070_ = v___y_1079_;
v___y_1071_ = v___y_1080_;
v___y_1072_ = v___y_1081_;
v___y_1073_ = v___y_1082_;
v___y_1074_ = v___y_1083_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___y_1077_;
v___y_1070_ = v___y_1079_;
v___y_1071_ = v___y_1080_;
v___y_1072_ = v___y_1081_;
v___y_1073_ = v___y_1082_;
v___y_1074_ = v___y_1083_;
goto v___jp_1068_;
}
}
else
{
v___y_1069_ = v___y_1077_;
v___y_1070_ = v___y_1079_;
v___y_1071_ = v___y_1080_;
v___y_1072_ = v___y_1081_;
v___y_1073_ = v___y_1082_;
v___y_1074_ = v___y_1083_;
goto v___jp_1068_;
}
}
v___jp_1089_:
{
if (v_bodyReplayable_1049_ == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v_current_1047_);
v___x_1099_ = lean_box(0);
return v___x_1099_;
}
else
{
if (v___y_1092_ == 0)
{
v___y_1077_ = v___y_1090_;
v___y_1078_ = v___y_1091_;
v___y_1079_ = v___y_1094_;
v___y_1080_ = v___y_1093_;
v___y_1081_ = v___y_1095_;
v___y_1082_ = v___y_1096_;
v___y_1083_ = v___y_1098_;
v___y_1084_ = v___y_1097_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1100_; 
lean_dec_ref(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v_current_1047_);
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
}
}
v___jp_1101_:
{
uint8_t v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = 9;
v___x_1112_ = l_Std_Http_instBEqMethod_beq(v___y_1106_, v___x_1111_);
if (v___x_1112_ == 0)
{
v___y_1090_ = v___y_1102_;
v___y_1091_ = v___y_1104_;
v___y_1092_ = v___y_1103_;
v___y_1093_ = v___y_1106_;
v___y_1094_ = v___y_1105_;
v___y_1095_ = v___y_1107_;
v___y_1096_ = v___y_1108_;
v___y_1097_ = v___y_1110_;
v___y_1098_ = v___y_1109_;
goto v___jp_1089_;
}
else
{
if (v___y_1103_ == 0)
{
v___y_1077_ = v___y_1102_;
v___y_1078_ = v___y_1104_;
v___y_1079_ = v___y_1105_;
v___y_1080_ = v___y_1106_;
v___y_1081_ = v___y_1107_;
v___y_1082_ = v___y_1108_;
v___y_1083_ = v___y_1109_;
v___y_1084_ = v___y_1110_;
goto v___jp_1076_;
}
else
{
v___y_1090_ = v___y_1102_;
v___y_1091_ = v___y_1104_;
v___y_1092_ = v___y_1103_;
v___y_1093_ = v___y_1106_;
v___y_1094_ = v___y_1105_;
v___y_1095_ = v___y_1107_;
v___y_1096_ = v___y_1108_;
v___y_1097_ = v___y_1110_;
v___y_1098_ = v___y_1109_;
goto v___jp_1089_;
}
}
}
v___jp_1113_:
{
uint8_t v___x_1123_; 
v___x_1123_ = l_Std_Http_instBEqMethod_beq(v___y_1118_, v___y_1116_);
if (v___x_1123_ == 0)
{
v___y_1102_ = v___y_1114_;
v___y_1103_ = v___y_1115_;
v___y_1104_ = v___y_1116_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___y_1118_;
v___y_1107_ = v___y_1119_;
v___y_1108_ = v___y_1120_;
v___y_1109_ = v___y_1122_;
v___y_1110_ = v___y_1121_;
goto v___jp_1101_;
}
else
{
if (v___y_1115_ == 0)
{
v___y_1077_ = v___y_1114_;
v___y_1078_ = v___y_1116_;
v___y_1079_ = v___y_1117_;
v___y_1080_ = v___y_1118_;
v___y_1081_ = v___y_1119_;
v___y_1082_ = v___y_1120_;
v___y_1083_ = v___y_1122_;
v___y_1084_ = v___y_1121_;
goto v___jp_1076_;
}
else
{
v___y_1102_ = v___y_1114_;
v___y_1103_ = v___y_1115_;
v___y_1104_ = v___y_1116_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___y_1118_;
v___y_1107_ = v___y_1119_;
v___y_1108_ = v___y_1120_;
v___y_1109_ = v___y_1122_;
v___y_1110_ = v___y_1121_;
goto v___jp_1101_;
}
}
}
v___jp_1124_:
{
if (v___y_1131_ == 0)
{
v___y_1114_ = v___y_1125_;
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1128_;
v___y_1118_ = v___y_1129_;
v___y_1119_ = v___y_1133_;
v___y_1120_ = v___y_1130_;
v___y_1121_ = v___y_1131_;
v___y_1122_ = v___y_1132_;
goto v___jp_1113_;
}
else
{
if (v___y_1126_ == 0)
{
v___y_1077_ = v___y_1125_;
v___y_1078_ = v___y_1127_;
v___y_1079_ = v___y_1128_;
v___y_1080_ = v___y_1129_;
v___y_1081_ = v___y_1133_;
v___y_1082_ = v___y_1130_;
v___y_1083_ = v___y_1132_;
v___y_1084_ = v___y_1131_;
goto v___jp_1076_;
}
else
{
v___y_1114_ = v___y_1125_;
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1128_;
v___y_1118_ = v___y_1129_;
v___y_1119_ = v___y_1133_;
v___y_1120_ = v___y_1130_;
v___y_1121_ = v___y_1131_;
v___y_1122_ = v___y_1132_;
goto v___jp_1113_;
}
}
}
v___jp_1134_:
{
lean_object* v_scrubbed_1144_; 
v_scrubbed_1144_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v___y_1141_, v___y_1143_, v___y_1142_);
if (v___y_1143_ == 0)
{
v___y_1125_ = v___y_1135_;
v___y_1126_ = v___y_1137_;
v___y_1127_ = v___y_1136_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___y_1138_;
v___y_1130_ = v___y_1140_;
v___y_1131_ = v___y_1142_;
v___y_1132_ = v___y_1143_;
v___y_1133_ = v_scrubbed_1144_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1145_; 
lean_inc_ref(v___y_1140_);
v___x_1145_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_1144_, v___y_1140_);
v___y_1125_ = v___y_1135_;
v___y_1126_ = v___y_1137_;
v___y_1127_ = v___y_1136_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___y_1138_;
v___y_1130_ = v___y_1140_;
v___y_1131_ = v___y_1142_;
v___y_1132_ = v___y_1143_;
v___y_1133_ = v___x_1145_;
goto v___jp_1124_;
}
}
v___jp_1146_:
{
if (v___y_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec_ref(v___y_1153_);
lean_dec_ref(v___y_1150_);
lean_dec_ref(v_current_1047_);
v___x_1157_ = lean_box(0);
return v___x_1157_;
}
else
{
if (v___y_1149_ == 0)
{
v___y_1135_ = v___y_1147_;
v___y_1136_ = v___y_1148_;
v___y_1137_ = v___y_1149_;
v___y_1138_ = v___y_1151_;
v___y_1139_ = v___y_1150_;
v___y_1140_ = v___y_1153_;
v___y_1141_ = v___y_1152_;
v___y_1142_ = v___y_1155_;
v___y_1143_ = v___y_1154_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v___y_1153_);
lean_dec_ref(v___y_1150_);
lean_dec_ref(v_current_1047_);
v___x_1158_ = lean_box(0);
return v___x_1158_;
}
}
}
v___jp_1159_:
{
if (v___y_1163_ == 0)
{
v___y_1147_ = v___y_1160_;
v___y_1148_ = v___y_1162_;
v___y_1149_ = v___y_1161_;
v___y_1150_ = v___y_1165_;
v___y_1151_ = v___y_1164_;
v___y_1152_ = v___y_1167_;
v___y_1153_ = v___y_1166_;
v___y_1154_ = v___y_1170_;
v___y_1155_ = v___y_1169_;
v___y_1156_ = v___y_1168_;
goto v___jp_1146_;
}
else
{
if (v___y_1161_ == 0)
{
v___y_1135_ = v___y_1160_;
v___y_1136_ = v___y_1162_;
v___y_1137_ = v___y_1161_;
v___y_1138_ = v___y_1164_;
v___y_1139_ = v___y_1165_;
v___y_1140_ = v___y_1166_;
v___y_1141_ = v___y_1167_;
v___y_1142_ = v___y_1169_;
v___y_1143_ = v___y_1170_;
goto v___jp_1134_;
}
else
{
v___y_1147_ = v___y_1160_;
v___y_1148_ = v___y_1162_;
v___y_1149_ = v___y_1161_;
v___y_1150_ = v___y_1165_;
v___y_1151_ = v___y_1164_;
v___y_1152_ = v___y_1167_;
v___y_1153_ = v___y_1166_;
v___y_1154_ = v___y_1170_;
v___y_1155_ = v___y_1169_;
v___y_1156_ = v___y_1168_;
goto v___jp_1146_;
}
}
}
v___jp_1171_:
{
if (v_bodyReplayable_1049_ == 0)
{
lean_object* v___x_1181_; 
lean_dec_ref(v___y_1178_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_current_1047_);
v___x_1181_ = lean_box(0);
return v___x_1181_;
}
else
{
if (v___y_1174_ == 0)
{
v___y_1135_ = v___y_1172_;
v___y_1136_ = v___y_1173_;
v___y_1137_ = v___y_1174_;
v___y_1138_ = v___y_1176_;
v___y_1139_ = v___y_1175_;
v___y_1140_ = v___y_1178_;
v___y_1141_ = v___y_1177_;
v___y_1142_ = v___y_1180_;
v___y_1143_ = v___y_1179_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1182_; 
lean_dec_ref(v___y_1178_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_current_1047_);
v___x_1182_ = lean_box(0);
return v___x_1182_;
}
}
}
v___jp_1183_:
{
if (v___y_1187_ == 0)
{
v___y_1172_ = v___y_1184_;
v___y_1173_ = v___y_1186_;
v___y_1174_ = v___y_1185_;
v___y_1175_ = v___y_1189_;
v___y_1176_ = v___y_1188_;
v___y_1177_ = v___y_1191_;
v___y_1178_ = v___y_1190_;
v___y_1179_ = v___y_1193_;
v___y_1180_ = v___y_1192_;
goto v___jp_1171_;
}
else
{
if (v___y_1185_ == 0)
{
v___y_1135_ = v___y_1184_;
v___y_1136_ = v___y_1186_;
v___y_1137_ = v___y_1185_;
v___y_1138_ = v___y_1188_;
v___y_1139_ = v___y_1189_;
v___y_1140_ = v___y_1190_;
v___y_1141_ = v___y_1191_;
v___y_1142_ = v___y_1192_;
v___y_1143_ = v___y_1193_;
goto v___jp_1134_;
}
else
{
v___y_1172_ = v___y_1184_;
v___y_1173_ = v___y_1186_;
v___y_1174_ = v___y_1185_;
v___y_1175_ = v___y_1189_;
v___y_1176_ = v___y_1188_;
v___y_1177_ = v___y_1191_;
v___y_1178_ = v___y_1190_;
v___y_1179_ = v___y_1193_;
v___y_1180_ = v___y_1192_;
goto v___jp_1171_;
}
}
}
v___jp_1194_:
{
uint8_t v___x_1206_; uint8_t v_isPost_1207_; 
v___x_1206_ = 23;
v_isPost_1207_ = l_Std_Http_instBEqMethod_beq(v___y_1195_, v___x_1206_);
switch(lean_obj_tag(v_status_1052_))
{
case 15:
{
v___y_1160_ = v___y_1196_;
v___y_1161_ = v___y_1198_;
v___y_1162_ = v___y_1197_;
v___y_1163_ = v___y_1205_;
v___y_1164_ = v___y_1200_;
v___y_1165_ = v___y_1199_;
v___y_1166_ = v___y_1202_;
v___y_1167_ = v___y_1201_;
v___y_1168_ = v_isPost_1207_;
v___y_1169_ = v___y_1204_;
v___y_1170_ = v___y_1203_;
goto v___jp_1159_;
}
case 16:
{
v___y_1160_ = v___y_1196_;
v___y_1161_ = v___y_1198_;
v___y_1162_ = v___y_1197_;
v___y_1163_ = v___y_1205_;
v___y_1164_ = v___y_1200_;
v___y_1165_ = v___y_1199_;
v___y_1166_ = v___y_1202_;
v___y_1167_ = v___y_1201_;
v___y_1168_ = v_isPost_1207_;
v___y_1169_ = v___y_1204_;
v___y_1170_ = v___y_1203_;
goto v___jp_1159_;
}
case 21:
{
v___y_1184_ = v___y_1196_;
v___y_1185_ = v___y_1198_;
v___y_1186_ = v___y_1197_;
v___y_1187_ = v___y_1205_;
v___y_1188_ = v___y_1200_;
v___y_1189_ = v___y_1199_;
v___y_1190_ = v___y_1202_;
v___y_1191_ = v___y_1201_;
v___y_1192_ = v___y_1204_;
v___y_1193_ = v___y_1203_;
goto v___jp_1183_;
}
case 22:
{
v___y_1184_ = v___y_1196_;
v___y_1185_ = v___y_1198_;
v___y_1186_ = v___y_1197_;
v___y_1187_ = v___y_1205_;
v___y_1188_ = v___y_1200_;
v___y_1189_ = v___y_1199_;
v___y_1190_ = v___y_1202_;
v___y_1191_ = v___y_1201_;
v___y_1192_ = v___y_1204_;
v___y_1193_ = v___y_1203_;
goto v___jp_1183_;
}
default: 
{
v___y_1135_ = v___y_1196_;
v___y_1136_ = v___y_1197_;
v___y_1137_ = v___y_1198_;
v___y_1138_ = v___y_1200_;
v___y_1139_ = v___y_1199_;
v___y_1140_ = v___y_1202_;
v___y_1141_ = v___y_1201_;
v___y_1142_ = v___y_1204_;
v___y_1143_ = v___y_1203_;
goto v___jp_1134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_1315_, lean_object* v_request_1316_, lean_object* v_bodyReplayable_1317_, lean_object* v_onlySafeRedirects_1318_, lean_object* v_responseVersion_1319_, lean_object* v_status_1320_, lean_object* v_responseHeaders_1321_){
_start:
{
uint8_t v_bodyReplayable_boxed_1322_; uint8_t v_onlySafeRedirects_boxed_1323_; uint8_t v_responseVersion_boxed_1324_; lean_object* v_res_1325_; 
v_bodyReplayable_boxed_1322_ = lean_unbox(v_bodyReplayable_1317_);
v_onlySafeRedirects_boxed_1323_ = lean_unbox(v_onlySafeRedirects_1318_);
v_responseVersion_boxed_1324_ = lean_unbox(v_responseVersion_1319_);
v_res_1325_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1315_, v_request_1316_, v_bodyReplayable_boxed_1322_, v_onlySafeRedirects_boxed_1323_, v_responseVersion_boxed_1324_, v_status_1320_, v_responseHeaders_1321_);
lean_dec_ref(v_responseHeaders_1321_);
lean_dec(v_status_1320_);
lean_dec_ref(v_request_1316_);
return v_res_1325_;
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
