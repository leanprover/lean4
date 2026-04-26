// Lean compiler output
// Module: Std.Http.Data.Method
// Imports: public import Init.Data.ToString public import Std.Http.Internal
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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Method_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Http.Method.acl"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__0 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__0_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__1 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__1_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Http.Method.baselineControl"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__2 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__2_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__3 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__3_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Http.Method.bind"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__4 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__4_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__4_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__5 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__5_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Http.Method.checkin"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__6 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__6_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__6_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__7 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__7_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Http.Method.checkout"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__8 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__8_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__8_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__9 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__9_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Http.Method.connect"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__10 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__10_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__10_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__11 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__11_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Http.Method.copy"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__12 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__12_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__12_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__13 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__13_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Http.Method.delete"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__14 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__14_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__14_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__15 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__15_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Http.Method.get"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__16 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__16_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__16_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__17 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__17_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Http.Method.head"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__18 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__18_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__18_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__19 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__19_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Http.Method.label"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__20 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__20_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__20_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__21 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__21_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Http.Method.link"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__22 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__22_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__22_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__23 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__23_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Http.Method.lock"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__24 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__24_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__24_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__25 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__25_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Http.Method.merge"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__26 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__26_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__26_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__27 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__27_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Http.Method.mkactivity"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__28 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__28_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__28_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__29 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__29_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Http.Method.mkcalendar"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__30 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__30_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__30_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__31 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__31_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Http.Method.mkcol"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__32 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__32_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__32_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__33 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__33_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Http.Method.mkredirectref"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__34 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__34_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__34_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__35 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__35_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Http.Method.mkworkspace"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__36 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__36_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__36_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__37 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__37_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Http.Method.move"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__38 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__38_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__38_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__39 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__39_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Http.Method.options"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__40 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__40_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__40_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__41 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__41_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Http.Method.orderpatch"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__42 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__42_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__42_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__43 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__43_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Http.Method.patch"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__44 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__44_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__44_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__45 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__45_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Http.Method.post"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__46 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__46_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__46_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__47 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__47_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Http.Method.pri"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__48 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__48_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__48_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__49 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__49_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Http.Method.propfind"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__50 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__50_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__50_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__51 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__51_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Std.Http.Method.proppatch"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__52 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__52_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__52_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__53 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__53_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Http.Method.put"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__54 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__54_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__54_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__55 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__55_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Http.Method.query"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__56 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__56_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__56_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__57 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__57_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Http.Method.rebind"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__58 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__58_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__58_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__59 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__59_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Http.Method.report"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__60 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__60_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__60_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__61 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__61_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Http.Method.search"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__62 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__62_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__62_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__63 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__63_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Http.Method.trace"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__64 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__64_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__64_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__65 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__65_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Http.Method.unbind"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__66 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__66_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__66_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__67 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__67_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Http.Method.uncheckout"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__68 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__68_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__68_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__69 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__69_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Http.Method.unlink"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__70 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__70_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__70_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__71 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__71_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Http.Method.unlock"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__72 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__72_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__72_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__73 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__73_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Http.Method.update"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__74 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__74_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__74_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__75 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__75_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Http.Method.updateredirectref"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__76 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__76_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__76_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__77 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__77_value;
static const lean_string_object l_Std_Http_instReprMethod_repr___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Std.Http.Method.versionControl"};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__78 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__78_value;
static const lean_ctor_object l_Std_Http_instReprMethod_repr___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprMethod_repr___closed__78_value)}};
static const lean_object* l_Std_Http_instReprMethod_repr___closed__79 = (const lean_object*)&l_Std_Http_instReprMethod_repr___closed__79_value;
static lean_once_cell_t l_Std_Http_instReprMethod_repr___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprMethod_repr___closed__80;
static lean_once_cell_t l_Std_Http_instReprMethod_repr___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprMethod_repr___closed__81;
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprMethod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprMethod_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprMethod___closed__0 = (const lean_object*)&l_Std_Http_instReprMethod___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprMethod = (const lean_object*)&l_Std_Http_instReprMethod___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_instInhabitedMethod_default;
LEAN_EXPORT uint8_t l_Std_Http_instInhabitedMethod;
LEAN_EXPORT uint8_t l_Std_Http_instBEqMethod_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_instBEqMethod_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instBEqMethod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instBEqMethod_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instBEqMethod___closed__0 = (const lean_object*)&l_Std_Http_instBEqMethod___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instBEqMethod = (const lean_object*)&l_Std_Http_instBEqMethod___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Method_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_instDecidableEqMethod(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_instDecidableEqMethod___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__0 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__0_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__1 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__1_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__2 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__2_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__3 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__3_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__4 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__4_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__5 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__5_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__6 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__6_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__7 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__7_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__8 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__8_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__9 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__9_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__10 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__10_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__11 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__11_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__12 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__12_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__13 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__13_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__14 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__14_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__15 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__15_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__16 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__16_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__17 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__17_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__18 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__18_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__19 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__19_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__20 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__20_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__21 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__21_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__22 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__22_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__23 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__23_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__24 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__24_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__25 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__25_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__26 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__26_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__27 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__27_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__28 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__28_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__29 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__29_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__30 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__30_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__31 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__31_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__32 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__32_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__33 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__33_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__34 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__34_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__35 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__35_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__36 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__36_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__37 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__37_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__38 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__38_value;
static const lean_string_object l_Std_Http_Method_ofString_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__39 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__39_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__40 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__40_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__41 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__41_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__42 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__42_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__43 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__43_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__44 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__44_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__45 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__45_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__46 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__46_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__47 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__47_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__48 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__48_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__49 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__49_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__50 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__50_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__51 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__51_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__52 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__52_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__53 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__53_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__54 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__54_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__55 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__55_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__56 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__56_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__57 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__57_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__58 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__58_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__59 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__59_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__60 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__60_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__61 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__61_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__62 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__62_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__63 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__63_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__64 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__64_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(14) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__65 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__65_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__66 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__66_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__67 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__67_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__68 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__68_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__69 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__69_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__70 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__70_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__71 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__71_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__72 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__72_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__73 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__73_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__74 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__74_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__75 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__75_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__76 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__76_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__77 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__77_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__78 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__78_value;
static const lean_ctor_object l_Std_Http_Method_ofString_x3f___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Method_ofString_x3f___closed__79 = (const lean_object*)&l_Std_Http_Method_ofString_x3f___closed__79_value;
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00Std_Http_Method_ofString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Method_ofString_x21_spec__0___boxed(lean_object*);
static const lean_string_object l_Std_Http_Method_ofString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Std.Http.Data.Method"};
static const lean_object* l_Std_Http_Method_ofString_x21___closed__0 = (const lean_object*)&l_Std_Http_Method_ofString_x21___closed__0_value;
static const lean_string_object l_Std_Http_Method_ofString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Std.Http.Method.ofString!"};
static const lean_object* l_Std_Http_Method_ofString_x21___closed__1 = (const lean_object*)&l_Std_Http_Method_ofString_x21___closed__1_value;
static const lean_string_object l_Std_Http_Method_ofString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid HTTP method: "};
static const lean_object* l_Std_Http_Method_ofString_x21___closed__2 = (const lean_object*)&l_Std_Http_Method_ofString_x21___closed__2_value;
LEAN_EXPORT uint8_t l_Std_Http_Method_ofString_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Method_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Method_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Method_instToString___closed__0 = (const lean_object*)&l_Std_Http_Method_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Method_instToString = (const lean_object*)&l_Std_Http_Method_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Method_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Method_instEncodeV11___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Method_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_Method_instEncodeV11___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Method_instEncodeV11 = (const lean_object*)&l_Std_Http_Method_instEncodeV11___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
case 7:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
case 8:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(8u);
return v___x_10_;
}
case 9:
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(9u);
return v___x_11_;
}
case 10:
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(10u);
return v___x_12_;
}
case 11:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(11u);
return v___x_13_;
}
case 12:
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(12u);
return v___x_14_;
}
case 13:
{
lean_object* v___x_15_; 
v___x_15_ = lean_unsigned_to_nat(13u);
return v___x_15_;
}
case 14:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(14u);
return v___x_16_;
}
case 15:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(15u);
return v___x_17_;
}
case 16:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(16u);
return v___x_18_;
}
case 17:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(17u);
return v___x_19_;
}
case 18:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(18u);
return v___x_20_;
}
case 19:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(19u);
return v___x_21_;
}
case 20:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(20u);
return v___x_22_;
}
case 21:
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(21u);
return v___x_23_;
}
case 22:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(22u);
return v___x_24_;
}
case 23:
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(23u);
return v___x_25_;
}
case 24:
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(24u);
return v___x_26_;
}
case 25:
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(25u);
return v___x_27_;
}
case 26:
{
lean_object* v___x_28_; 
v___x_28_ = lean_unsigned_to_nat(26u);
return v___x_28_;
}
case 27:
{
lean_object* v___x_29_; 
v___x_29_ = lean_unsigned_to_nat(27u);
return v___x_29_;
}
case 28:
{
lean_object* v___x_30_; 
v___x_30_ = lean_unsigned_to_nat(28u);
return v___x_30_;
}
case 29:
{
lean_object* v___x_31_; 
v___x_31_ = lean_unsigned_to_nat(29u);
return v___x_31_;
}
case 30:
{
lean_object* v___x_32_; 
v___x_32_ = lean_unsigned_to_nat(30u);
return v___x_32_;
}
case 31:
{
lean_object* v___x_33_; 
v___x_33_ = lean_unsigned_to_nat(31u);
return v___x_33_;
}
case 32:
{
lean_object* v___x_34_; 
v___x_34_ = lean_unsigned_to_nat(32u);
return v___x_34_;
}
case 33:
{
lean_object* v___x_35_; 
v___x_35_ = lean_unsigned_to_nat(33u);
return v___x_35_;
}
case 34:
{
lean_object* v___x_36_; 
v___x_36_ = lean_unsigned_to_nat(34u);
return v___x_36_;
}
case 35:
{
lean_object* v___x_37_; 
v___x_37_ = lean_unsigned_to_nat(35u);
return v___x_37_;
}
case 36:
{
lean_object* v___x_38_; 
v___x_38_ = lean_unsigned_to_nat(36u);
return v___x_38_;
}
case 37:
{
lean_object* v___x_39_; 
v___x_39_ = lean_unsigned_to_nat(37u);
return v___x_39_;
}
case 38:
{
lean_object* v___x_40_; 
v___x_40_ = lean_unsigned_to_nat(38u);
return v___x_40_;
}
default: 
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(39u);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx___boxed(lean_object* v_x_42_){
_start:
{
uint8_t v_x_boxed_43_; lean_object* v_res_44_; 
v_x_boxed_43_ = lean_unbox(v_x_42_);
v_res_44_ = l_Std_Http_Method_ctorIdx(v_x_boxed_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_toCtorIdx(uint8_t v_x_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Http_Method_ctorIdx(v_x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_toCtorIdx___boxed(lean_object* v_x_47_){
_start:
{
uint8_t v_x_4__boxed_48_; lean_object* v_res_49_; 
v_x_4__boxed_48_ = lean_unbox(v_x_47_);
v_res_49_ = l_Std_Http_Method_toCtorIdx(v_x_4__boxed_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg(lean_object* v_k_50_){
_start:
{
lean_inc(v_k_50_);
return v_k_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg___boxed(lean_object* v_k_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Http_Method_ctorElim___redArg(v_k_51_);
lean_dec(v_k_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim(lean_object* v_motive_53_, lean_object* v_ctorIdx_54_, uint8_t v_t_55_, lean_object* v_h_56_, lean_object* v_k_57_){
_start:
{
lean_inc(v_k_57_);
return v_k_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___boxed(lean_object* v_motive_58_, lean_object* v_ctorIdx_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_k_62_){
_start:
{
uint8_t v_t_boxed_63_; lean_object* v_res_64_; 
v_t_boxed_63_ = lean_unbox(v_t_60_);
v_res_64_ = l_Std_Http_Method_ctorElim(v_motive_58_, v_ctorIdx_59_, v_t_boxed_63_, v_h_61_, v_k_62_);
lean_dec(v_k_62_);
lean_dec(v_ctorIdx_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg(lean_object* v_acl_65_){
_start:
{
lean_inc(v_acl_65_);
return v_acl_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg___boxed(lean_object* v_acl_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_Http_Method_acl_elim___redArg(v_acl_66_);
lean_dec(v_acl_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim(lean_object* v_motive_68_, uint8_t v_t_69_, lean_object* v_h_70_, lean_object* v_acl_71_){
_start:
{
lean_inc(v_acl_71_);
return v_acl_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_acl_75_){
_start:
{
uint8_t v_t_boxed_76_; lean_object* v_res_77_; 
v_t_boxed_76_ = lean_unbox(v_t_73_);
v_res_77_ = l_Std_Http_Method_acl_elim(v_motive_72_, v_t_boxed_76_, v_h_74_, v_acl_75_);
lean_dec(v_acl_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg(lean_object* v_baselineControl_78_){
_start:
{
lean_inc(v_baselineControl_78_);
return v_baselineControl_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg___boxed(lean_object* v_baselineControl_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_Http_Method_baselineControl_elim___redArg(v_baselineControl_79_);
lean_dec(v_baselineControl_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim(lean_object* v_motive_81_, uint8_t v_t_82_, lean_object* v_h_83_, lean_object* v_baselineControl_84_){
_start:
{
lean_inc(v_baselineControl_84_);
return v_baselineControl_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___boxed(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_baselineControl_88_){
_start:
{
uint8_t v_t_boxed_89_; lean_object* v_res_90_; 
v_t_boxed_89_ = lean_unbox(v_t_86_);
v_res_90_ = l_Std_Http_Method_baselineControl_elim(v_motive_85_, v_t_boxed_89_, v_h_87_, v_baselineControl_88_);
lean_dec(v_baselineControl_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg(lean_object* v_bind_91_){
_start:
{
lean_inc(v_bind_91_);
return v_bind_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg___boxed(lean_object* v_bind_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_Http_Method_bind_elim___redArg(v_bind_92_);
lean_dec(v_bind_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim(lean_object* v_motive_94_, uint8_t v_t_95_, lean_object* v_h_96_, lean_object* v_bind_97_){
_start:
{
lean_inc(v_bind_97_);
return v_bind_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___boxed(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_bind_101_){
_start:
{
uint8_t v_t_boxed_102_; lean_object* v_res_103_; 
v_t_boxed_102_ = lean_unbox(v_t_99_);
v_res_103_ = l_Std_Http_Method_bind_elim(v_motive_98_, v_t_boxed_102_, v_h_100_, v_bind_101_);
lean_dec(v_bind_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg(lean_object* v_checkin_104_){
_start:
{
lean_inc(v_checkin_104_);
return v_checkin_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg___boxed(lean_object* v_checkin_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Http_Method_checkin_elim___redArg(v_checkin_105_);
lean_dec(v_checkin_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim(lean_object* v_motive_107_, uint8_t v_t_108_, lean_object* v_h_109_, lean_object* v_checkin_110_){
_start:
{
lean_inc(v_checkin_110_);
return v_checkin_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___boxed(lean_object* v_motive_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_checkin_114_){
_start:
{
uint8_t v_t_boxed_115_; lean_object* v_res_116_; 
v_t_boxed_115_ = lean_unbox(v_t_112_);
v_res_116_ = l_Std_Http_Method_checkin_elim(v_motive_111_, v_t_boxed_115_, v_h_113_, v_checkin_114_);
lean_dec(v_checkin_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg(lean_object* v_checkout_117_){
_start:
{
lean_inc(v_checkout_117_);
return v_checkout_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg___boxed(lean_object* v_checkout_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_Http_Method_checkout_elim___redArg(v_checkout_118_);
lean_dec(v_checkout_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim(lean_object* v_motive_120_, uint8_t v_t_121_, lean_object* v_h_122_, lean_object* v_checkout_123_){
_start:
{
lean_inc(v_checkout_123_);
return v_checkout_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___boxed(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_checkout_127_){
_start:
{
uint8_t v_t_boxed_128_; lean_object* v_res_129_; 
v_t_boxed_128_ = lean_unbox(v_t_125_);
v_res_129_ = l_Std_Http_Method_checkout_elim(v_motive_124_, v_t_boxed_128_, v_h_126_, v_checkout_127_);
lean_dec(v_checkout_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg(lean_object* v_connect_130_){
_start:
{
lean_inc(v_connect_130_);
return v_connect_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg___boxed(lean_object* v_connect_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Http_Method_connect_elim___redArg(v_connect_131_);
lean_dec(v_connect_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim(lean_object* v_motive_133_, uint8_t v_t_134_, lean_object* v_h_135_, lean_object* v_connect_136_){
_start:
{
lean_inc(v_connect_136_);
return v_connect_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___boxed(lean_object* v_motive_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_connect_140_){
_start:
{
uint8_t v_t_boxed_141_; lean_object* v_res_142_; 
v_t_boxed_141_ = lean_unbox(v_t_138_);
v_res_142_ = l_Std_Http_Method_connect_elim(v_motive_137_, v_t_boxed_141_, v_h_139_, v_connect_140_);
lean_dec(v_connect_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg(lean_object* v_copy_143_){
_start:
{
lean_inc(v_copy_143_);
return v_copy_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg___boxed(lean_object* v_copy_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_Http_Method_copy_elim___redArg(v_copy_144_);
lean_dec(v_copy_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim(lean_object* v_motive_146_, uint8_t v_t_147_, lean_object* v_h_148_, lean_object* v_copy_149_){
_start:
{
lean_inc(v_copy_149_);
return v_copy_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___boxed(lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_copy_153_){
_start:
{
uint8_t v_t_boxed_154_; lean_object* v_res_155_; 
v_t_boxed_154_ = lean_unbox(v_t_151_);
v_res_155_ = l_Std_Http_Method_copy_elim(v_motive_150_, v_t_boxed_154_, v_h_152_, v_copy_153_);
lean_dec(v_copy_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg(lean_object* v_delete_156_){
_start:
{
lean_inc(v_delete_156_);
return v_delete_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg___boxed(lean_object* v_delete_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_Http_Method_delete_elim___redArg(v_delete_157_);
lean_dec(v_delete_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim(lean_object* v_motive_159_, uint8_t v_t_160_, lean_object* v_h_161_, lean_object* v_delete_162_){
_start:
{
lean_inc(v_delete_162_);
return v_delete_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___boxed(lean_object* v_motive_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_delete_166_){
_start:
{
uint8_t v_t_boxed_167_; lean_object* v_res_168_; 
v_t_boxed_167_ = lean_unbox(v_t_164_);
v_res_168_ = l_Std_Http_Method_delete_elim(v_motive_163_, v_t_boxed_167_, v_h_165_, v_delete_166_);
lean_dec(v_delete_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg(lean_object* v_get_169_){
_start:
{
lean_inc(v_get_169_);
return v_get_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg___boxed(lean_object* v_get_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_Http_Method_get_elim___redArg(v_get_170_);
lean_dec(v_get_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim(lean_object* v_motive_172_, uint8_t v_t_173_, lean_object* v_h_174_, lean_object* v_get_175_){
_start:
{
lean_inc(v_get_175_);
return v_get_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___boxed(lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_get_179_){
_start:
{
uint8_t v_t_boxed_180_; lean_object* v_res_181_; 
v_t_boxed_180_ = lean_unbox(v_t_177_);
v_res_181_ = l_Std_Http_Method_get_elim(v_motive_176_, v_t_boxed_180_, v_h_178_, v_get_179_);
lean_dec(v_get_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg(lean_object* v_head_182_){
_start:
{
lean_inc(v_head_182_);
return v_head_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg___boxed(lean_object* v_head_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_Http_Method_head_elim___redArg(v_head_183_);
lean_dec(v_head_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim(lean_object* v_motive_185_, uint8_t v_t_186_, lean_object* v_h_187_, lean_object* v_head_188_){
_start:
{
lean_inc(v_head_188_);
return v_head_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___boxed(lean_object* v_motive_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_head_192_){
_start:
{
uint8_t v_t_boxed_193_; lean_object* v_res_194_; 
v_t_boxed_193_ = lean_unbox(v_t_190_);
v_res_194_ = l_Std_Http_Method_head_elim(v_motive_189_, v_t_boxed_193_, v_h_191_, v_head_192_);
lean_dec(v_head_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg(lean_object* v_label_195_){
_start:
{
lean_inc(v_label_195_);
return v_label_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg___boxed(lean_object* v_label_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_Http_Method_label_elim___redArg(v_label_196_);
lean_dec(v_label_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim(lean_object* v_motive_198_, uint8_t v_t_199_, lean_object* v_h_200_, lean_object* v_label_201_){
_start:
{
lean_inc(v_label_201_);
return v_label_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___boxed(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_label_205_){
_start:
{
uint8_t v_t_boxed_206_; lean_object* v_res_207_; 
v_t_boxed_206_ = lean_unbox(v_t_203_);
v_res_207_ = l_Std_Http_Method_label_elim(v_motive_202_, v_t_boxed_206_, v_h_204_, v_label_205_);
lean_dec(v_label_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg(lean_object* v_link_208_){
_start:
{
lean_inc(v_link_208_);
return v_link_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg___boxed(lean_object* v_link_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Http_Method_link_elim___redArg(v_link_209_);
lean_dec(v_link_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim(lean_object* v_motive_211_, uint8_t v_t_212_, lean_object* v_h_213_, lean_object* v_link_214_){
_start:
{
lean_inc(v_link_214_);
return v_link_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___boxed(lean_object* v_motive_215_, lean_object* v_t_216_, lean_object* v_h_217_, lean_object* v_link_218_){
_start:
{
uint8_t v_t_boxed_219_; lean_object* v_res_220_; 
v_t_boxed_219_ = lean_unbox(v_t_216_);
v_res_220_ = l_Std_Http_Method_link_elim(v_motive_215_, v_t_boxed_219_, v_h_217_, v_link_218_);
lean_dec(v_link_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg(lean_object* v_lock_221_){
_start:
{
lean_inc(v_lock_221_);
return v_lock_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg___boxed(lean_object* v_lock_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Http_Method_lock_elim___redArg(v_lock_222_);
lean_dec(v_lock_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim(lean_object* v_motive_224_, uint8_t v_t_225_, lean_object* v_h_226_, lean_object* v_lock_227_){
_start:
{
lean_inc(v_lock_227_);
return v_lock_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___boxed(lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_lock_231_){
_start:
{
uint8_t v_t_boxed_232_; lean_object* v_res_233_; 
v_t_boxed_232_ = lean_unbox(v_t_229_);
v_res_233_ = l_Std_Http_Method_lock_elim(v_motive_228_, v_t_boxed_232_, v_h_230_, v_lock_231_);
lean_dec(v_lock_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg(lean_object* v_merge_234_){
_start:
{
lean_inc(v_merge_234_);
return v_merge_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg___boxed(lean_object* v_merge_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Http_Method_merge_elim___redArg(v_merge_235_);
lean_dec(v_merge_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim(lean_object* v_motive_237_, uint8_t v_t_238_, lean_object* v_h_239_, lean_object* v_merge_240_){
_start:
{
lean_inc(v_merge_240_);
return v_merge_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___boxed(lean_object* v_motive_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_merge_244_){
_start:
{
uint8_t v_t_boxed_245_; lean_object* v_res_246_; 
v_t_boxed_245_ = lean_unbox(v_t_242_);
v_res_246_ = l_Std_Http_Method_merge_elim(v_motive_241_, v_t_boxed_245_, v_h_243_, v_merge_244_);
lean_dec(v_merge_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg(lean_object* v_mkactivity_247_){
_start:
{
lean_inc(v_mkactivity_247_);
return v_mkactivity_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg___boxed(lean_object* v_mkactivity_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_Http_Method_mkactivity_elim___redArg(v_mkactivity_248_);
lean_dec(v_mkactivity_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim(lean_object* v_motive_250_, uint8_t v_t_251_, lean_object* v_h_252_, lean_object* v_mkactivity_253_){
_start:
{
lean_inc(v_mkactivity_253_);
return v_mkactivity_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___boxed(lean_object* v_motive_254_, lean_object* v_t_255_, lean_object* v_h_256_, lean_object* v_mkactivity_257_){
_start:
{
uint8_t v_t_boxed_258_; lean_object* v_res_259_; 
v_t_boxed_258_ = lean_unbox(v_t_255_);
v_res_259_ = l_Std_Http_Method_mkactivity_elim(v_motive_254_, v_t_boxed_258_, v_h_256_, v_mkactivity_257_);
lean_dec(v_mkactivity_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg(lean_object* v_mkcalendar_260_){
_start:
{
lean_inc(v_mkcalendar_260_);
return v_mkcalendar_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg___boxed(lean_object* v_mkcalendar_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Http_Method_mkcalendar_elim___redArg(v_mkcalendar_261_);
lean_dec(v_mkcalendar_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim(lean_object* v_motive_263_, uint8_t v_t_264_, lean_object* v_h_265_, lean_object* v_mkcalendar_266_){
_start:
{
lean_inc(v_mkcalendar_266_);
return v_mkcalendar_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___boxed(lean_object* v_motive_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_mkcalendar_270_){
_start:
{
uint8_t v_t_boxed_271_; lean_object* v_res_272_; 
v_t_boxed_271_ = lean_unbox(v_t_268_);
v_res_272_ = l_Std_Http_Method_mkcalendar_elim(v_motive_267_, v_t_boxed_271_, v_h_269_, v_mkcalendar_270_);
lean_dec(v_mkcalendar_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg(lean_object* v_mkcol_273_){
_start:
{
lean_inc(v_mkcol_273_);
return v_mkcol_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg___boxed(lean_object* v_mkcol_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_Http_Method_mkcol_elim___redArg(v_mkcol_274_);
lean_dec(v_mkcol_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim(lean_object* v_motive_276_, uint8_t v_t_277_, lean_object* v_h_278_, lean_object* v_mkcol_279_){
_start:
{
lean_inc(v_mkcol_279_);
return v_mkcol_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___boxed(lean_object* v_motive_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_mkcol_283_){
_start:
{
uint8_t v_t_boxed_284_; lean_object* v_res_285_; 
v_t_boxed_284_ = lean_unbox(v_t_281_);
v_res_285_ = l_Std_Http_Method_mkcol_elim(v_motive_280_, v_t_boxed_284_, v_h_282_, v_mkcol_283_);
lean_dec(v_mkcol_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg(lean_object* v_mkredirectref_286_){
_start:
{
lean_inc(v_mkredirectref_286_);
return v_mkredirectref_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg___boxed(lean_object* v_mkredirectref_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Http_Method_mkredirectref_elim___redArg(v_mkredirectref_287_);
lean_dec(v_mkredirectref_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim(lean_object* v_motive_289_, uint8_t v_t_290_, lean_object* v_h_291_, lean_object* v_mkredirectref_292_){
_start:
{
lean_inc(v_mkredirectref_292_);
return v_mkredirectref_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___boxed(lean_object* v_motive_293_, lean_object* v_t_294_, lean_object* v_h_295_, lean_object* v_mkredirectref_296_){
_start:
{
uint8_t v_t_boxed_297_; lean_object* v_res_298_; 
v_t_boxed_297_ = lean_unbox(v_t_294_);
v_res_298_ = l_Std_Http_Method_mkredirectref_elim(v_motive_293_, v_t_boxed_297_, v_h_295_, v_mkredirectref_296_);
lean_dec(v_mkredirectref_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg(lean_object* v_mkworkspace_299_){
_start:
{
lean_inc(v_mkworkspace_299_);
return v_mkworkspace_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg___boxed(lean_object* v_mkworkspace_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_Http_Method_mkworkspace_elim___redArg(v_mkworkspace_300_);
lean_dec(v_mkworkspace_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim(lean_object* v_motive_302_, uint8_t v_t_303_, lean_object* v_h_304_, lean_object* v_mkworkspace_305_){
_start:
{
lean_inc(v_mkworkspace_305_);
return v_mkworkspace_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___boxed(lean_object* v_motive_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_mkworkspace_309_){
_start:
{
uint8_t v_t_boxed_310_; lean_object* v_res_311_; 
v_t_boxed_310_ = lean_unbox(v_t_307_);
v_res_311_ = l_Std_Http_Method_mkworkspace_elim(v_motive_306_, v_t_boxed_310_, v_h_308_, v_mkworkspace_309_);
lean_dec(v_mkworkspace_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg(lean_object* v_move_312_){
_start:
{
lean_inc(v_move_312_);
return v_move_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg___boxed(lean_object* v_move_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Http_Method_move_elim___redArg(v_move_313_);
lean_dec(v_move_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim(lean_object* v_motive_315_, uint8_t v_t_316_, lean_object* v_h_317_, lean_object* v_move_318_){
_start:
{
lean_inc(v_move_318_);
return v_move_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___boxed(lean_object* v_motive_319_, lean_object* v_t_320_, lean_object* v_h_321_, lean_object* v_move_322_){
_start:
{
uint8_t v_t_boxed_323_; lean_object* v_res_324_; 
v_t_boxed_323_ = lean_unbox(v_t_320_);
v_res_324_ = l_Std_Http_Method_move_elim(v_motive_319_, v_t_boxed_323_, v_h_321_, v_move_322_);
lean_dec(v_move_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg(lean_object* v_options_325_){
_start:
{
lean_inc(v_options_325_);
return v_options_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg___boxed(lean_object* v_options_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Http_Method_options_elim___redArg(v_options_326_);
lean_dec(v_options_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim(lean_object* v_motive_328_, uint8_t v_t_329_, lean_object* v_h_330_, lean_object* v_options_331_){
_start:
{
lean_inc(v_options_331_);
return v_options_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___boxed(lean_object* v_motive_332_, lean_object* v_t_333_, lean_object* v_h_334_, lean_object* v_options_335_){
_start:
{
uint8_t v_t_boxed_336_; lean_object* v_res_337_; 
v_t_boxed_336_ = lean_unbox(v_t_333_);
v_res_337_ = l_Std_Http_Method_options_elim(v_motive_332_, v_t_boxed_336_, v_h_334_, v_options_335_);
lean_dec(v_options_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg(lean_object* v_orderpatch_338_){
_start:
{
lean_inc(v_orderpatch_338_);
return v_orderpatch_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg___boxed(lean_object* v_orderpatch_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Http_Method_orderpatch_elim___redArg(v_orderpatch_339_);
lean_dec(v_orderpatch_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim(lean_object* v_motive_341_, uint8_t v_t_342_, lean_object* v_h_343_, lean_object* v_orderpatch_344_){
_start:
{
lean_inc(v_orderpatch_344_);
return v_orderpatch_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___boxed(lean_object* v_motive_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_orderpatch_348_){
_start:
{
uint8_t v_t_boxed_349_; lean_object* v_res_350_; 
v_t_boxed_349_ = lean_unbox(v_t_346_);
v_res_350_ = l_Std_Http_Method_orderpatch_elim(v_motive_345_, v_t_boxed_349_, v_h_347_, v_orderpatch_348_);
lean_dec(v_orderpatch_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg(lean_object* v_patch_351_){
_start:
{
lean_inc(v_patch_351_);
return v_patch_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg___boxed(lean_object* v_patch_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Http_Method_patch_elim___redArg(v_patch_352_);
lean_dec(v_patch_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim(lean_object* v_motive_354_, uint8_t v_t_355_, lean_object* v_h_356_, lean_object* v_patch_357_){
_start:
{
lean_inc(v_patch_357_);
return v_patch_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___boxed(lean_object* v_motive_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_patch_361_){
_start:
{
uint8_t v_t_boxed_362_; lean_object* v_res_363_; 
v_t_boxed_362_ = lean_unbox(v_t_359_);
v_res_363_ = l_Std_Http_Method_patch_elim(v_motive_358_, v_t_boxed_362_, v_h_360_, v_patch_361_);
lean_dec(v_patch_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg(lean_object* v_post_364_){
_start:
{
lean_inc(v_post_364_);
return v_post_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg___boxed(lean_object* v_post_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Http_Method_post_elim___redArg(v_post_365_);
lean_dec(v_post_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim(lean_object* v_motive_367_, uint8_t v_t_368_, lean_object* v_h_369_, lean_object* v_post_370_){
_start:
{
lean_inc(v_post_370_);
return v_post_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___boxed(lean_object* v_motive_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_post_374_){
_start:
{
uint8_t v_t_boxed_375_; lean_object* v_res_376_; 
v_t_boxed_375_ = lean_unbox(v_t_372_);
v_res_376_ = l_Std_Http_Method_post_elim(v_motive_371_, v_t_boxed_375_, v_h_373_, v_post_374_);
lean_dec(v_post_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg(lean_object* v_pri_377_){
_start:
{
lean_inc(v_pri_377_);
return v_pri_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg___boxed(lean_object* v_pri_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Http_Method_pri_elim___redArg(v_pri_378_);
lean_dec(v_pri_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim(lean_object* v_motive_380_, uint8_t v_t_381_, lean_object* v_h_382_, lean_object* v_pri_383_){
_start:
{
lean_inc(v_pri_383_);
return v_pri_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___boxed(lean_object* v_motive_384_, lean_object* v_t_385_, lean_object* v_h_386_, lean_object* v_pri_387_){
_start:
{
uint8_t v_t_boxed_388_; lean_object* v_res_389_; 
v_t_boxed_388_ = lean_unbox(v_t_385_);
v_res_389_ = l_Std_Http_Method_pri_elim(v_motive_384_, v_t_boxed_388_, v_h_386_, v_pri_387_);
lean_dec(v_pri_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg(lean_object* v_propfind_390_){
_start:
{
lean_inc(v_propfind_390_);
return v_propfind_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg___boxed(lean_object* v_propfind_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Http_Method_propfind_elim___redArg(v_propfind_391_);
lean_dec(v_propfind_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim(lean_object* v_motive_393_, uint8_t v_t_394_, lean_object* v_h_395_, lean_object* v_propfind_396_){
_start:
{
lean_inc(v_propfind_396_);
return v_propfind_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___boxed(lean_object* v_motive_397_, lean_object* v_t_398_, lean_object* v_h_399_, lean_object* v_propfind_400_){
_start:
{
uint8_t v_t_boxed_401_; lean_object* v_res_402_; 
v_t_boxed_401_ = lean_unbox(v_t_398_);
v_res_402_ = l_Std_Http_Method_propfind_elim(v_motive_397_, v_t_boxed_401_, v_h_399_, v_propfind_400_);
lean_dec(v_propfind_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg(lean_object* v_proppatch_403_){
_start:
{
lean_inc(v_proppatch_403_);
return v_proppatch_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg___boxed(lean_object* v_proppatch_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Http_Method_proppatch_elim___redArg(v_proppatch_404_);
lean_dec(v_proppatch_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim(lean_object* v_motive_406_, uint8_t v_t_407_, lean_object* v_h_408_, lean_object* v_proppatch_409_){
_start:
{
lean_inc(v_proppatch_409_);
return v_proppatch_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___boxed(lean_object* v_motive_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_proppatch_413_){
_start:
{
uint8_t v_t_boxed_414_; lean_object* v_res_415_; 
v_t_boxed_414_ = lean_unbox(v_t_411_);
v_res_415_ = l_Std_Http_Method_proppatch_elim(v_motive_410_, v_t_boxed_414_, v_h_412_, v_proppatch_413_);
lean_dec(v_proppatch_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg(lean_object* v_put_416_){
_start:
{
lean_inc(v_put_416_);
return v_put_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg___boxed(lean_object* v_put_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Http_Method_put_elim___redArg(v_put_417_);
lean_dec(v_put_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim(lean_object* v_motive_419_, uint8_t v_t_420_, lean_object* v_h_421_, lean_object* v_put_422_){
_start:
{
lean_inc(v_put_422_);
return v_put_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___boxed(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_put_426_){
_start:
{
uint8_t v_t_boxed_427_; lean_object* v_res_428_; 
v_t_boxed_427_ = lean_unbox(v_t_424_);
v_res_428_ = l_Std_Http_Method_put_elim(v_motive_423_, v_t_boxed_427_, v_h_425_, v_put_426_);
lean_dec(v_put_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg(lean_object* v_query_429_){
_start:
{
lean_inc(v_query_429_);
return v_query_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg___boxed(lean_object* v_query_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_Http_Method_query_elim___redArg(v_query_430_);
lean_dec(v_query_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim(lean_object* v_motive_432_, uint8_t v_t_433_, lean_object* v_h_434_, lean_object* v_query_435_){
_start:
{
lean_inc(v_query_435_);
return v_query_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___boxed(lean_object* v_motive_436_, lean_object* v_t_437_, lean_object* v_h_438_, lean_object* v_query_439_){
_start:
{
uint8_t v_t_boxed_440_; lean_object* v_res_441_; 
v_t_boxed_440_ = lean_unbox(v_t_437_);
v_res_441_ = l_Std_Http_Method_query_elim(v_motive_436_, v_t_boxed_440_, v_h_438_, v_query_439_);
lean_dec(v_query_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg(lean_object* v_rebind_442_){
_start:
{
lean_inc(v_rebind_442_);
return v_rebind_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg___boxed(lean_object* v_rebind_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_Http_Method_rebind_elim___redArg(v_rebind_443_);
lean_dec(v_rebind_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim(lean_object* v_motive_445_, uint8_t v_t_446_, lean_object* v_h_447_, lean_object* v_rebind_448_){
_start:
{
lean_inc(v_rebind_448_);
return v_rebind_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___boxed(lean_object* v_motive_449_, lean_object* v_t_450_, lean_object* v_h_451_, lean_object* v_rebind_452_){
_start:
{
uint8_t v_t_boxed_453_; lean_object* v_res_454_; 
v_t_boxed_453_ = lean_unbox(v_t_450_);
v_res_454_ = l_Std_Http_Method_rebind_elim(v_motive_449_, v_t_boxed_453_, v_h_451_, v_rebind_452_);
lean_dec(v_rebind_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg(lean_object* v_report_455_){
_start:
{
lean_inc(v_report_455_);
return v_report_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg___boxed(lean_object* v_report_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_Http_Method_report_elim___redArg(v_report_456_);
lean_dec(v_report_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim(lean_object* v_motive_458_, uint8_t v_t_459_, lean_object* v_h_460_, lean_object* v_report_461_){
_start:
{
lean_inc(v_report_461_);
return v_report_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___boxed(lean_object* v_motive_462_, lean_object* v_t_463_, lean_object* v_h_464_, lean_object* v_report_465_){
_start:
{
uint8_t v_t_boxed_466_; lean_object* v_res_467_; 
v_t_boxed_466_ = lean_unbox(v_t_463_);
v_res_467_ = l_Std_Http_Method_report_elim(v_motive_462_, v_t_boxed_466_, v_h_464_, v_report_465_);
lean_dec(v_report_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg(lean_object* v_search_468_){
_start:
{
lean_inc(v_search_468_);
return v_search_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg___boxed(lean_object* v_search_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Http_Method_search_elim___redArg(v_search_469_);
lean_dec(v_search_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim(lean_object* v_motive_471_, uint8_t v_t_472_, lean_object* v_h_473_, lean_object* v_search_474_){
_start:
{
lean_inc(v_search_474_);
return v_search_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___boxed(lean_object* v_motive_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_search_478_){
_start:
{
uint8_t v_t_boxed_479_; lean_object* v_res_480_; 
v_t_boxed_479_ = lean_unbox(v_t_476_);
v_res_480_ = l_Std_Http_Method_search_elim(v_motive_475_, v_t_boxed_479_, v_h_477_, v_search_478_);
lean_dec(v_search_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg(lean_object* v_trace_481_){
_start:
{
lean_inc(v_trace_481_);
return v_trace_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg___boxed(lean_object* v_trace_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_Http_Method_trace_elim___redArg(v_trace_482_);
lean_dec(v_trace_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim(lean_object* v_motive_484_, uint8_t v_t_485_, lean_object* v_h_486_, lean_object* v_trace_487_){
_start:
{
lean_inc(v_trace_487_);
return v_trace_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___boxed(lean_object* v_motive_488_, lean_object* v_t_489_, lean_object* v_h_490_, lean_object* v_trace_491_){
_start:
{
uint8_t v_t_boxed_492_; lean_object* v_res_493_; 
v_t_boxed_492_ = lean_unbox(v_t_489_);
v_res_493_ = l_Std_Http_Method_trace_elim(v_motive_488_, v_t_boxed_492_, v_h_490_, v_trace_491_);
lean_dec(v_trace_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg(lean_object* v_unbind_494_){
_start:
{
lean_inc(v_unbind_494_);
return v_unbind_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg___boxed(lean_object* v_unbind_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_Http_Method_unbind_elim___redArg(v_unbind_495_);
lean_dec(v_unbind_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim(lean_object* v_motive_497_, uint8_t v_t_498_, lean_object* v_h_499_, lean_object* v_unbind_500_){
_start:
{
lean_inc(v_unbind_500_);
return v_unbind_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___boxed(lean_object* v_motive_501_, lean_object* v_t_502_, lean_object* v_h_503_, lean_object* v_unbind_504_){
_start:
{
uint8_t v_t_boxed_505_; lean_object* v_res_506_; 
v_t_boxed_505_ = lean_unbox(v_t_502_);
v_res_506_ = l_Std_Http_Method_unbind_elim(v_motive_501_, v_t_boxed_505_, v_h_503_, v_unbind_504_);
lean_dec(v_unbind_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg(lean_object* v_uncheckout_507_){
_start:
{
lean_inc(v_uncheckout_507_);
return v_uncheckout_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg___boxed(lean_object* v_uncheckout_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Http_Method_uncheckout_elim___redArg(v_uncheckout_508_);
lean_dec(v_uncheckout_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim(lean_object* v_motive_510_, uint8_t v_t_511_, lean_object* v_h_512_, lean_object* v_uncheckout_513_){
_start:
{
lean_inc(v_uncheckout_513_);
return v_uncheckout_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___boxed(lean_object* v_motive_514_, lean_object* v_t_515_, lean_object* v_h_516_, lean_object* v_uncheckout_517_){
_start:
{
uint8_t v_t_boxed_518_; lean_object* v_res_519_; 
v_t_boxed_518_ = lean_unbox(v_t_515_);
v_res_519_ = l_Std_Http_Method_uncheckout_elim(v_motive_514_, v_t_boxed_518_, v_h_516_, v_uncheckout_517_);
lean_dec(v_uncheckout_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg(lean_object* v_unlink_520_){
_start:
{
lean_inc(v_unlink_520_);
return v_unlink_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg___boxed(lean_object* v_unlink_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Http_Method_unlink_elim___redArg(v_unlink_521_);
lean_dec(v_unlink_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim(lean_object* v_motive_523_, uint8_t v_t_524_, lean_object* v_h_525_, lean_object* v_unlink_526_){
_start:
{
lean_inc(v_unlink_526_);
return v_unlink_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___boxed(lean_object* v_motive_527_, lean_object* v_t_528_, lean_object* v_h_529_, lean_object* v_unlink_530_){
_start:
{
uint8_t v_t_boxed_531_; lean_object* v_res_532_; 
v_t_boxed_531_ = lean_unbox(v_t_528_);
v_res_532_ = l_Std_Http_Method_unlink_elim(v_motive_527_, v_t_boxed_531_, v_h_529_, v_unlink_530_);
lean_dec(v_unlink_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___redArg(lean_object* v_unlock_533_){
_start:
{
lean_inc(v_unlock_533_);
return v_unlock_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___redArg___boxed(lean_object* v_unlock_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_Http_Method_unlock_elim___redArg(v_unlock_534_);
lean_dec(v_unlock_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim(lean_object* v_motive_536_, uint8_t v_t_537_, lean_object* v_h_538_, lean_object* v_unlock_539_){
_start:
{
lean_inc(v_unlock_539_);
return v_unlock_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___boxed(lean_object* v_motive_540_, lean_object* v_t_541_, lean_object* v_h_542_, lean_object* v_unlock_543_){
_start:
{
uint8_t v_t_boxed_544_; lean_object* v_res_545_; 
v_t_boxed_544_ = lean_unbox(v_t_541_);
v_res_545_ = l_Std_Http_Method_unlock_elim(v_motive_540_, v_t_boxed_544_, v_h_542_, v_unlock_543_);
lean_dec(v_unlock_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg(lean_object* v_update_546_){
_start:
{
lean_inc(v_update_546_);
return v_update_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg___boxed(lean_object* v_update_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Http_Method_update_elim___redArg(v_update_547_);
lean_dec(v_update_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim(lean_object* v_motive_549_, uint8_t v_t_550_, lean_object* v_h_551_, lean_object* v_update_552_){
_start:
{
lean_inc(v_update_552_);
return v_update_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___boxed(lean_object* v_motive_553_, lean_object* v_t_554_, lean_object* v_h_555_, lean_object* v_update_556_){
_start:
{
uint8_t v_t_boxed_557_; lean_object* v_res_558_; 
v_t_boxed_557_ = lean_unbox(v_t_554_);
v_res_558_ = l_Std_Http_Method_update_elim(v_motive_553_, v_t_boxed_557_, v_h_555_, v_update_556_);
lean_dec(v_update_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg(lean_object* v_updateredirectref_559_){
_start:
{
lean_inc(v_updateredirectref_559_);
return v_updateredirectref_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg___boxed(lean_object* v_updateredirectref_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Http_Method_updateredirectref_elim___redArg(v_updateredirectref_560_);
lean_dec(v_updateredirectref_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim(lean_object* v_motive_562_, uint8_t v_t_563_, lean_object* v_h_564_, lean_object* v_updateredirectref_565_){
_start:
{
lean_inc(v_updateredirectref_565_);
return v_updateredirectref_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___boxed(lean_object* v_motive_566_, lean_object* v_t_567_, lean_object* v_h_568_, lean_object* v_updateredirectref_569_){
_start:
{
uint8_t v_t_boxed_570_; lean_object* v_res_571_; 
v_t_boxed_570_ = lean_unbox(v_t_567_);
v_res_571_ = l_Std_Http_Method_updateredirectref_elim(v_motive_566_, v_t_boxed_570_, v_h_568_, v_updateredirectref_569_);
lean_dec(v_updateredirectref_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg(lean_object* v_versionControl_572_){
_start:
{
lean_inc(v_versionControl_572_);
return v_versionControl_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg___boxed(lean_object* v_versionControl_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Http_Method_versionControl_elim___redArg(v_versionControl_573_);
lean_dec(v_versionControl_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim(lean_object* v_motive_575_, uint8_t v_t_576_, lean_object* v_h_577_, lean_object* v_versionControl_578_){
_start:
{
lean_inc(v_versionControl_578_);
return v_versionControl_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___boxed(lean_object* v_motive_579_, lean_object* v_t_580_, lean_object* v_h_581_, lean_object* v_versionControl_582_){
_start:
{
uint8_t v_t_boxed_583_; lean_object* v_res_584_; 
v_t_boxed_583_ = lean_unbox(v_t_580_);
v_res_584_ = l_Std_Http_Method_versionControl_elim(v_motive_579_, v_t_boxed_583_, v_h_581_, v_versionControl_582_);
lean_dec(v_versionControl_582_);
return v_res_584_;
}
}
static lean_object* _init_l_Std_Http_instReprMethod_repr___closed__80(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(2u);
v___x_706_ = lean_nat_to_int(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Std_Http_instReprMethod_repr___closed__81(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_to_int(v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr(uint8_t v_x_709_, lean_object* v_prec_710_){
_start:
{
lean_object* v___y_712_; lean_object* v___y_719_; lean_object* v___y_726_; lean_object* v___y_733_; lean_object* v___y_740_; lean_object* v___y_747_; lean_object* v___y_754_; lean_object* v___y_761_; lean_object* v___y_768_; lean_object* v___y_775_; lean_object* v___y_782_; lean_object* v___y_789_; lean_object* v___y_796_; lean_object* v___y_803_; lean_object* v___y_810_; lean_object* v___y_817_; lean_object* v___y_824_; lean_object* v___y_831_; lean_object* v___y_838_; lean_object* v___y_845_; lean_object* v___y_852_; lean_object* v___y_859_; lean_object* v___y_866_; lean_object* v___y_873_; lean_object* v___y_880_; lean_object* v___y_887_; lean_object* v___y_894_; lean_object* v___y_901_; lean_object* v___y_908_; lean_object* v___y_915_; lean_object* v___y_922_; lean_object* v___y_929_; lean_object* v___y_936_; lean_object* v___y_943_; lean_object* v___y_950_; lean_object* v___y_957_; lean_object* v___y_964_; lean_object* v___y_971_; lean_object* v___y_978_; lean_object* v___y_985_; 
switch(v_x_709_)
{
case 0:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_unsigned_to_nat(1024u);
v___x_992_ = lean_nat_dec_le(v___x_991_, v_prec_710_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_712_ = v___x_993_;
goto v___jp_711_;
}
else
{
lean_object* v___x_994_; 
v___x_994_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_712_ = v___x_994_;
goto v___jp_711_;
}
}
case 1:
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = lean_unsigned_to_nat(1024u);
v___x_996_ = lean_nat_dec_le(v___x_995_, v_prec_710_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
v___x_997_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_719_ = v___x_997_;
goto v___jp_718_;
}
else
{
lean_object* v___x_998_; 
v___x_998_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_719_ = v___x_998_;
goto v___jp_718_;
}
}
case 2:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_unsigned_to_nat(1024u);
v___x_1000_ = lean_nat_dec_le(v___x_999_, v_prec_710_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_726_ = v___x_1001_;
goto v___jp_725_;
}
else
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_726_ = v___x_1002_;
goto v___jp_725_;
}
}
case 3:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = lean_unsigned_to_nat(1024u);
v___x_1004_ = lean_nat_dec_le(v___x_1003_, v_prec_710_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_733_ = v___x_1005_;
goto v___jp_732_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_733_ = v___x_1006_;
goto v___jp_732_;
}
}
case 4:
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = lean_unsigned_to_nat(1024u);
v___x_1008_ = lean_nat_dec_le(v___x_1007_, v_prec_710_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_740_ = v___x_1009_;
goto v___jp_739_;
}
else
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_740_ = v___x_1010_;
goto v___jp_739_;
}
}
case 5:
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = lean_unsigned_to_nat(1024u);
v___x_1012_ = lean_nat_dec_le(v___x_1011_, v_prec_710_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_747_ = v___x_1013_;
goto v___jp_746_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_747_ = v___x_1014_;
goto v___jp_746_;
}
}
case 6:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1024u);
v___x_1016_ = lean_nat_dec_le(v___x_1015_, v_prec_710_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_754_ = v___x_1017_;
goto v___jp_753_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_754_ = v___x_1018_;
goto v___jp_753_;
}
}
case 7:
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = lean_unsigned_to_nat(1024u);
v___x_1020_ = lean_nat_dec_le(v___x_1019_, v_prec_710_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_761_ = v___x_1021_;
goto v___jp_760_;
}
else
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_761_ = v___x_1022_;
goto v___jp_760_;
}
}
case 8:
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(1024u);
v___x_1024_ = lean_nat_dec_le(v___x_1023_, v_prec_710_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_768_ = v___x_1025_;
goto v___jp_767_;
}
else
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_768_ = v___x_1026_;
goto v___jp_767_;
}
}
case 9:
{
lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = lean_unsigned_to_nat(1024u);
v___x_1028_ = lean_nat_dec_le(v___x_1027_, v_prec_710_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_775_ = v___x_1029_;
goto v___jp_774_;
}
else
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_775_ = v___x_1030_;
goto v___jp_774_;
}
}
case 10:
{
lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(1024u);
v___x_1032_ = lean_nat_dec_le(v___x_1031_, v_prec_710_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_782_ = v___x_1033_;
goto v___jp_781_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_782_ = v___x_1034_;
goto v___jp_781_;
}
}
case 11:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1024u);
v___x_1036_ = lean_nat_dec_le(v___x_1035_, v_prec_710_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_789_ = v___x_1037_;
goto v___jp_788_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_789_ = v___x_1038_;
goto v___jp_788_;
}
}
case 12:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(1024u);
v___x_1040_ = lean_nat_dec_le(v___x_1039_, v_prec_710_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_796_ = v___x_1041_;
goto v___jp_795_;
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_796_ = v___x_1042_;
goto v___jp_795_;
}
}
case 13:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = lean_unsigned_to_nat(1024u);
v___x_1044_ = lean_nat_dec_le(v___x_1043_, v_prec_710_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_803_ = v___x_1045_;
goto v___jp_802_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_803_ = v___x_1046_;
goto v___jp_802_;
}
}
case 14:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(1024u);
v___x_1048_ = lean_nat_dec_le(v___x_1047_, v_prec_710_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_810_ = v___x_1049_;
goto v___jp_809_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_810_ = v___x_1050_;
goto v___jp_809_;
}
}
case 15:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(1024u);
v___x_1052_ = lean_nat_dec_le(v___x_1051_, v_prec_710_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_817_ = v___x_1053_;
goto v___jp_816_;
}
else
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_817_ = v___x_1054_;
goto v___jp_816_;
}
}
case 16:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(1024u);
v___x_1056_ = lean_nat_dec_le(v___x_1055_, v_prec_710_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_824_ = v___x_1057_;
goto v___jp_823_;
}
else
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_824_ = v___x_1058_;
goto v___jp_823_;
}
}
case 17:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(1024u);
v___x_1060_ = lean_nat_dec_le(v___x_1059_, v_prec_710_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_831_ = v___x_1061_;
goto v___jp_830_;
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_831_ = v___x_1062_;
goto v___jp_830_;
}
}
case 18:
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(1024u);
v___x_1064_ = lean_nat_dec_le(v___x_1063_, v_prec_710_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_838_ = v___x_1065_;
goto v___jp_837_;
}
else
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_838_ = v___x_1066_;
goto v___jp_837_;
}
}
case 19:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_unsigned_to_nat(1024u);
v___x_1068_ = lean_nat_dec_le(v___x_1067_, v_prec_710_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_845_ = v___x_1069_;
goto v___jp_844_;
}
else
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_845_ = v___x_1070_;
goto v___jp_844_;
}
}
case 20:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(1024u);
v___x_1072_ = lean_nat_dec_le(v___x_1071_, v_prec_710_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_852_ = v___x_1073_;
goto v___jp_851_;
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_852_ = v___x_1074_;
goto v___jp_851_;
}
}
case 21:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_unsigned_to_nat(1024u);
v___x_1076_ = lean_nat_dec_le(v___x_1075_, v_prec_710_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_859_ = v___x_1077_;
goto v___jp_858_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_859_ = v___x_1078_;
goto v___jp_858_;
}
}
case 22:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_unsigned_to_nat(1024u);
v___x_1080_ = lean_nat_dec_le(v___x_1079_, v_prec_710_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_866_ = v___x_1081_;
goto v___jp_865_;
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_866_ = v___x_1082_;
goto v___jp_865_;
}
}
case 23:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_unsigned_to_nat(1024u);
v___x_1084_ = lean_nat_dec_le(v___x_1083_, v_prec_710_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_873_ = v___x_1085_;
goto v___jp_872_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_873_ = v___x_1086_;
goto v___jp_872_;
}
}
case 24:
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(1024u);
v___x_1088_ = lean_nat_dec_le(v___x_1087_, v_prec_710_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_880_ = v___x_1089_;
goto v___jp_879_;
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_880_ = v___x_1090_;
goto v___jp_879_;
}
}
case 25:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = lean_unsigned_to_nat(1024u);
v___x_1092_ = lean_nat_dec_le(v___x_1091_, v_prec_710_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_887_ = v___x_1093_;
goto v___jp_886_;
}
else
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_887_ = v___x_1094_;
goto v___jp_886_;
}
}
case 26:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = lean_unsigned_to_nat(1024u);
v___x_1096_ = lean_nat_dec_le(v___x_1095_, v_prec_710_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_894_ = v___x_1097_;
goto v___jp_893_;
}
else
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_894_ = v___x_1098_;
goto v___jp_893_;
}
}
case 27:
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(1024u);
v___x_1100_ = lean_nat_dec_le(v___x_1099_, v_prec_710_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_901_ = v___x_1101_;
goto v___jp_900_;
}
else
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_901_ = v___x_1102_;
goto v___jp_900_;
}
}
case 28:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1024u);
v___x_1104_ = lean_nat_dec_le(v___x_1103_, v_prec_710_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_908_ = v___x_1105_;
goto v___jp_907_;
}
else
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_908_ = v___x_1106_;
goto v___jp_907_;
}
}
case 29:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_unsigned_to_nat(1024u);
v___x_1108_ = lean_nat_dec_le(v___x_1107_, v_prec_710_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_915_ = v___x_1109_;
goto v___jp_914_;
}
else
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_915_ = v___x_1110_;
goto v___jp_914_;
}
}
case 30:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(1024u);
v___x_1112_ = lean_nat_dec_le(v___x_1111_, v_prec_710_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_922_ = v___x_1113_;
goto v___jp_921_;
}
else
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_922_ = v___x_1114_;
goto v___jp_921_;
}
}
case 31:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_unsigned_to_nat(1024u);
v___x_1116_ = lean_nat_dec_le(v___x_1115_, v_prec_710_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_929_ = v___x_1117_;
goto v___jp_928_;
}
else
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_929_ = v___x_1118_;
goto v___jp_928_;
}
}
case 32:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_unsigned_to_nat(1024u);
v___x_1120_ = lean_nat_dec_le(v___x_1119_, v_prec_710_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_936_ = v___x_1121_;
goto v___jp_935_;
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_936_ = v___x_1122_;
goto v___jp_935_;
}
}
case 33:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_unsigned_to_nat(1024u);
v___x_1124_ = lean_nat_dec_le(v___x_1123_, v_prec_710_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_943_ = v___x_1125_;
goto v___jp_942_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_943_ = v___x_1126_;
goto v___jp_942_;
}
}
case 34:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_unsigned_to_nat(1024u);
v___x_1128_ = lean_nat_dec_le(v___x_1127_, v_prec_710_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_950_ = v___x_1129_;
goto v___jp_949_;
}
else
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_950_ = v___x_1130_;
goto v___jp_949_;
}
}
case 35:
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_unsigned_to_nat(1024u);
v___x_1132_ = lean_nat_dec_le(v___x_1131_, v_prec_710_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_957_ = v___x_1133_;
goto v___jp_956_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_957_ = v___x_1134_;
goto v___jp_956_;
}
}
case 36:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_unsigned_to_nat(1024u);
v___x_1136_ = lean_nat_dec_le(v___x_1135_, v_prec_710_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_964_ = v___x_1137_;
goto v___jp_963_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_964_ = v___x_1138_;
goto v___jp_963_;
}
}
case 37:
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_unsigned_to_nat(1024u);
v___x_1140_ = lean_nat_dec_le(v___x_1139_, v_prec_710_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_971_ = v___x_1141_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_971_ = v___x_1142_;
goto v___jp_970_;
}
}
case 38:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(1024u);
v___x_1144_ = lean_nat_dec_le(v___x_1143_, v_prec_710_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_978_ = v___x_1145_;
goto v___jp_977_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_978_ = v___x_1146_;
goto v___jp_977_;
}
}
default: 
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_unsigned_to_nat(1024u);
v___x_1148_ = lean_nat_dec_le(v___x_1147_, v_prec_710_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_985_ = v___x_1149_;
goto v___jp_984_;
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_985_ = v___x_1150_;
goto v___jp_984_;
}
}
}
v___jp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_713_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__1));
lean_inc(v___y_712_);
v___x_714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_714_, 0, v___y_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = 0;
v___x_716_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*1, v___x_715_);
v___x_717_ = l_Repr_addAppParen(v___x_716_, v_prec_710_);
return v___x_717_;
}
v___jp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_720_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__3));
lean_inc(v___y_719_);
v___x_721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_721_, 0, v___y_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = 0;
v___x_723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*1, v___x_722_);
v___x_724_ = l_Repr_addAppParen(v___x_723_, v_prec_710_);
return v___x_724_;
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_727_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__5));
lean_inc(v___y_726_);
v___x_728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_728_, 0, v___y_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = 0;
v___x_730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*1, v___x_729_);
v___x_731_ = l_Repr_addAppParen(v___x_730_, v_prec_710_);
return v___x_731_;
}
v___jp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_734_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__7));
lean_inc(v___y_733_);
v___x_735_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_735_, 0, v___y_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = 0;
v___x_737_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*1, v___x_736_);
v___x_738_ = l_Repr_addAppParen(v___x_737_, v_prec_710_);
return v___x_738_;
}
v___jp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_741_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__9));
lean_inc(v___y_740_);
v___x_742_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_742_, 0, v___y_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = 0;
v___x_744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*1, v___x_743_);
v___x_745_ = l_Repr_addAppParen(v___x_744_, v_prec_710_);
return v___x_745_;
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_748_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__11));
lean_inc(v___y_747_);
v___x_749_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_749_, 0, v___y_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = 0;
v___x_751_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*1, v___x_750_);
v___x_752_ = l_Repr_addAppParen(v___x_751_, v_prec_710_);
return v___x_752_;
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_755_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__13));
lean_inc(v___y_754_);
v___x_756_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_756_, 0, v___y_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = 0;
v___x_758_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*1, v___x_757_);
v___x_759_ = l_Repr_addAppParen(v___x_758_, v_prec_710_);
return v___x_759_;
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_762_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__15));
lean_inc(v___y_761_);
v___x_763_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_763_, 0, v___y_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = 0;
v___x_765_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set_uint8(v___x_765_, sizeof(void*)*1, v___x_764_);
v___x_766_ = l_Repr_addAppParen(v___x_765_, v_prec_710_);
return v___x_766_;
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_769_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__17));
lean_inc(v___y_768_);
v___x_770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = 0;
v___x_772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1, v___x_771_);
v___x_773_ = l_Repr_addAppParen(v___x_772_, v_prec_710_);
return v___x_773_;
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_776_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__19));
lean_inc(v___y_775_);
v___x_777_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_777_, 0, v___y_775_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = 0;
v___x_779_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*1, v___x_778_);
v___x_780_ = l_Repr_addAppParen(v___x_779_, v_prec_710_);
return v___x_780_;
}
v___jp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_783_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__21));
lean_inc(v___y_782_);
v___x_784_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_784_, 0, v___y_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = 0;
v___x_786_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*1, v___x_785_);
v___x_787_ = l_Repr_addAppParen(v___x_786_, v_prec_710_);
return v___x_787_;
}
v___jp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__23));
lean_inc(v___y_789_);
v___x_791_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_791_, 0, v___y_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = 0;
v___x_793_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*1, v___x_792_);
v___x_794_ = l_Repr_addAppParen(v___x_793_, v_prec_710_);
return v___x_794_;
}
v___jp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_797_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__25));
lean_inc(v___y_796_);
v___x_798_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_798_, 0, v___y_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = 0;
v___x_800_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*1, v___x_799_);
v___x_801_ = l_Repr_addAppParen(v___x_800_, v_prec_710_);
return v___x_801_;
}
v___jp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_804_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__27));
lean_inc(v___y_803_);
v___x_805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_805_, 0, v___y_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = 0;
v___x_807_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*1, v___x_806_);
v___x_808_ = l_Repr_addAppParen(v___x_807_, v_prec_710_);
return v___x_808_;
}
v___jp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_811_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__29));
lean_inc(v___y_810_);
v___x_812_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_812_, 0, v___y_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = 0;
v___x_814_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*1, v___x_813_);
v___x_815_ = l_Repr_addAppParen(v___x_814_, v_prec_710_);
return v___x_815_;
}
v___jp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_818_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__31));
lean_inc(v___y_817_);
v___x_819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_819_, 0, v___y_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = 0;
v___x_821_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*1, v___x_820_);
v___x_822_ = l_Repr_addAppParen(v___x_821_, v_prec_710_);
return v___x_822_;
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_825_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__33));
lean_inc(v___y_824_);
v___x_826_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_826_, 0, v___y_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = 0;
v___x_828_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*1, v___x_827_);
v___x_829_ = l_Repr_addAppParen(v___x_828_, v_prec_710_);
return v___x_829_;
}
v___jp_830_:
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_832_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__35));
lean_inc(v___y_831_);
v___x_833_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_833_, 0, v___y_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = 0;
v___x_835_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*1, v___x_834_);
v___x_836_ = l_Repr_addAppParen(v___x_835_, v_prec_710_);
return v___x_836_;
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_839_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__37));
lean_inc(v___y_838_);
v___x_840_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_840_, 0, v___y_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = 0;
v___x_842_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*1, v___x_841_);
v___x_843_ = l_Repr_addAppParen(v___x_842_, v_prec_710_);
return v___x_843_;
}
v___jp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_846_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__39));
lean_inc(v___y_845_);
v___x_847_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_847_, 0, v___y_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = 0;
v___x_849_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*1, v___x_848_);
v___x_850_ = l_Repr_addAppParen(v___x_849_, v_prec_710_);
return v___x_850_;
}
v___jp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_853_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__41));
lean_inc(v___y_852_);
v___x_854_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_854_, 0, v___y_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = 0;
v___x_856_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_855_);
v___x_857_ = l_Repr_addAppParen(v___x_856_, v_prec_710_);
return v___x_857_;
}
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_860_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__43));
lean_inc(v___y_859_);
v___x_861_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_861_, 0, v___y_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = 0;
v___x_863_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set_uint8(v___x_863_, sizeof(void*)*1, v___x_862_);
v___x_864_ = l_Repr_addAppParen(v___x_863_, v_prec_710_);
return v___x_864_;
}
v___jp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_867_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__45));
lean_inc(v___y_866_);
v___x_868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = 0;
v___x_870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*1, v___x_869_);
v___x_871_ = l_Repr_addAppParen(v___x_870_, v_prec_710_);
return v___x_871_;
}
v___jp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_874_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__47));
lean_inc(v___y_873_);
v___x_875_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_875_, 0, v___y_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = 0;
v___x_877_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*1, v___x_876_);
v___x_878_ = l_Repr_addAppParen(v___x_877_, v_prec_710_);
return v___x_878_;
}
v___jp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_881_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__49));
lean_inc(v___y_880_);
v___x_882_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_882_, 0, v___y_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = 0;
v___x_884_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1, v___x_883_);
v___x_885_ = l_Repr_addAppParen(v___x_884_, v_prec_710_);
return v___x_885_;
}
v___jp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_888_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__51));
lean_inc(v___y_887_);
v___x_889_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_889_, 0, v___y_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = 0;
v___x_891_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set_uint8(v___x_891_, sizeof(void*)*1, v___x_890_);
v___x_892_ = l_Repr_addAppParen(v___x_891_, v_prec_710_);
return v___x_892_;
}
v___jp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_895_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__53));
lean_inc(v___y_894_);
v___x_896_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_896_, 0, v___y_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = 0;
v___x_898_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*1, v___x_897_);
v___x_899_ = l_Repr_addAppParen(v___x_898_, v_prec_710_);
return v___x_899_;
}
v___jp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_902_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__55));
lean_inc(v___y_901_);
v___x_903_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_903_, 0, v___y_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = 0;
v___x_905_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1, v___x_904_);
v___x_906_ = l_Repr_addAppParen(v___x_905_, v_prec_710_);
return v___x_906_;
}
v___jp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_909_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__57));
lean_inc(v___y_908_);
v___x_910_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_910_, 0, v___y_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = 0;
v___x_912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_911_);
v___x_913_ = l_Repr_addAppParen(v___x_912_, v_prec_710_);
return v___x_913_;
}
v___jp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_916_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__59));
lean_inc(v___y_915_);
v___x_917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_917_, 0, v___y_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = 0;
v___x_919_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*1, v___x_918_);
v___x_920_ = l_Repr_addAppParen(v___x_919_, v_prec_710_);
return v___x_920_;
}
v___jp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_923_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__61));
lean_inc(v___y_922_);
v___x_924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_924_, 0, v___y_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = 0;
v___x_926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*1, v___x_925_);
v___x_927_ = l_Repr_addAppParen(v___x_926_, v_prec_710_);
return v___x_927_;
}
v___jp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_930_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__63));
lean_inc(v___y_929_);
v___x_931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_931_, 0, v___y_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = 0;
v___x_933_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*1, v___x_932_);
v___x_934_ = l_Repr_addAppParen(v___x_933_, v_prec_710_);
return v___x_934_;
}
v___jp_935_:
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_937_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__65));
lean_inc(v___y_936_);
v___x_938_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_938_, 0, v___y_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = 0;
v___x_940_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*1, v___x_939_);
v___x_941_ = l_Repr_addAppParen(v___x_940_, v_prec_710_);
return v___x_941_;
}
v___jp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_944_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__67));
lean_inc(v___y_943_);
v___x_945_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_945_, 0, v___y_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = 0;
v___x_947_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*1, v___x_946_);
v___x_948_ = l_Repr_addAppParen(v___x_947_, v_prec_710_);
return v___x_948_;
}
v___jp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_951_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__69));
lean_inc(v___y_950_);
v___x_952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_952_, 0, v___y_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = 0;
v___x_954_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*1, v___x_953_);
v___x_955_ = l_Repr_addAppParen(v___x_954_, v_prec_710_);
return v___x_955_;
}
v___jp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_958_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__71));
lean_inc(v___y_957_);
v___x_959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_959_, 0, v___y_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = 0;
v___x_961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_960_);
v___x_962_ = l_Repr_addAppParen(v___x_961_, v_prec_710_);
return v___x_962_;
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_965_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__73));
lean_inc(v___y_964_);
v___x_966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_966_, 0, v___y_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = 0;
v___x_968_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*1, v___x_967_);
v___x_969_ = l_Repr_addAppParen(v___x_968_, v_prec_710_);
return v___x_969_;
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_972_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__75));
lean_inc(v___y_971_);
v___x_973_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_973_, 0, v___y_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = 0;
v___x_975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_974_);
v___x_976_ = l_Repr_addAppParen(v___x_975_, v_prec_710_);
return v___x_976_;
}
v___jp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_979_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__77));
lean_inc(v___y_978_);
v___x_980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = 0;
v___x_982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*1, v___x_981_);
v___x_983_ = l_Repr_addAppParen(v___x_982_, v_prec_710_);
return v___x_983_;
}
v___jp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_986_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__79));
lean_inc(v___y_985_);
v___x_987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_987_, 0, v___y_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = 0;
v___x_989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_988_);
v___x_990_ = l_Repr_addAppParen(v___x_989_, v_prec_710_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr___boxed(lean_object* v_x_1151_, lean_object* v_prec_1152_){
_start:
{
uint8_t v_x_2249__boxed_1153_; lean_object* v_res_1154_; 
v_x_2249__boxed_1153_ = lean_unbox(v_x_1151_);
v_res_1154_ = l_Std_Http_instReprMethod_repr(v_x_2249__boxed_1153_, v_prec_1152_);
lean_dec(v_prec_1152_);
return v_res_1154_;
}
}
static uint8_t _init_l_Std_Http_instInhabitedMethod_default(void){
_start:
{
uint8_t v___x_1157_; 
v___x_1157_ = 0;
return v___x_1157_;
}
}
static uint8_t _init_l_Std_Http_instInhabitedMethod(void){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = 0;
return v___x_1158_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqMethod_beq(uint8_t v_x_1159_, uint8_t v_y_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1161_ = l_Std_Http_Method_ctorIdx(v_x_1159_);
v___x_1162_ = l_Std_Http_Method_ctorIdx(v_y_1160_);
v___x_1163_ = lean_nat_dec_eq(v___x_1161_, v___x_1162_);
lean_dec(v___x_1162_);
lean_dec(v___x_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqMethod_beq___boxed(lean_object* v_x_1164_, lean_object* v_y_1165_){
_start:
{
uint8_t v_x_17__boxed_1166_; uint8_t v_y_18__boxed_1167_; uint8_t v_res_1168_; lean_object* v_r_1169_; 
v_x_17__boxed_1166_ = lean_unbox(v_x_1164_);
v_y_18__boxed_1167_ = lean_unbox(v_y_1165_);
v_res_1168_ = l_Std_Http_instBEqMethod_beq(v_x_17__boxed_1166_, v_y_18__boxed_1167_);
v_r_1169_ = lean_box(v_res_1168_);
return v_r_1169_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_ofNat(lean_object* v_n_1172_){
_start:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(19u);
v___x_1174_ = lean_nat_dec_le(v_n_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(29u);
v___x_1176_ = lean_nat_dec_le(v_n_1172_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(34u);
v___x_1178_ = lean_nat_dec_le(v_n_1172_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_unsigned_to_nat(36u);
v___x_1180_ = lean_nat_dec_le(v_n_1172_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_unsigned_to_nat(37u);
v___x_1182_ = lean_nat_dec_le(v_n_1172_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(38u);
v___x_1184_ = lean_nat_dec_le(v_n_1172_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint8_t v___x_1185_; 
v___x_1185_ = 39;
return v___x_1185_;
}
else
{
uint8_t v___x_1186_; 
v___x_1186_ = 38;
return v___x_1186_;
}
}
else
{
uint8_t v___x_1187_; 
v___x_1187_ = 37;
return v___x_1187_;
}
}
else
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(35u);
v___x_1189_ = lean_nat_dec_le(v_n_1172_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = 36;
return v___x_1190_;
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = 35;
return v___x_1191_;
}
}
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_unsigned_to_nat(31u);
v___x_1193_ = lean_nat_dec_le(v_n_1172_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(32u);
v___x_1195_ = lean_nat_dec_le(v_n_1172_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(33u);
v___x_1197_ = lean_nat_dec_le(v_n_1172_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; 
v___x_1198_ = 34;
return v___x_1198_;
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = 33;
return v___x_1199_;
}
}
else
{
uint8_t v___x_1200_; 
v___x_1200_ = 32;
return v___x_1200_;
}
}
else
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = lean_unsigned_to_nat(30u);
v___x_1202_ = lean_nat_dec_le(v_n_1172_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; 
v___x_1203_ = 31;
return v___x_1203_;
}
else
{
uint8_t v___x_1204_; 
v___x_1204_ = 30;
return v___x_1204_;
}
}
}
}
else
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(24u);
v___x_1206_ = lean_nat_dec_le(v_n_1172_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_unsigned_to_nat(26u);
v___x_1208_ = lean_nat_dec_le(v_n_1172_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(27u);
v___x_1210_ = lean_nat_dec_le(v_n_1172_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(28u);
v___x_1212_ = lean_nat_dec_le(v_n_1172_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint8_t v___x_1213_; 
v___x_1213_ = 29;
return v___x_1213_;
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = 28;
return v___x_1214_;
}
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = 27;
return v___x_1215_;
}
}
else
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_unsigned_to_nat(25u);
v___x_1217_ = lean_nat_dec_le(v_n_1172_, v___x_1216_);
if (v___x_1217_ == 0)
{
uint8_t v___x_1218_; 
v___x_1218_ = 26;
return v___x_1218_;
}
else
{
uint8_t v___x_1219_; 
v___x_1219_ = 25;
return v___x_1219_;
}
}
}
else
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(21u);
v___x_1221_ = lean_nat_dec_le(v_n_1172_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_unsigned_to_nat(22u);
v___x_1223_ = lean_nat_dec_le(v_n_1172_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_unsigned_to_nat(23u);
v___x_1225_ = lean_nat_dec_le(v_n_1172_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = 24;
return v___x_1226_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = 23;
return v___x_1227_;
}
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = 22;
return v___x_1228_;
}
}
else
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_unsigned_to_nat(20u);
v___x_1230_ = lean_nat_dec_le(v_n_1172_, v___x_1229_);
if (v___x_1230_ == 0)
{
uint8_t v___x_1231_; 
v___x_1231_ = 21;
return v___x_1231_;
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = 20;
return v___x_1232_;
}
}
}
}
}
else
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(9u);
v___x_1234_ = lean_nat_dec_le(v_n_1172_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(14u);
v___x_1236_ = lean_nat_dec_le(v_n_1172_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(16u);
v___x_1238_ = lean_nat_dec_le(v_n_1172_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_unsigned_to_nat(17u);
v___x_1240_ = lean_nat_dec_le(v_n_1172_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_unsigned_to_nat(18u);
v___x_1242_ = lean_nat_dec_le(v_n_1172_, v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = 19;
return v___x_1243_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = 18;
return v___x_1244_;
}
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = 17;
return v___x_1245_;
}
}
else
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(15u);
v___x_1247_ = lean_nat_dec_le(v_n_1172_, v___x_1246_);
if (v___x_1247_ == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = 16;
return v___x_1248_;
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = 15;
return v___x_1249_;
}
}
}
else
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_unsigned_to_nat(11u);
v___x_1251_ = lean_nat_dec_le(v_n_1172_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_unsigned_to_nat(12u);
v___x_1253_ = lean_nat_dec_le(v_n_1172_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(13u);
v___x_1255_ = lean_nat_dec_le(v_n_1172_, v___x_1254_);
if (v___x_1255_ == 0)
{
uint8_t v___x_1256_; 
v___x_1256_ = 14;
return v___x_1256_;
}
else
{
uint8_t v___x_1257_; 
v___x_1257_ = 13;
return v___x_1257_;
}
}
else
{
uint8_t v___x_1258_; 
v___x_1258_ = 12;
return v___x_1258_;
}
}
else
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = lean_unsigned_to_nat(10u);
v___x_1260_ = lean_nat_dec_le(v_n_1172_, v___x_1259_);
if (v___x_1260_ == 0)
{
uint8_t v___x_1261_; 
v___x_1261_ = 11;
return v___x_1261_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = 10;
return v___x_1262_;
}
}
}
}
else
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(4u);
v___x_1264_ = lean_nat_dec_le(v_n_1172_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = lean_unsigned_to_nat(6u);
v___x_1266_ = lean_nat_dec_le(v_n_1172_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = lean_unsigned_to_nat(7u);
v___x_1268_ = lean_nat_dec_le(v_n_1172_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_unsigned_to_nat(8u);
v___x_1270_ = lean_nat_dec_le(v_n_1172_, v___x_1269_);
if (v___x_1270_ == 0)
{
uint8_t v___x_1271_; 
v___x_1271_ = 9;
return v___x_1271_;
}
else
{
uint8_t v___x_1272_; 
v___x_1272_ = 8;
return v___x_1272_;
}
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = 7;
return v___x_1273_;
}
}
else
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = lean_unsigned_to_nat(5u);
v___x_1275_ = lean_nat_dec_le(v_n_1172_, v___x_1274_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; 
v___x_1276_ = 6;
return v___x_1276_;
}
else
{
uint8_t v___x_1277_; 
v___x_1277_ = 5;
return v___x_1277_;
}
}
}
else
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_dec_le(v_n_1172_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = lean_unsigned_to_nat(2u);
v___x_1281_ = lean_nat_dec_le(v_n_1172_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(3u);
v___x_1283_ = lean_nat_dec_le(v_n_1172_, v___x_1282_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; 
v___x_1284_ = 4;
return v___x_1284_;
}
else
{
uint8_t v___x_1285_; 
v___x_1285_ = 3;
return v___x_1285_;
}
}
else
{
uint8_t v___x_1286_; 
v___x_1286_ = 2;
return v___x_1286_;
}
}
else
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_nat_dec_le(v_n_1172_, v___x_1287_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = 1;
return v___x_1289_;
}
else
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
return v___x_1290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofNat___boxed(lean_object* v_n_1291_){
_start:
{
uint8_t v_res_1292_; lean_object* v_r_1293_; 
v_res_1292_ = l_Std_Http_Method_ofNat(v_n_1291_);
lean_dec(v_n_1291_);
v_r_1293_ = lean_box(v_res_1292_);
return v_r_1293_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instDecidableEqMethod(uint8_t v_x_1294_, uint8_t v_y_1295_){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = l_Std_Http_Method_ctorIdx(v_x_1294_);
v___x_1297_ = l_Std_Http_Method_ctorIdx(v_y_1295_);
v___x_1298_ = lean_nat_dec_eq(v___x_1296_, v___x_1297_);
lean_dec(v___x_1297_);
lean_dec(v___x_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableEqMethod___boxed(lean_object* v_x_1299_, lean_object* v_y_1300_){
_start:
{
uint8_t v_x_13__boxed_1301_; uint8_t v_y_14__boxed_1302_; uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_x_13__boxed_1301_ = lean_unbox(v_x_1299_);
v_y_14__boxed_1302_ = lean_unbox(v_y_1300_);
v_res_1303_ = l_Std_Http_instDecidableEqMethod(v_x_13__boxed_1301_, v_y_14__boxed_1302_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f(lean_object* v_x_1465_){
_start:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
v___x_1467_ = lean_string_dec_eq(v_x_1465_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
v___x_1469_ = lean_string_dec_eq(v_x_1465_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
v___x_1471_ = lean_string_dec_eq(v_x_1465_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
v___x_1473_ = lean_string_dec_eq(v_x_1465_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
v___x_1475_ = lean_string_dec_eq(v_x_1465_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
v___x_1477_ = lean_string_dec_eq(v_x_1465_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
v___x_1479_ = lean_string_dec_eq(v_x_1465_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
v___x_1481_ = lean_string_dec_eq(v_x_1465_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
v___x_1483_ = lean_string_dec_eq(v_x_1465_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
v___x_1485_ = lean_string_dec_eq(v_x_1465_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
v___x_1487_ = lean_string_dec_eq(v_x_1465_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
v___x_1489_ = lean_string_dec_eq(v_x_1465_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
v___x_1491_ = lean_string_dec_eq(v_x_1465_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
v___x_1493_ = lean_string_dec_eq(v_x_1465_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
v___x_1495_ = lean_string_dec_eq(v_x_1465_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
v___x_1497_ = lean_string_dec_eq(v_x_1465_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
v___x_1499_ = lean_string_dec_eq(v_x_1465_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
v___x_1501_ = lean_string_dec_eq(v_x_1465_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
v___x_1503_ = lean_string_dec_eq(v_x_1465_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
v___x_1505_ = lean_string_dec_eq(v_x_1465_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
v___x_1507_ = lean_string_dec_eq(v_x_1465_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
v___x_1509_ = lean_string_dec_eq(v_x_1465_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
v___x_1511_ = lean_string_dec_eq(v_x_1465_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
v___x_1513_ = lean_string_dec_eq(v_x_1465_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
v___x_1515_ = lean_string_dec_eq(v_x_1465_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
v___x_1517_ = lean_string_dec_eq(v_x_1465_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
v___x_1519_ = lean_string_dec_eq(v_x_1465_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
v___x_1521_ = lean_string_dec_eq(v_x_1465_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
v___x_1523_ = lean_string_dec_eq(v_x_1465_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
v___x_1525_ = lean_string_dec_eq(v_x_1465_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
v___x_1527_ = lean_string_dec_eq(v_x_1465_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
v___x_1529_ = lean_string_dec_eq(v_x_1465_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
v___x_1531_ = lean_string_dec_eq(v_x_1465_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
v___x_1533_ = lean_string_dec_eq(v_x_1465_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
v___x_1535_ = lean_string_dec_eq(v_x_1465_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
v___x_1537_ = lean_string_dec_eq(v_x_1465_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
v___x_1539_ = lean_string_dec_eq(v_x_1465_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
v___x_1541_ = lean_string_dec_eq(v_x_1465_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
v___x_1543_ = lean_string_dec_eq(v_x_1465_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
v___x_1545_ = lean_string_dec_eq(v_x_1465_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_box(0);
return v___x_1546_;
}
else
{
lean_object* v___x_1547_; 
v___x_1547_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__40));
return v___x_1547_;
}
}
else
{
lean_object* v___x_1548_; 
v___x_1548_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__41));
return v___x_1548_;
}
}
else
{
lean_object* v___x_1549_; 
v___x_1549_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__42));
return v___x_1549_;
}
}
else
{
lean_object* v___x_1550_; 
v___x_1550_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__43));
return v___x_1550_;
}
}
else
{
lean_object* v___x_1551_; 
v___x_1551_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__44));
return v___x_1551_;
}
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__45));
return v___x_1552_;
}
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__46));
return v___x_1553_;
}
}
else
{
lean_object* v___x_1554_; 
v___x_1554_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__47));
return v___x_1554_;
}
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__48));
return v___x_1555_;
}
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__49));
return v___x_1556_;
}
}
else
{
lean_object* v___x_1557_; 
v___x_1557_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__50));
return v___x_1557_;
}
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__51));
return v___x_1558_;
}
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__52));
return v___x_1559_;
}
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__53));
return v___x_1560_;
}
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__54));
return v___x_1561_;
}
}
else
{
lean_object* v___x_1562_; 
v___x_1562_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__55));
return v___x_1562_;
}
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__56));
return v___x_1563_;
}
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__57));
return v___x_1564_;
}
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__58));
return v___x_1565_;
}
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__59));
return v___x_1566_;
}
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__60));
return v___x_1567_;
}
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__61));
return v___x_1568_;
}
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__62));
return v___x_1569_;
}
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__63));
return v___x_1570_;
}
}
else
{
lean_object* v___x_1571_; 
v___x_1571_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__64));
return v___x_1571_;
}
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__65));
return v___x_1572_;
}
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__66));
return v___x_1573_;
}
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__67));
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__68));
return v___x_1575_;
}
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__69));
return v___x_1576_;
}
}
else
{
lean_object* v___x_1577_; 
v___x_1577_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__70));
return v___x_1577_;
}
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__71));
return v___x_1578_;
}
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__72));
return v___x_1579_;
}
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__73));
return v___x_1580_;
}
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__74));
return v___x_1581_;
}
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__75));
return v___x_1582_;
}
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__76));
return v___x_1583_;
}
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__77));
return v___x_1584_;
}
}
else
{
lean_object* v___x_1585_; 
v___x_1585_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__78));
return v___x_1585_;
}
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__79));
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f___boxed(lean_object* v_x_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Std_Http_Method_ofString_x3f(v_x_1587_);
lean_dec_ref(v_x_1587_);
return v_res_1588_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Std_Http_Method_ofString_x21_spec__0(lean_object* v_msg_1589_){
_start:
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1590_ = 0;
v___x_1591_ = lean_box(v___x_1590_);
v___x_1592_ = lean_panic_fn_borrowed(v___x_1591_, v_msg_1589_);
lean_dec(v___x_1591_);
v___x_1593_ = lean_unbox(v___x_1592_);
lean_dec(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Method_ofString_x21_spec__0___boxed(lean_object* v_msg_1594_){
_start:
{
uint8_t v_res_1595_; lean_object* v_r_1596_; 
v_res_1595_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v_msg_1594_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_ofString_x21(lean_object* v_s_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Std_Http_Method_ofString_x3f(v_s_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1602_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__0));
v___x_1603_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__1));
v___x_1604_ = lean_unsigned_to_nat(337u);
v___x_1605_ = lean_unsigned_to_nat(12u);
v___x_1606_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__2));
v___x_1607_ = l_String_quote(v_s_1600_);
v___x_1608_ = lean_string_append(v___x_1606_, v___x_1607_);
lean_dec_ref(v___x_1607_);
v___x_1609_ = l_mkPanicMessageWithDecl(v___x_1602_, v___x_1603_, v___x_1604_, v___x_1605_, v___x_1608_);
lean_dec_ref(v___x_1608_);
v___x_1610_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v___x_1609_);
return v___x_1610_;
}
else
{
lean_object* v_val_1611_; uint8_t v___x_1612_; 
lean_dec_ref(v_s_1600_);
v_val_1611_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_val_1611_);
lean_dec_ref(v___x_1601_);
v___x_1612_ = lean_unbox(v_val_1611_);
lean_dec(v_val_1611_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x21___boxed(lean_object* v_s_1613_){
_start:
{
uint8_t v_res_1614_; lean_object* v_r_1615_; 
v_res_1614_ = l_Std_Http_Method_ofString_x21(v_s_1613_);
v_r_1615_ = lean_box(v_res_1614_);
return v_r_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0(uint8_t v_x_1616_){
_start:
{
switch(v_x_1616_)
{
case 0:
{
lean_object* v___x_1617_; 
v___x_1617_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
return v___x_1617_;
}
case 1:
{
lean_object* v___x_1618_; 
v___x_1618_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
return v___x_1618_;
}
case 2:
{
lean_object* v___x_1619_; 
v___x_1619_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
return v___x_1619_;
}
case 3:
{
lean_object* v___x_1620_; 
v___x_1620_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
return v___x_1620_;
}
case 4:
{
lean_object* v___x_1621_; 
v___x_1621_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
return v___x_1621_;
}
case 5:
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
return v___x_1622_;
}
case 6:
{
lean_object* v___x_1623_; 
v___x_1623_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
return v___x_1623_;
}
case 7:
{
lean_object* v___x_1624_; 
v___x_1624_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
return v___x_1624_;
}
case 8:
{
lean_object* v___x_1625_; 
v___x_1625_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
return v___x_1625_;
}
case 9:
{
lean_object* v___x_1626_; 
v___x_1626_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
return v___x_1626_;
}
case 10:
{
lean_object* v___x_1627_; 
v___x_1627_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
return v___x_1627_;
}
case 11:
{
lean_object* v___x_1628_; 
v___x_1628_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
return v___x_1628_;
}
case 12:
{
lean_object* v___x_1629_; 
v___x_1629_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
return v___x_1629_;
}
case 13:
{
lean_object* v___x_1630_; 
v___x_1630_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
return v___x_1630_;
}
case 14:
{
lean_object* v___x_1631_; 
v___x_1631_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
return v___x_1631_;
}
case 15:
{
lean_object* v___x_1632_; 
v___x_1632_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
return v___x_1632_;
}
case 16:
{
lean_object* v___x_1633_; 
v___x_1633_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
return v___x_1633_;
}
case 17:
{
lean_object* v___x_1634_; 
v___x_1634_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
return v___x_1634_;
}
case 18:
{
lean_object* v___x_1635_; 
v___x_1635_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
return v___x_1635_;
}
case 19:
{
lean_object* v___x_1636_; 
v___x_1636_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
return v___x_1636_;
}
case 20:
{
lean_object* v___x_1637_; 
v___x_1637_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
return v___x_1637_;
}
case 21:
{
lean_object* v___x_1638_; 
v___x_1638_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
return v___x_1638_;
}
case 22:
{
lean_object* v___x_1639_; 
v___x_1639_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
return v___x_1639_;
}
case 23:
{
lean_object* v___x_1640_; 
v___x_1640_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
return v___x_1640_;
}
case 24:
{
lean_object* v___x_1641_; 
v___x_1641_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
return v___x_1641_;
}
case 25:
{
lean_object* v___x_1642_; 
v___x_1642_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
return v___x_1642_;
}
case 26:
{
lean_object* v___x_1643_; 
v___x_1643_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
return v___x_1643_;
}
case 27:
{
lean_object* v___x_1644_; 
v___x_1644_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
return v___x_1644_;
}
case 28:
{
lean_object* v___x_1645_; 
v___x_1645_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
return v___x_1645_;
}
case 29:
{
lean_object* v___x_1646_; 
v___x_1646_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
return v___x_1646_;
}
case 30:
{
lean_object* v___x_1647_; 
v___x_1647_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
return v___x_1647_;
}
case 31:
{
lean_object* v___x_1648_; 
v___x_1648_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
return v___x_1648_;
}
case 32:
{
lean_object* v___x_1649_; 
v___x_1649_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
return v___x_1649_;
}
case 33:
{
lean_object* v___x_1650_; 
v___x_1650_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
return v___x_1650_;
}
case 34:
{
lean_object* v___x_1651_; 
v___x_1651_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
return v___x_1651_;
}
case 35:
{
lean_object* v___x_1652_; 
v___x_1652_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
return v___x_1652_;
}
case 36:
{
lean_object* v___x_1653_; 
v___x_1653_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
return v___x_1653_;
}
case 37:
{
lean_object* v___x_1654_; 
v___x_1654_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
return v___x_1654_;
}
case 38:
{
lean_object* v___x_1655_; 
v___x_1655_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
return v___x_1655_;
}
default: 
{
lean_object* v___x_1656_; 
v___x_1656_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0___boxed(lean_object* v_x_1657_){
_start:
{
uint8_t v_x_366__boxed_1658_; lean_object* v_res_1659_; 
v_x_366__boxed_1658_ = lean_unbox(v_x_1657_);
v_res_1659_ = l_Std_Http_Method_instToString___lam__0(v_x_366__boxed_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0(lean_object* v_buffer_1662_, uint8_t v___y_1663_){
_start:
{
lean_object* v___y_1665_; 
switch(v___y_1663_)
{
case 0:
{
lean_object* v___x_1679_; 
v___x_1679_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
v___y_1665_ = v___x_1679_;
goto v___jp_1664_;
}
case 1:
{
lean_object* v___x_1680_; 
v___x_1680_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
v___y_1665_ = v___x_1680_;
goto v___jp_1664_;
}
case 2:
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
v___y_1665_ = v___x_1681_;
goto v___jp_1664_;
}
case 3:
{
lean_object* v___x_1682_; 
v___x_1682_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
v___y_1665_ = v___x_1682_;
goto v___jp_1664_;
}
case 4:
{
lean_object* v___x_1683_; 
v___x_1683_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
v___y_1665_ = v___x_1683_;
goto v___jp_1664_;
}
case 5:
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
v___y_1665_ = v___x_1684_;
goto v___jp_1664_;
}
case 6:
{
lean_object* v___x_1685_; 
v___x_1685_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
v___y_1665_ = v___x_1685_;
goto v___jp_1664_;
}
case 7:
{
lean_object* v___x_1686_; 
v___x_1686_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
v___y_1665_ = v___x_1686_;
goto v___jp_1664_;
}
case 8:
{
lean_object* v___x_1687_; 
v___x_1687_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
v___y_1665_ = v___x_1687_;
goto v___jp_1664_;
}
case 9:
{
lean_object* v___x_1688_; 
v___x_1688_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
v___y_1665_ = v___x_1688_;
goto v___jp_1664_;
}
case 10:
{
lean_object* v___x_1689_; 
v___x_1689_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
v___y_1665_ = v___x_1689_;
goto v___jp_1664_;
}
case 11:
{
lean_object* v___x_1690_; 
v___x_1690_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
v___y_1665_ = v___x_1690_;
goto v___jp_1664_;
}
case 12:
{
lean_object* v___x_1691_; 
v___x_1691_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
v___y_1665_ = v___x_1691_;
goto v___jp_1664_;
}
case 13:
{
lean_object* v___x_1692_; 
v___x_1692_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
v___y_1665_ = v___x_1692_;
goto v___jp_1664_;
}
case 14:
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
v___y_1665_ = v___x_1693_;
goto v___jp_1664_;
}
case 15:
{
lean_object* v___x_1694_; 
v___x_1694_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
v___y_1665_ = v___x_1694_;
goto v___jp_1664_;
}
case 16:
{
lean_object* v___x_1695_; 
v___x_1695_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
v___y_1665_ = v___x_1695_;
goto v___jp_1664_;
}
case 17:
{
lean_object* v___x_1696_; 
v___x_1696_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
v___y_1665_ = v___x_1696_;
goto v___jp_1664_;
}
case 18:
{
lean_object* v___x_1697_; 
v___x_1697_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
v___y_1665_ = v___x_1697_;
goto v___jp_1664_;
}
case 19:
{
lean_object* v___x_1698_; 
v___x_1698_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
v___y_1665_ = v___x_1698_;
goto v___jp_1664_;
}
case 20:
{
lean_object* v___x_1699_; 
v___x_1699_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
v___y_1665_ = v___x_1699_;
goto v___jp_1664_;
}
case 21:
{
lean_object* v___x_1700_; 
v___x_1700_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
v___y_1665_ = v___x_1700_;
goto v___jp_1664_;
}
case 22:
{
lean_object* v___x_1701_; 
v___x_1701_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
v___y_1665_ = v___x_1701_;
goto v___jp_1664_;
}
case 23:
{
lean_object* v___x_1702_; 
v___x_1702_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
v___y_1665_ = v___x_1702_;
goto v___jp_1664_;
}
case 24:
{
lean_object* v___x_1703_; 
v___x_1703_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
v___y_1665_ = v___x_1703_;
goto v___jp_1664_;
}
case 25:
{
lean_object* v___x_1704_; 
v___x_1704_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
v___y_1665_ = v___x_1704_;
goto v___jp_1664_;
}
case 26:
{
lean_object* v___x_1705_; 
v___x_1705_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
v___y_1665_ = v___x_1705_;
goto v___jp_1664_;
}
case 27:
{
lean_object* v___x_1706_; 
v___x_1706_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
v___y_1665_ = v___x_1706_;
goto v___jp_1664_;
}
case 28:
{
lean_object* v___x_1707_; 
v___x_1707_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
v___y_1665_ = v___x_1707_;
goto v___jp_1664_;
}
case 29:
{
lean_object* v___x_1708_; 
v___x_1708_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
v___y_1665_ = v___x_1708_;
goto v___jp_1664_;
}
case 30:
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
v___y_1665_ = v___x_1709_;
goto v___jp_1664_;
}
case 31:
{
lean_object* v___x_1710_; 
v___x_1710_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
v___y_1665_ = v___x_1710_;
goto v___jp_1664_;
}
case 32:
{
lean_object* v___x_1711_; 
v___x_1711_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
v___y_1665_ = v___x_1711_;
goto v___jp_1664_;
}
case 33:
{
lean_object* v___x_1712_; 
v___x_1712_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
v___y_1665_ = v___x_1712_;
goto v___jp_1664_;
}
case 34:
{
lean_object* v___x_1713_; 
v___x_1713_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
v___y_1665_ = v___x_1713_;
goto v___jp_1664_;
}
case 35:
{
lean_object* v___x_1714_; 
v___x_1714_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
v___y_1665_ = v___x_1714_;
goto v___jp_1664_;
}
case 36:
{
lean_object* v___x_1715_; 
v___x_1715_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
v___y_1665_ = v___x_1715_;
goto v___jp_1664_;
}
case 37:
{
lean_object* v___x_1716_; 
v___x_1716_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
v___y_1665_ = v___x_1716_;
goto v___jp_1664_;
}
case 38:
{
lean_object* v___x_1717_; 
v___x_1717_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
v___y_1665_ = v___x_1717_;
goto v___jp_1664_;
}
default: 
{
lean_object* v___x_1718_; 
v___x_1718_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
v___y_1665_ = v___x_1718_;
goto v___jp_1664_;
}
}
v___jp_1664_:
{
lean_object* v_data_1666_; lean_object* v_size_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1678_; 
v_data_1666_ = lean_ctor_get(v_buffer_1662_, 0);
v_size_1667_ = lean_ctor_get(v_buffer_1662_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_buffer_1662_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1669_ = v_buffer_1662_;
v_isShared_1670_ = v_isSharedCheck_1678_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_size_1667_);
lean_inc(v_data_1666_);
lean_dec(v_buffer_1662_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1678_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1671_ = lean_string_to_utf8(v___y_1665_);
lean_inc_ref(v___x_1671_);
v___x_1672_ = lean_array_push(v_data_1666_, v___x_1671_);
v___x_1673_ = lean_byte_array_size(v___x_1671_);
lean_dec_ref(v___x_1671_);
v___x_1674_ = lean_nat_add(v_size_1667_, v___x_1673_);
lean_dec(v_size_1667_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 1, v___x_1674_);
lean_ctor_set(v___x_1669_, 0, v___x_1672_);
v___x_1676_ = v___x_1669_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0___boxed(lean_object* v_buffer_1719_, lean_object* v___y_1720_){
_start:
{
uint8_t v___y_192__boxed_1721_; lean_object* v_res_1722_; 
v___y_192__boxed_1721_ = lean_unbox(v___y_1720_);
v_res_1722_ = l_Std_Http_Method_instEncodeV11___lam__0(v_buffer_1719_, v___y_192__boxed_1721_);
return v_res_1722_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Method(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_instInhabitedMethod_default = _init_l_Std_Http_instInhabitedMethod_default();
l_Std_Http_instInhabitedMethod = _init_l_Std_Http_instInhabitedMethod();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Method(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Method(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Method(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Method(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Method(builtin);
}
#ifdef __cplusplus
}
#endif
