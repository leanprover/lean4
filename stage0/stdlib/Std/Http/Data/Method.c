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
LEAN_EXPORT uint8_t l_Std_Http_Method_isIdempotent(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Method_isIdempotent___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Method_isSafe(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Method_isSafe___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg(lean_object* v_k_45_){
_start:
{
lean_inc(v_k_45_);
return v_k_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg___boxed(lean_object* v_k_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_Http_Method_ctorElim___redArg(v_k_46_);
lean_dec(v_k_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim(lean_object* v_motive_48_, lean_object* v_ctorIdx_49_, uint8_t v_t_50_, lean_object* v_h_51_, lean_object* v_k_52_){
_start:
{
lean_inc(v_k_52_);
return v_k_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___boxed(lean_object* v_motive_53_, lean_object* v_ctorIdx_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_k_57_){
_start:
{
uint8_t v_t_boxed_58_; lean_object* v_res_59_; 
v_t_boxed_58_ = lean_unbox(v_t_55_);
v_res_59_ = l_Std_Http_Method_ctorElim(v_motive_53_, v_ctorIdx_54_, v_t_boxed_58_, v_h_56_, v_k_57_);
lean_dec(v_k_57_);
lean_dec(v_ctorIdx_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg(lean_object* v_acl_60_){
_start:
{
lean_inc(v_acl_60_);
return v_acl_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg___boxed(lean_object* v_acl_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_Http_Method_acl_elim___redArg(v_acl_61_);
lean_dec(v_acl_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_acl_66_){
_start:
{
lean_inc(v_acl_66_);
return v_acl_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___boxed(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_acl_70_){
_start:
{
uint8_t v_t_boxed_71_; lean_object* v_res_72_; 
v_t_boxed_71_ = lean_unbox(v_t_68_);
v_res_72_ = l_Std_Http_Method_acl_elim(v_motive_67_, v_t_boxed_71_, v_h_69_, v_acl_70_);
lean_dec(v_acl_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg(lean_object* v_baselineControl_73_){
_start:
{
lean_inc(v_baselineControl_73_);
return v_baselineControl_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg___boxed(lean_object* v_baselineControl_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Http_Method_baselineControl_elim___redArg(v_baselineControl_74_);
lean_dec(v_baselineControl_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim(lean_object* v_motive_76_, uint8_t v_t_77_, lean_object* v_h_78_, lean_object* v_baselineControl_79_){
_start:
{
lean_inc(v_baselineControl_79_);
return v_baselineControl_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___boxed(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_baselineControl_83_){
_start:
{
uint8_t v_t_boxed_84_; lean_object* v_res_85_; 
v_t_boxed_84_ = lean_unbox(v_t_81_);
v_res_85_ = l_Std_Http_Method_baselineControl_elim(v_motive_80_, v_t_boxed_84_, v_h_82_, v_baselineControl_83_);
lean_dec(v_baselineControl_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg(lean_object* v_bind_86_){
_start:
{
lean_inc(v_bind_86_);
return v_bind_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg___boxed(lean_object* v_bind_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Http_Method_bind_elim___redArg(v_bind_87_);
lean_dec(v_bind_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim(lean_object* v_motive_89_, uint8_t v_t_90_, lean_object* v_h_91_, lean_object* v_bind_92_){
_start:
{
lean_inc(v_bind_92_);
return v_bind_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___boxed(lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_bind_96_){
_start:
{
uint8_t v_t_boxed_97_; lean_object* v_res_98_; 
v_t_boxed_97_ = lean_unbox(v_t_94_);
v_res_98_ = l_Std_Http_Method_bind_elim(v_motive_93_, v_t_boxed_97_, v_h_95_, v_bind_96_);
lean_dec(v_bind_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg(lean_object* v_checkin_99_){
_start:
{
lean_inc(v_checkin_99_);
return v_checkin_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg___boxed(lean_object* v_checkin_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Std_Http_Method_checkin_elim___redArg(v_checkin_100_);
lean_dec(v_checkin_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim(lean_object* v_motive_102_, uint8_t v_t_103_, lean_object* v_h_104_, lean_object* v_checkin_105_){
_start:
{
lean_inc(v_checkin_105_);
return v_checkin_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___boxed(lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_checkin_109_){
_start:
{
uint8_t v_t_boxed_110_; lean_object* v_res_111_; 
v_t_boxed_110_ = lean_unbox(v_t_107_);
v_res_111_ = l_Std_Http_Method_checkin_elim(v_motive_106_, v_t_boxed_110_, v_h_108_, v_checkin_109_);
lean_dec(v_checkin_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg(lean_object* v_checkout_112_){
_start:
{
lean_inc(v_checkout_112_);
return v_checkout_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg___boxed(lean_object* v_checkout_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_Http_Method_checkout_elim___redArg(v_checkout_113_);
lean_dec(v_checkout_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim(lean_object* v_motive_115_, uint8_t v_t_116_, lean_object* v_h_117_, lean_object* v_checkout_118_){
_start:
{
lean_inc(v_checkout_118_);
return v_checkout_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___boxed(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_checkout_122_){
_start:
{
uint8_t v_t_boxed_123_; lean_object* v_res_124_; 
v_t_boxed_123_ = lean_unbox(v_t_120_);
v_res_124_ = l_Std_Http_Method_checkout_elim(v_motive_119_, v_t_boxed_123_, v_h_121_, v_checkout_122_);
lean_dec(v_checkout_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg(lean_object* v_connect_125_){
_start:
{
lean_inc(v_connect_125_);
return v_connect_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg___boxed(lean_object* v_connect_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Http_Method_connect_elim___redArg(v_connect_126_);
lean_dec(v_connect_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim(lean_object* v_motive_128_, uint8_t v_t_129_, lean_object* v_h_130_, lean_object* v_connect_131_){
_start:
{
lean_inc(v_connect_131_);
return v_connect_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___boxed(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_connect_135_){
_start:
{
uint8_t v_t_boxed_136_; lean_object* v_res_137_; 
v_t_boxed_136_ = lean_unbox(v_t_133_);
v_res_137_ = l_Std_Http_Method_connect_elim(v_motive_132_, v_t_boxed_136_, v_h_134_, v_connect_135_);
lean_dec(v_connect_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg(lean_object* v_copy_138_){
_start:
{
lean_inc(v_copy_138_);
return v_copy_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg___boxed(lean_object* v_copy_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_Http_Method_copy_elim___redArg(v_copy_139_);
lean_dec(v_copy_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim(lean_object* v_motive_141_, uint8_t v_t_142_, lean_object* v_h_143_, lean_object* v_copy_144_){
_start:
{
lean_inc(v_copy_144_);
return v_copy_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___boxed(lean_object* v_motive_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_copy_148_){
_start:
{
uint8_t v_t_boxed_149_; lean_object* v_res_150_; 
v_t_boxed_149_ = lean_unbox(v_t_146_);
v_res_150_ = l_Std_Http_Method_copy_elim(v_motive_145_, v_t_boxed_149_, v_h_147_, v_copy_148_);
lean_dec(v_copy_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg(lean_object* v_delete_151_){
_start:
{
lean_inc(v_delete_151_);
return v_delete_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg___boxed(lean_object* v_delete_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Http_Method_delete_elim___redArg(v_delete_152_);
lean_dec(v_delete_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim(lean_object* v_motive_154_, uint8_t v_t_155_, lean_object* v_h_156_, lean_object* v_delete_157_){
_start:
{
lean_inc(v_delete_157_);
return v_delete_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___boxed(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_delete_161_){
_start:
{
uint8_t v_t_boxed_162_; lean_object* v_res_163_; 
v_t_boxed_162_ = lean_unbox(v_t_159_);
v_res_163_ = l_Std_Http_Method_delete_elim(v_motive_158_, v_t_boxed_162_, v_h_160_, v_delete_161_);
lean_dec(v_delete_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg(lean_object* v_get_164_){
_start:
{
lean_inc(v_get_164_);
return v_get_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg___boxed(lean_object* v_get_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Http_Method_get_elim___redArg(v_get_165_);
lean_dec(v_get_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim(lean_object* v_motive_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_get_170_){
_start:
{
lean_inc(v_get_170_);
return v_get_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___boxed(lean_object* v_motive_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_get_174_){
_start:
{
uint8_t v_t_boxed_175_; lean_object* v_res_176_; 
v_t_boxed_175_ = lean_unbox(v_t_172_);
v_res_176_ = l_Std_Http_Method_get_elim(v_motive_171_, v_t_boxed_175_, v_h_173_, v_get_174_);
lean_dec(v_get_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg(lean_object* v_head_177_){
_start:
{
lean_inc(v_head_177_);
return v_head_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg___boxed(lean_object* v_head_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Http_Method_head_elim___redArg(v_head_178_);
lean_dec(v_head_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim(lean_object* v_motive_180_, uint8_t v_t_181_, lean_object* v_h_182_, lean_object* v_head_183_){
_start:
{
lean_inc(v_head_183_);
return v_head_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___boxed(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_head_187_){
_start:
{
uint8_t v_t_boxed_188_; lean_object* v_res_189_; 
v_t_boxed_188_ = lean_unbox(v_t_185_);
v_res_189_ = l_Std_Http_Method_head_elim(v_motive_184_, v_t_boxed_188_, v_h_186_, v_head_187_);
lean_dec(v_head_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg(lean_object* v_label_190_){
_start:
{
lean_inc(v_label_190_);
return v_label_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg___boxed(lean_object* v_label_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Http_Method_label_elim___redArg(v_label_191_);
lean_dec(v_label_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim(lean_object* v_motive_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_label_196_){
_start:
{
lean_inc(v_label_196_);
return v_label_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___boxed(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_label_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Std_Http_Method_label_elim(v_motive_197_, v_t_boxed_201_, v_h_199_, v_label_200_);
lean_dec(v_label_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg(lean_object* v_link_203_){
_start:
{
lean_inc(v_link_203_);
return v_link_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg___boxed(lean_object* v_link_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_Http_Method_link_elim___redArg(v_link_204_);
lean_dec(v_link_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_link_209_){
_start:
{
lean_inc(v_link_209_);
return v_link_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_link_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Std_Http_Method_link_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_link_213_);
lean_dec(v_link_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg(lean_object* v_lock_216_){
_start:
{
lean_inc(v_lock_216_);
return v_lock_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg___boxed(lean_object* v_lock_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Http_Method_lock_elim___redArg(v_lock_217_);
lean_dec(v_lock_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_lock_222_){
_start:
{
lean_inc(v_lock_222_);
return v_lock_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_lock_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Std_Http_Method_lock_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_lock_226_);
lean_dec(v_lock_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg(lean_object* v_merge_229_){
_start:
{
lean_inc(v_merge_229_);
return v_merge_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg___boxed(lean_object* v_merge_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Http_Method_merge_elim___redArg(v_merge_230_);
lean_dec(v_merge_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_merge_235_){
_start:
{
lean_inc(v_merge_235_);
return v_merge_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_merge_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Std_Http_Method_merge_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_merge_239_);
lean_dec(v_merge_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg(lean_object* v_mkactivity_242_){
_start:
{
lean_inc(v_mkactivity_242_);
return v_mkactivity_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg___boxed(lean_object* v_mkactivity_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Http_Method_mkactivity_elim___redArg(v_mkactivity_243_);
lean_dec(v_mkactivity_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_mkactivity_248_){
_start:
{
lean_inc(v_mkactivity_248_);
return v_mkactivity_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_mkactivity_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Std_Http_Method_mkactivity_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_mkactivity_252_);
lean_dec(v_mkactivity_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg(lean_object* v_mkcalendar_255_){
_start:
{
lean_inc(v_mkcalendar_255_);
return v_mkcalendar_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg___boxed(lean_object* v_mkcalendar_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Http_Method_mkcalendar_elim___redArg(v_mkcalendar_256_);
lean_dec(v_mkcalendar_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_mkcalendar_261_){
_start:
{
lean_inc(v_mkcalendar_261_);
return v_mkcalendar_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_mkcalendar_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Std_Http_Method_mkcalendar_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_mkcalendar_265_);
lean_dec(v_mkcalendar_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg(lean_object* v_mkcol_268_){
_start:
{
lean_inc(v_mkcol_268_);
return v_mkcol_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg___boxed(lean_object* v_mkcol_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Http_Method_mkcol_elim___redArg(v_mkcol_269_);
lean_dec(v_mkcol_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim(lean_object* v_motive_271_, uint8_t v_t_272_, lean_object* v_h_273_, lean_object* v_mkcol_274_){
_start:
{
lean_inc(v_mkcol_274_);
return v_mkcol_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___boxed(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_mkcol_278_){
_start:
{
uint8_t v_t_boxed_279_; lean_object* v_res_280_; 
v_t_boxed_279_ = lean_unbox(v_t_276_);
v_res_280_ = l_Std_Http_Method_mkcol_elim(v_motive_275_, v_t_boxed_279_, v_h_277_, v_mkcol_278_);
lean_dec(v_mkcol_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg(lean_object* v_mkredirectref_281_){
_start:
{
lean_inc(v_mkredirectref_281_);
return v_mkredirectref_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg___boxed(lean_object* v_mkredirectref_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Http_Method_mkredirectref_elim___redArg(v_mkredirectref_282_);
lean_dec(v_mkredirectref_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim(lean_object* v_motive_284_, uint8_t v_t_285_, lean_object* v_h_286_, lean_object* v_mkredirectref_287_){
_start:
{
lean_inc(v_mkredirectref_287_);
return v_mkredirectref_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___boxed(lean_object* v_motive_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_mkredirectref_291_){
_start:
{
uint8_t v_t_boxed_292_; lean_object* v_res_293_; 
v_t_boxed_292_ = lean_unbox(v_t_289_);
v_res_293_ = l_Std_Http_Method_mkredirectref_elim(v_motive_288_, v_t_boxed_292_, v_h_290_, v_mkredirectref_291_);
lean_dec(v_mkredirectref_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg(lean_object* v_mkworkspace_294_){
_start:
{
lean_inc(v_mkworkspace_294_);
return v_mkworkspace_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg___boxed(lean_object* v_mkworkspace_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Http_Method_mkworkspace_elim___redArg(v_mkworkspace_295_);
lean_dec(v_mkworkspace_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim(lean_object* v_motive_297_, uint8_t v_t_298_, lean_object* v_h_299_, lean_object* v_mkworkspace_300_){
_start:
{
lean_inc(v_mkworkspace_300_);
return v_mkworkspace_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___boxed(lean_object* v_motive_301_, lean_object* v_t_302_, lean_object* v_h_303_, lean_object* v_mkworkspace_304_){
_start:
{
uint8_t v_t_boxed_305_; lean_object* v_res_306_; 
v_t_boxed_305_ = lean_unbox(v_t_302_);
v_res_306_ = l_Std_Http_Method_mkworkspace_elim(v_motive_301_, v_t_boxed_305_, v_h_303_, v_mkworkspace_304_);
lean_dec(v_mkworkspace_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg(lean_object* v_move_307_){
_start:
{
lean_inc(v_move_307_);
return v_move_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg___boxed(lean_object* v_move_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Http_Method_move_elim___redArg(v_move_308_);
lean_dec(v_move_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim(lean_object* v_motive_310_, uint8_t v_t_311_, lean_object* v_h_312_, lean_object* v_move_313_){
_start:
{
lean_inc(v_move_313_);
return v_move_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___boxed(lean_object* v_motive_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_move_317_){
_start:
{
uint8_t v_t_boxed_318_; lean_object* v_res_319_; 
v_t_boxed_318_ = lean_unbox(v_t_315_);
v_res_319_ = l_Std_Http_Method_move_elim(v_motive_314_, v_t_boxed_318_, v_h_316_, v_move_317_);
lean_dec(v_move_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg(lean_object* v_options_320_){
_start:
{
lean_inc(v_options_320_);
return v_options_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg___boxed(lean_object* v_options_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_Http_Method_options_elim___redArg(v_options_321_);
lean_dec(v_options_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim(lean_object* v_motive_323_, uint8_t v_t_324_, lean_object* v_h_325_, lean_object* v_options_326_){
_start:
{
lean_inc(v_options_326_);
return v_options_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___boxed(lean_object* v_motive_327_, lean_object* v_t_328_, lean_object* v_h_329_, lean_object* v_options_330_){
_start:
{
uint8_t v_t_boxed_331_; lean_object* v_res_332_; 
v_t_boxed_331_ = lean_unbox(v_t_328_);
v_res_332_ = l_Std_Http_Method_options_elim(v_motive_327_, v_t_boxed_331_, v_h_329_, v_options_330_);
lean_dec(v_options_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg(lean_object* v_orderpatch_333_){
_start:
{
lean_inc(v_orderpatch_333_);
return v_orderpatch_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg___boxed(lean_object* v_orderpatch_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Http_Method_orderpatch_elim___redArg(v_orderpatch_334_);
lean_dec(v_orderpatch_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim(lean_object* v_motive_336_, uint8_t v_t_337_, lean_object* v_h_338_, lean_object* v_orderpatch_339_){
_start:
{
lean_inc(v_orderpatch_339_);
return v_orderpatch_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___boxed(lean_object* v_motive_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_orderpatch_343_){
_start:
{
uint8_t v_t_boxed_344_; lean_object* v_res_345_; 
v_t_boxed_344_ = lean_unbox(v_t_341_);
v_res_345_ = l_Std_Http_Method_orderpatch_elim(v_motive_340_, v_t_boxed_344_, v_h_342_, v_orderpatch_343_);
lean_dec(v_orderpatch_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg(lean_object* v_patch_346_){
_start:
{
lean_inc(v_patch_346_);
return v_patch_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg___boxed(lean_object* v_patch_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Http_Method_patch_elim___redArg(v_patch_347_);
lean_dec(v_patch_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim(lean_object* v_motive_349_, uint8_t v_t_350_, lean_object* v_h_351_, lean_object* v_patch_352_){
_start:
{
lean_inc(v_patch_352_);
return v_patch_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___boxed(lean_object* v_motive_353_, lean_object* v_t_354_, lean_object* v_h_355_, lean_object* v_patch_356_){
_start:
{
uint8_t v_t_boxed_357_; lean_object* v_res_358_; 
v_t_boxed_357_ = lean_unbox(v_t_354_);
v_res_358_ = l_Std_Http_Method_patch_elim(v_motive_353_, v_t_boxed_357_, v_h_355_, v_patch_356_);
lean_dec(v_patch_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg(lean_object* v_post_359_){
_start:
{
lean_inc(v_post_359_);
return v_post_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg___boxed(lean_object* v_post_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Http_Method_post_elim___redArg(v_post_360_);
lean_dec(v_post_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim(lean_object* v_motive_362_, uint8_t v_t_363_, lean_object* v_h_364_, lean_object* v_post_365_){
_start:
{
lean_inc(v_post_365_);
return v_post_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___boxed(lean_object* v_motive_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_post_369_){
_start:
{
uint8_t v_t_boxed_370_; lean_object* v_res_371_; 
v_t_boxed_370_ = lean_unbox(v_t_367_);
v_res_371_ = l_Std_Http_Method_post_elim(v_motive_366_, v_t_boxed_370_, v_h_368_, v_post_369_);
lean_dec(v_post_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg(lean_object* v_pri_372_){
_start:
{
lean_inc(v_pri_372_);
return v_pri_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg___boxed(lean_object* v_pri_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_Http_Method_pri_elim___redArg(v_pri_373_);
lean_dec(v_pri_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim(lean_object* v_motive_375_, uint8_t v_t_376_, lean_object* v_h_377_, lean_object* v_pri_378_){
_start:
{
lean_inc(v_pri_378_);
return v_pri_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___boxed(lean_object* v_motive_379_, lean_object* v_t_380_, lean_object* v_h_381_, lean_object* v_pri_382_){
_start:
{
uint8_t v_t_boxed_383_; lean_object* v_res_384_; 
v_t_boxed_383_ = lean_unbox(v_t_380_);
v_res_384_ = l_Std_Http_Method_pri_elim(v_motive_379_, v_t_boxed_383_, v_h_381_, v_pri_382_);
lean_dec(v_pri_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg(lean_object* v_propfind_385_){
_start:
{
lean_inc(v_propfind_385_);
return v_propfind_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg___boxed(lean_object* v_propfind_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Http_Method_propfind_elim___redArg(v_propfind_386_);
lean_dec(v_propfind_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim(lean_object* v_motive_388_, uint8_t v_t_389_, lean_object* v_h_390_, lean_object* v_propfind_391_){
_start:
{
lean_inc(v_propfind_391_);
return v_propfind_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___boxed(lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_propfind_395_){
_start:
{
uint8_t v_t_boxed_396_; lean_object* v_res_397_; 
v_t_boxed_396_ = lean_unbox(v_t_393_);
v_res_397_ = l_Std_Http_Method_propfind_elim(v_motive_392_, v_t_boxed_396_, v_h_394_, v_propfind_395_);
lean_dec(v_propfind_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg(lean_object* v_proppatch_398_){
_start:
{
lean_inc(v_proppatch_398_);
return v_proppatch_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg___boxed(lean_object* v_proppatch_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_Http_Method_proppatch_elim___redArg(v_proppatch_399_);
lean_dec(v_proppatch_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim(lean_object* v_motive_401_, uint8_t v_t_402_, lean_object* v_h_403_, lean_object* v_proppatch_404_){
_start:
{
lean_inc(v_proppatch_404_);
return v_proppatch_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___boxed(lean_object* v_motive_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_proppatch_408_){
_start:
{
uint8_t v_t_boxed_409_; lean_object* v_res_410_; 
v_t_boxed_409_ = lean_unbox(v_t_406_);
v_res_410_ = l_Std_Http_Method_proppatch_elim(v_motive_405_, v_t_boxed_409_, v_h_407_, v_proppatch_408_);
lean_dec(v_proppatch_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg(lean_object* v_put_411_){
_start:
{
lean_inc(v_put_411_);
return v_put_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg___boxed(lean_object* v_put_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Http_Method_put_elim___redArg(v_put_412_);
lean_dec(v_put_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim(lean_object* v_motive_414_, uint8_t v_t_415_, lean_object* v_h_416_, lean_object* v_put_417_){
_start:
{
lean_inc(v_put_417_);
return v_put_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___boxed(lean_object* v_motive_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_put_421_){
_start:
{
uint8_t v_t_boxed_422_; lean_object* v_res_423_; 
v_t_boxed_422_ = lean_unbox(v_t_419_);
v_res_423_ = l_Std_Http_Method_put_elim(v_motive_418_, v_t_boxed_422_, v_h_420_, v_put_421_);
lean_dec(v_put_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg(lean_object* v_query_424_){
_start:
{
lean_inc(v_query_424_);
return v_query_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg___boxed(lean_object* v_query_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_Http_Method_query_elim___redArg(v_query_425_);
lean_dec(v_query_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim(lean_object* v_motive_427_, uint8_t v_t_428_, lean_object* v_h_429_, lean_object* v_query_430_){
_start:
{
lean_inc(v_query_430_);
return v_query_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___boxed(lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_query_434_){
_start:
{
uint8_t v_t_boxed_435_; lean_object* v_res_436_; 
v_t_boxed_435_ = lean_unbox(v_t_432_);
v_res_436_ = l_Std_Http_Method_query_elim(v_motive_431_, v_t_boxed_435_, v_h_433_, v_query_434_);
lean_dec(v_query_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg(lean_object* v_rebind_437_){
_start:
{
lean_inc(v_rebind_437_);
return v_rebind_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg___boxed(lean_object* v_rebind_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_Http_Method_rebind_elim___redArg(v_rebind_438_);
lean_dec(v_rebind_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim(lean_object* v_motive_440_, uint8_t v_t_441_, lean_object* v_h_442_, lean_object* v_rebind_443_){
_start:
{
lean_inc(v_rebind_443_);
return v_rebind_443_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___boxed(lean_object* v_motive_444_, lean_object* v_t_445_, lean_object* v_h_446_, lean_object* v_rebind_447_){
_start:
{
uint8_t v_t_boxed_448_; lean_object* v_res_449_; 
v_t_boxed_448_ = lean_unbox(v_t_445_);
v_res_449_ = l_Std_Http_Method_rebind_elim(v_motive_444_, v_t_boxed_448_, v_h_446_, v_rebind_447_);
lean_dec(v_rebind_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg(lean_object* v_report_450_){
_start:
{
lean_inc(v_report_450_);
return v_report_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg___boxed(lean_object* v_report_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_Http_Method_report_elim___redArg(v_report_451_);
lean_dec(v_report_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim(lean_object* v_motive_453_, uint8_t v_t_454_, lean_object* v_h_455_, lean_object* v_report_456_){
_start:
{
lean_inc(v_report_456_);
return v_report_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___boxed(lean_object* v_motive_457_, lean_object* v_t_458_, lean_object* v_h_459_, lean_object* v_report_460_){
_start:
{
uint8_t v_t_boxed_461_; lean_object* v_res_462_; 
v_t_boxed_461_ = lean_unbox(v_t_458_);
v_res_462_ = l_Std_Http_Method_report_elim(v_motive_457_, v_t_boxed_461_, v_h_459_, v_report_460_);
lean_dec(v_report_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg(lean_object* v_search_463_){
_start:
{
lean_inc(v_search_463_);
return v_search_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg___boxed(lean_object* v_search_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_Http_Method_search_elim___redArg(v_search_464_);
lean_dec(v_search_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim(lean_object* v_motive_466_, uint8_t v_t_467_, lean_object* v_h_468_, lean_object* v_search_469_){
_start:
{
lean_inc(v_search_469_);
return v_search_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___boxed(lean_object* v_motive_470_, lean_object* v_t_471_, lean_object* v_h_472_, lean_object* v_search_473_){
_start:
{
uint8_t v_t_boxed_474_; lean_object* v_res_475_; 
v_t_boxed_474_ = lean_unbox(v_t_471_);
v_res_475_ = l_Std_Http_Method_search_elim(v_motive_470_, v_t_boxed_474_, v_h_472_, v_search_473_);
lean_dec(v_search_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg(lean_object* v_trace_476_){
_start:
{
lean_inc(v_trace_476_);
return v_trace_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg___boxed(lean_object* v_trace_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_Http_Method_trace_elim___redArg(v_trace_477_);
lean_dec(v_trace_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim(lean_object* v_motive_479_, uint8_t v_t_480_, lean_object* v_h_481_, lean_object* v_trace_482_){
_start:
{
lean_inc(v_trace_482_);
return v_trace_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___boxed(lean_object* v_motive_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_trace_486_){
_start:
{
uint8_t v_t_boxed_487_; lean_object* v_res_488_; 
v_t_boxed_487_ = lean_unbox(v_t_484_);
v_res_488_ = l_Std_Http_Method_trace_elim(v_motive_483_, v_t_boxed_487_, v_h_485_, v_trace_486_);
lean_dec(v_trace_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg(lean_object* v_unbind_489_){
_start:
{
lean_inc(v_unbind_489_);
return v_unbind_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg___boxed(lean_object* v_unbind_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_Http_Method_unbind_elim___redArg(v_unbind_490_);
lean_dec(v_unbind_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim(lean_object* v_motive_492_, uint8_t v_t_493_, lean_object* v_h_494_, lean_object* v_unbind_495_){
_start:
{
lean_inc(v_unbind_495_);
return v_unbind_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___boxed(lean_object* v_motive_496_, lean_object* v_t_497_, lean_object* v_h_498_, lean_object* v_unbind_499_){
_start:
{
uint8_t v_t_boxed_500_; lean_object* v_res_501_; 
v_t_boxed_500_ = lean_unbox(v_t_497_);
v_res_501_ = l_Std_Http_Method_unbind_elim(v_motive_496_, v_t_boxed_500_, v_h_498_, v_unbind_499_);
lean_dec(v_unbind_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg(lean_object* v_uncheckout_502_){
_start:
{
lean_inc(v_uncheckout_502_);
return v_uncheckout_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg___boxed(lean_object* v_uncheckout_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_Http_Method_uncheckout_elim___redArg(v_uncheckout_503_);
lean_dec(v_uncheckout_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim(lean_object* v_motive_505_, uint8_t v_t_506_, lean_object* v_h_507_, lean_object* v_uncheckout_508_){
_start:
{
lean_inc(v_uncheckout_508_);
return v_uncheckout_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___boxed(lean_object* v_motive_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_uncheckout_512_){
_start:
{
uint8_t v_t_boxed_513_; lean_object* v_res_514_; 
v_t_boxed_513_ = lean_unbox(v_t_510_);
v_res_514_ = l_Std_Http_Method_uncheckout_elim(v_motive_509_, v_t_boxed_513_, v_h_511_, v_uncheckout_512_);
lean_dec(v_uncheckout_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg(lean_object* v_unlink_515_){
_start:
{
lean_inc(v_unlink_515_);
return v_unlink_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg___boxed(lean_object* v_unlink_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_Http_Method_unlink_elim___redArg(v_unlink_516_);
lean_dec(v_unlink_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim(lean_object* v_motive_518_, uint8_t v_t_519_, lean_object* v_h_520_, lean_object* v_unlink_521_){
_start:
{
lean_inc(v_unlink_521_);
return v_unlink_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___boxed(lean_object* v_motive_522_, lean_object* v_t_523_, lean_object* v_h_524_, lean_object* v_unlink_525_){
_start:
{
uint8_t v_t_boxed_526_; lean_object* v_res_527_; 
v_t_boxed_526_ = lean_unbox(v_t_523_);
v_res_527_ = l_Std_Http_Method_unlink_elim(v_motive_522_, v_t_boxed_526_, v_h_524_, v_unlink_525_);
lean_dec(v_unlink_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___redArg(lean_object* v_unlock_528_){
_start:
{
lean_inc(v_unlock_528_);
return v_unlock_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___redArg___boxed(lean_object* v_unlock_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_Http_Method_unlock_elim___redArg(v_unlock_529_);
lean_dec(v_unlock_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim(lean_object* v_motive_531_, uint8_t v_t_532_, lean_object* v_h_533_, lean_object* v_unlock_534_){
_start:
{
lean_inc(v_unlock_534_);
return v_unlock_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___boxed(lean_object* v_motive_535_, lean_object* v_t_536_, lean_object* v_h_537_, lean_object* v_unlock_538_){
_start:
{
uint8_t v_t_boxed_539_; lean_object* v_res_540_; 
v_t_boxed_539_ = lean_unbox(v_t_536_);
v_res_540_ = l_Std_Http_Method_unlock_elim(v_motive_535_, v_t_boxed_539_, v_h_537_, v_unlock_538_);
lean_dec(v_unlock_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg(lean_object* v_update_541_){
_start:
{
lean_inc(v_update_541_);
return v_update_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg___boxed(lean_object* v_update_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_Http_Method_update_elim___redArg(v_update_542_);
lean_dec(v_update_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim(lean_object* v_motive_544_, uint8_t v_t_545_, lean_object* v_h_546_, lean_object* v_update_547_){
_start:
{
lean_inc(v_update_547_);
return v_update_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___boxed(lean_object* v_motive_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_update_551_){
_start:
{
uint8_t v_t_boxed_552_; lean_object* v_res_553_; 
v_t_boxed_552_ = lean_unbox(v_t_549_);
v_res_553_ = l_Std_Http_Method_update_elim(v_motive_548_, v_t_boxed_552_, v_h_550_, v_update_551_);
lean_dec(v_update_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg(lean_object* v_updateredirectref_554_){
_start:
{
lean_inc(v_updateredirectref_554_);
return v_updateredirectref_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg___boxed(lean_object* v_updateredirectref_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_Http_Method_updateredirectref_elim___redArg(v_updateredirectref_555_);
lean_dec(v_updateredirectref_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim(lean_object* v_motive_557_, uint8_t v_t_558_, lean_object* v_h_559_, lean_object* v_updateredirectref_560_){
_start:
{
lean_inc(v_updateredirectref_560_);
return v_updateredirectref_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___boxed(lean_object* v_motive_561_, lean_object* v_t_562_, lean_object* v_h_563_, lean_object* v_updateredirectref_564_){
_start:
{
uint8_t v_t_boxed_565_; lean_object* v_res_566_; 
v_t_boxed_565_ = lean_unbox(v_t_562_);
v_res_566_ = l_Std_Http_Method_updateredirectref_elim(v_motive_561_, v_t_boxed_565_, v_h_563_, v_updateredirectref_564_);
lean_dec(v_updateredirectref_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg(lean_object* v_versionControl_567_){
_start:
{
lean_inc(v_versionControl_567_);
return v_versionControl_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg___boxed(lean_object* v_versionControl_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_Method_versionControl_elim___redArg(v_versionControl_568_);
lean_dec(v_versionControl_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim(lean_object* v_motive_570_, uint8_t v_t_571_, lean_object* v_h_572_, lean_object* v_versionControl_573_){
_start:
{
lean_inc(v_versionControl_573_);
return v_versionControl_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___boxed(lean_object* v_motive_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_versionControl_577_){
_start:
{
uint8_t v_t_boxed_578_; lean_object* v_res_579_; 
v_t_boxed_578_ = lean_unbox(v_t_575_);
v_res_579_ = l_Std_Http_Method_versionControl_elim(v_motive_574_, v_t_boxed_578_, v_h_576_, v_versionControl_577_);
lean_dec(v_versionControl_577_);
return v_res_579_;
}
}
static lean_object* _init_l_Std_Http_instReprMethod_repr___closed__80(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(2u);
v___x_701_ = lean_nat_to_int(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l_Std_Http_instReprMethod_repr___closed__81(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_to_int(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr(uint8_t v_x_704_, lean_object* v_prec_705_){
_start:
{
lean_object* v___y_707_; lean_object* v___y_714_; lean_object* v___y_721_; lean_object* v___y_728_; lean_object* v___y_735_; lean_object* v___y_742_; lean_object* v___y_749_; lean_object* v___y_756_; lean_object* v___y_763_; lean_object* v___y_770_; lean_object* v___y_777_; lean_object* v___y_784_; lean_object* v___y_791_; lean_object* v___y_798_; lean_object* v___y_805_; lean_object* v___y_812_; lean_object* v___y_819_; lean_object* v___y_826_; lean_object* v___y_833_; lean_object* v___y_840_; lean_object* v___y_847_; lean_object* v___y_854_; lean_object* v___y_861_; lean_object* v___y_868_; lean_object* v___y_875_; lean_object* v___y_882_; lean_object* v___y_889_; lean_object* v___y_896_; lean_object* v___y_903_; lean_object* v___y_910_; lean_object* v___y_917_; lean_object* v___y_924_; lean_object* v___y_931_; lean_object* v___y_938_; lean_object* v___y_945_; lean_object* v___y_952_; lean_object* v___y_959_; lean_object* v___y_966_; lean_object* v___y_973_; lean_object* v___y_980_; 
switch(v_x_704_)
{
case 0:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_unsigned_to_nat(1024u);
v___x_987_ = lean_nat_dec_le(v___x_986_, v_prec_705_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_707_ = v___x_988_;
goto v___jp_706_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_707_ = v___x_989_;
goto v___jp_706_;
}
}
case 1:
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(1024u);
v___x_991_ = lean_nat_dec_le(v___x_990_, v_prec_705_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_714_ = v___x_992_;
goto v___jp_713_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_714_ = v___x_993_;
goto v___jp_713_;
}
}
case 2:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_unsigned_to_nat(1024u);
v___x_995_ = lean_nat_dec_le(v___x_994_, v_prec_705_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
v___x_996_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_721_ = v___x_996_;
goto v___jp_720_;
}
else
{
lean_object* v___x_997_; 
v___x_997_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_721_ = v___x_997_;
goto v___jp_720_;
}
}
case 3:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_unsigned_to_nat(1024u);
v___x_999_ = lean_nat_dec_le(v___x_998_, v_prec_705_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_728_ = v___x_1000_;
goto v___jp_727_;
}
else
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_728_ = v___x_1001_;
goto v___jp_727_;
}
}
case 4:
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(1024u);
v___x_1003_ = lean_nat_dec_le(v___x_1002_, v_prec_705_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_735_ = v___x_1004_;
goto v___jp_734_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_735_ = v___x_1005_;
goto v___jp_734_;
}
}
case 5:
{
lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = lean_unsigned_to_nat(1024u);
v___x_1007_ = lean_nat_dec_le(v___x_1006_, v_prec_705_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_742_ = v___x_1008_;
goto v___jp_741_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_742_ = v___x_1009_;
goto v___jp_741_;
}
}
case 6:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(1024u);
v___x_1011_ = lean_nat_dec_le(v___x_1010_, v_prec_705_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_749_ = v___x_1012_;
goto v___jp_748_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_749_ = v___x_1013_;
goto v___jp_748_;
}
}
case 7:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_unsigned_to_nat(1024u);
v___x_1015_ = lean_nat_dec_le(v___x_1014_, v_prec_705_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_756_ = v___x_1016_;
goto v___jp_755_;
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_756_ = v___x_1017_;
goto v___jp_755_;
}
}
case 8:
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(1024u);
v___x_1019_ = lean_nat_dec_le(v___x_1018_, v_prec_705_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_763_ = v___x_1020_;
goto v___jp_762_;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_763_ = v___x_1021_;
goto v___jp_762_;
}
}
case 9:
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(1024u);
v___x_1023_ = lean_nat_dec_le(v___x_1022_, v_prec_705_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_770_ = v___x_1024_;
goto v___jp_769_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_770_ = v___x_1025_;
goto v___jp_769_;
}
}
case 10:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = lean_unsigned_to_nat(1024u);
v___x_1027_ = lean_nat_dec_le(v___x_1026_, v_prec_705_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_777_ = v___x_1028_;
goto v___jp_776_;
}
else
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_777_ = v___x_1029_;
goto v___jp_776_;
}
}
case 11:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_unsigned_to_nat(1024u);
v___x_1031_ = lean_nat_dec_le(v___x_1030_, v_prec_705_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_784_ = v___x_1032_;
goto v___jp_783_;
}
else
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_784_ = v___x_1033_;
goto v___jp_783_;
}
}
case 12:
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_unsigned_to_nat(1024u);
v___x_1035_ = lean_nat_dec_le(v___x_1034_, v_prec_705_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_791_ = v___x_1036_;
goto v___jp_790_;
}
else
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_791_ = v___x_1037_;
goto v___jp_790_;
}
}
case 13:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_unsigned_to_nat(1024u);
v___x_1039_ = lean_nat_dec_le(v___x_1038_, v_prec_705_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_798_ = v___x_1040_;
goto v___jp_797_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_798_ = v___x_1041_;
goto v___jp_797_;
}
}
case 14:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(1024u);
v___x_1043_ = lean_nat_dec_le(v___x_1042_, v_prec_705_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_805_ = v___x_1044_;
goto v___jp_804_;
}
else
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_805_ = v___x_1045_;
goto v___jp_804_;
}
}
case 15:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_unsigned_to_nat(1024u);
v___x_1047_ = lean_nat_dec_le(v___x_1046_, v_prec_705_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_812_ = v___x_1048_;
goto v___jp_811_;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_812_ = v___x_1049_;
goto v___jp_811_;
}
}
case 16:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(1024u);
v___x_1051_ = lean_nat_dec_le(v___x_1050_, v_prec_705_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_819_ = v___x_1052_;
goto v___jp_818_;
}
else
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_819_ = v___x_1053_;
goto v___jp_818_;
}
}
case 17:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_unsigned_to_nat(1024u);
v___x_1055_ = lean_nat_dec_le(v___x_1054_, v_prec_705_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_826_ = v___x_1056_;
goto v___jp_825_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_826_ = v___x_1057_;
goto v___jp_825_;
}
}
case 18:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(1024u);
v___x_1059_ = lean_nat_dec_le(v___x_1058_, v_prec_705_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_833_ = v___x_1060_;
goto v___jp_832_;
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_833_ = v___x_1061_;
goto v___jp_832_;
}
}
case 19:
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(1024u);
v___x_1063_ = lean_nat_dec_le(v___x_1062_, v_prec_705_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_840_ = v___x_1064_;
goto v___jp_839_;
}
else
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_840_ = v___x_1065_;
goto v___jp_839_;
}
}
case 20:
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(1024u);
v___x_1067_ = lean_nat_dec_le(v___x_1066_, v_prec_705_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_847_ = v___x_1068_;
goto v___jp_846_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_847_ = v___x_1069_;
goto v___jp_846_;
}
}
case 21:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_unsigned_to_nat(1024u);
v___x_1071_ = lean_nat_dec_le(v___x_1070_, v_prec_705_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_854_ = v___x_1072_;
goto v___jp_853_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_854_ = v___x_1073_;
goto v___jp_853_;
}
}
case 22:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(1024u);
v___x_1075_ = lean_nat_dec_le(v___x_1074_, v_prec_705_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_861_ = v___x_1076_;
goto v___jp_860_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_861_ = v___x_1077_;
goto v___jp_860_;
}
}
case 23:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(1024u);
v___x_1079_ = lean_nat_dec_le(v___x_1078_, v_prec_705_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_868_ = v___x_1080_;
goto v___jp_867_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_868_ = v___x_1081_;
goto v___jp_867_;
}
}
case 24:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_unsigned_to_nat(1024u);
v___x_1083_ = lean_nat_dec_le(v___x_1082_, v_prec_705_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_875_ = v___x_1084_;
goto v___jp_874_;
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_875_ = v___x_1085_;
goto v___jp_874_;
}
}
case 25:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_unsigned_to_nat(1024u);
v___x_1087_ = lean_nat_dec_le(v___x_1086_, v_prec_705_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_882_ = v___x_1088_;
goto v___jp_881_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_882_ = v___x_1089_;
goto v___jp_881_;
}
}
case 26:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_unsigned_to_nat(1024u);
v___x_1091_ = lean_nat_dec_le(v___x_1090_, v_prec_705_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_889_ = v___x_1092_;
goto v___jp_888_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_889_ = v___x_1093_;
goto v___jp_888_;
}
}
case 27:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = lean_unsigned_to_nat(1024u);
v___x_1095_ = lean_nat_dec_le(v___x_1094_, v_prec_705_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_896_ = v___x_1096_;
goto v___jp_895_;
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_896_ = v___x_1097_;
goto v___jp_895_;
}
}
case 28:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_unsigned_to_nat(1024u);
v___x_1099_ = lean_nat_dec_le(v___x_1098_, v_prec_705_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_903_ = v___x_1100_;
goto v___jp_902_;
}
else
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_903_ = v___x_1101_;
goto v___jp_902_;
}
}
case 29:
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_unsigned_to_nat(1024u);
v___x_1103_ = lean_nat_dec_le(v___x_1102_, v_prec_705_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_910_ = v___x_1104_;
goto v___jp_909_;
}
else
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_910_ = v___x_1105_;
goto v___jp_909_;
}
}
case 30:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_unsigned_to_nat(1024u);
v___x_1107_ = lean_nat_dec_le(v___x_1106_, v_prec_705_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_917_ = v___x_1108_;
goto v___jp_916_;
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_917_ = v___x_1109_;
goto v___jp_916_;
}
}
case 31:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_unsigned_to_nat(1024u);
v___x_1111_ = lean_nat_dec_le(v___x_1110_, v_prec_705_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_924_ = v___x_1112_;
goto v___jp_923_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_924_ = v___x_1113_;
goto v___jp_923_;
}
}
case 32:
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = lean_unsigned_to_nat(1024u);
v___x_1115_ = lean_nat_dec_le(v___x_1114_, v_prec_705_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_931_ = v___x_1116_;
goto v___jp_930_;
}
else
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_931_ = v___x_1117_;
goto v___jp_930_;
}
}
case 33:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = lean_unsigned_to_nat(1024u);
v___x_1119_ = lean_nat_dec_le(v___x_1118_, v_prec_705_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_938_ = v___x_1120_;
goto v___jp_937_;
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_938_ = v___x_1121_;
goto v___jp_937_;
}
}
case 34:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(1024u);
v___x_1123_ = lean_nat_dec_le(v___x_1122_, v_prec_705_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_945_ = v___x_1124_;
goto v___jp_944_;
}
else
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_945_ = v___x_1125_;
goto v___jp_944_;
}
}
case 35:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(1024u);
v___x_1127_ = lean_nat_dec_le(v___x_1126_, v_prec_705_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_952_ = v___x_1128_;
goto v___jp_951_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_952_ = v___x_1129_;
goto v___jp_951_;
}
}
case 36:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(1024u);
v___x_1131_ = lean_nat_dec_le(v___x_1130_, v_prec_705_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_959_ = v___x_1132_;
goto v___jp_958_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_959_ = v___x_1133_;
goto v___jp_958_;
}
}
case 37:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_unsigned_to_nat(1024u);
v___x_1135_ = lean_nat_dec_le(v___x_1134_, v_prec_705_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_966_ = v___x_1136_;
goto v___jp_965_;
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_966_ = v___x_1137_;
goto v___jp_965_;
}
}
case 38:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(1024u);
v___x_1139_ = lean_nat_dec_le(v___x_1138_, v_prec_705_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_973_ = v___x_1140_;
goto v___jp_972_;
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_973_ = v___x_1141_;
goto v___jp_972_;
}
}
default: 
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(1024u);
v___x_1143_ = lean_nat_dec_le(v___x_1142_, v_prec_705_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_980_ = v___x_1144_;
goto v___jp_979_;
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_980_ = v___x_1145_;
goto v___jp_979_;
}
}
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_708_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__1));
lean_inc(v___y_707_);
v___x_709_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_709_, 0, v___y_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = 0;
v___x_711_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*1, v___x_710_);
v___x_712_ = l_Repr_addAppParen(v___x_711_, v_prec_705_);
return v___x_712_;
}
v___jp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_715_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__3));
lean_inc(v___y_714_);
v___x_716_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_716_, 0, v___y_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = 0;
v___x_718_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*1, v___x_717_);
v___x_719_ = l_Repr_addAppParen(v___x_718_, v_prec_705_);
return v___x_719_;
}
v___jp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_722_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__5));
lean_inc(v___y_721_);
v___x_723_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_723_, 0, v___y_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = 0;
v___x_725_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*1, v___x_724_);
v___x_726_ = l_Repr_addAppParen(v___x_725_, v_prec_705_);
return v___x_726_;
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_729_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__7));
lean_inc(v___y_728_);
v___x_730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_730_, 0, v___y_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = 0;
v___x_732_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*1, v___x_731_);
v___x_733_ = l_Repr_addAppParen(v___x_732_, v_prec_705_);
return v___x_733_;
}
v___jp_734_:
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_736_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__9));
lean_inc(v___y_735_);
v___x_737_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_737_, 0, v___y_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = 0;
v___x_739_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*1, v___x_738_);
v___x_740_ = l_Repr_addAppParen(v___x_739_, v_prec_705_);
return v___x_740_;
}
v___jp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_743_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__11));
lean_inc(v___y_742_);
v___x_744_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_744_, 0, v___y_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = 0;
v___x_746_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*1, v___x_745_);
v___x_747_ = l_Repr_addAppParen(v___x_746_, v_prec_705_);
return v___x_747_;
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_750_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__13));
lean_inc(v___y_749_);
v___x_751_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_751_, 0, v___y_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = 0;
v___x_753_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*1, v___x_752_);
v___x_754_ = l_Repr_addAppParen(v___x_753_, v_prec_705_);
return v___x_754_;
}
v___jp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_757_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__15));
lean_inc(v___y_756_);
v___x_758_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_758_, 0, v___y_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = 0;
v___x_760_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*1, v___x_759_);
v___x_761_ = l_Repr_addAppParen(v___x_760_, v_prec_705_);
return v___x_761_;
}
v___jp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_764_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__17));
lean_inc(v___y_763_);
v___x_765_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_765_, 0, v___y_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = 0;
v___x_767_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*1, v___x_766_);
v___x_768_ = l_Repr_addAppParen(v___x_767_, v_prec_705_);
return v___x_768_;
}
v___jp_769_:
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_771_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__19));
lean_inc(v___y_770_);
v___x_772_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_772_, 0, v___y_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = 0;
v___x_774_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*1, v___x_773_);
v___x_775_ = l_Repr_addAppParen(v___x_774_, v_prec_705_);
return v___x_775_;
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_778_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__21));
lean_inc(v___y_777_);
v___x_779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_779_, 0, v___y_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = 0;
v___x_781_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*1, v___x_780_);
v___x_782_ = l_Repr_addAppParen(v___x_781_, v_prec_705_);
return v___x_782_;
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_785_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__23));
lean_inc(v___y_784_);
v___x_786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_786_, 0, v___y_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = 0;
v___x_788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*1, v___x_787_);
v___x_789_ = l_Repr_addAppParen(v___x_788_, v_prec_705_);
return v___x_789_;
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_792_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__25));
lean_inc(v___y_791_);
v___x_793_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_793_, 0, v___y_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = 0;
v___x_795_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*1, v___x_794_);
v___x_796_ = l_Repr_addAppParen(v___x_795_, v_prec_705_);
return v___x_796_;
}
v___jp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_799_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__27));
lean_inc(v___y_798_);
v___x_800_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_800_, 0, v___y_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = 0;
v___x_802_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*1, v___x_801_);
v___x_803_ = l_Repr_addAppParen(v___x_802_, v_prec_705_);
return v___x_803_;
}
v___jp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_806_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__29));
lean_inc(v___y_805_);
v___x_807_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_807_, 0, v___y_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = 0;
v___x_809_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*1, v___x_808_);
v___x_810_ = l_Repr_addAppParen(v___x_809_, v_prec_705_);
return v___x_810_;
}
v___jp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_813_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__31));
lean_inc(v___y_812_);
v___x_814_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_814_, 0, v___y_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = 0;
v___x_816_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_815_);
v___x_817_ = l_Repr_addAppParen(v___x_816_, v_prec_705_);
return v___x_817_;
}
v___jp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_820_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__33));
lean_inc(v___y_819_);
v___x_821_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_821_, 0, v___y_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = 0;
v___x_823_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*1, v___x_822_);
v___x_824_ = l_Repr_addAppParen(v___x_823_, v_prec_705_);
return v___x_824_;
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_827_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__35));
lean_inc(v___y_826_);
v___x_828_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_828_, 0, v___y_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = 0;
v___x_830_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*1, v___x_829_);
v___x_831_ = l_Repr_addAppParen(v___x_830_, v_prec_705_);
return v___x_831_;
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_834_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__37));
lean_inc(v___y_833_);
v___x_835_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_835_, 0, v___y_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = 0;
v___x_837_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*1, v___x_836_);
v___x_838_ = l_Repr_addAppParen(v___x_837_, v_prec_705_);
return v___x_838_;
}
v___jp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_841_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__39));
lean_inc(v___y_840_);
v___x_842_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = 0;
v___x_844_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*1, v___x_843_);
v___x_845_ = l_Repr_addAppParen(v___x_844_, v_prec_705_);
return v___x_845_;
}
v___jp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_848_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__41));
lean_inc(v___y_847_);
v___x_849_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_849_, 0, v___y_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = 0;
v___x_851_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*1, v___x_850_);
v___x_852_ = l_Repr_addAppParen(v___x_851_, v_prec_705_);
return v___x_852_;
}
v___jp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_855_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__43));
lean_inc(v___y_854_);
v___x_856_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_856_, 0, v___y_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = 0;
v___x_858_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*1, v___x_857_);
v___x_859_ = l_Repr_addAppParen(v___x_858_, v_prec_705_);
return v___x_859_;
}
v___jp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_862_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__45));
lean_inc(v___y_861_);
v___x_863_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_863_, 0, v___y_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = 0;
v___x_865_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*1, v___x_864_);
v___x_866_ = l_Repr_addAppParen(v___x_865_, v_prec_705_);
return v___x_866_;
}
v___jp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_869_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__47));
lean_inc(v___y_868_);
v___x_870_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_870_, 0, v___y_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = 0;
v___x_872_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*1, v___x_871_);
v___x_873_ = l_Repr_addAppParen(v___x_872_, v_prec_705_);
return v___x_873_;
}
v___jp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_876_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__49));
lean_inc(v___y_875_);
v___x_877_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = 0;
v___x_879_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*1, v___x_878_);
v___x_880_ = l_Repr_addAppParen(v___x_879_, v_prec_705_);
return v___x_880_;
}
v___jp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_883_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__51));
lean_inc(v___y_882_);
v___x_884_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = 0;
v___x_886_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1, v___x_885_);
v___x_887_ = l_Repr_addAppParen(v___x_886_, v_prec_705_);
return v___x_887_;
}
v___jp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_890_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__53));
lean_inc(v___y_889_);
v___x_891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_891_, 0, v___y_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = 0;
v___x_893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_892_);
v___x_894_ = l_Repr_addAppParen(v___x_893_, v_prec_705_);
return v___x_894_;
}
v___jp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_897_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__55));
lean_inc(v___y_896_);
v___x_898_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_898_, 0, v___y_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = 0;
v___x_900_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set_uint8(v___x_900_, sizeof(void*)*1, v___x_899_);
v___x_901_ = l_Repr_addAppParen(v___x_900_, v_prec_705_);
return v___x_901_;
}
v___jp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_904_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__57));
lean_inc(v___y_903_);
v___x_905_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_905_, 0, v___y_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = 0;
v___x_907_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*1, v___x_906_);
v___x_908_ = l_Repr_addAppParen(v___x_907_, v_prec_705_);
return v___x_908_;
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_911_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__59));
lean_inc(v___y_910_);
v___x_912_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_912_, 0, v___y_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = 0;
v___x_914_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*1, v___x_913_);
v___x_915_ = l_Repr_addAppParen(v___x_914_, v_prec_705_);
return v___x_915_;
}
v___jp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_918_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__61));
lean_inc(v___y_917_);
v___x_919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_919_, 0, v___y_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = 0;
v___x_921_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*1, v___x_920_);
v___x_922_ = l_Repr_addAppParen(v___x_921_, v_prec_705_);
return v___x_922_;
}
v___jp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_925_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__63));
lean_inc(v___y_924_);
v___x_926_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_926_, 0, v___y_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = 0;
v___x_928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___x_927_);
v___x_929_ = l_Repr_addAppParen(v___x_928_, v_prec_705_);
return v___x_929_;
}
v___jp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_932_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__65));
lean_inc(v___y_931_);
v___x_933_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_933_, 0, v___y_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = 0;
v___x_935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1, v___x_934_);
v___x_936_ = l_Repr_addAppParen(v___x_935_, v_prec_705_);
return v___x_936_;
}
v___jp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_939_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__67));
lean_inc(v___y_938_);
v___x_940_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_940_, 0, v___y_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = 0;
v___x_942_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*1, v___x_941_);
v___x_943_ = l_Repr_addAppParen(v___x_942_, v_prec_705_);
return v___x_943_;
}
v___jp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_946_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__69));
lean_inc(v___y_945_);
v___x_947_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_947_, 0, v___y_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = 0;
v___x_949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_948_);
v___x_950_ = l_Repr_addAppParen(v___x_949_, v_prec_705_);
return v___x_950_;
}
v___jp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_953_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__71));
lean_inc(v___y_952_);
v___x_954_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_954_, 0, v___y_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = 0;
v___x_956_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*1, v___x_955_);
v___x_957_ = l_Repr_addAppParen(v___x_956_, v_prec_705_);
return v___x_957_;
}
v___jp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_960_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__73));
lean_inc(v___y_959_);
v___x_961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_961_, 0, v___y_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = 0;
v___x_963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*1, v___x_962_);
v___x_964_ = l_Repr_addAppParen(v___x_963_, v_prec_705_);
return v___x_964_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_967_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__75));
lean_inc(v___y_966_);
v___x_968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_968_, 0, v___y_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = 0;
v___x_970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*1, v___x_969_);
v___x_971_ = l_Repr_addAppParen(v___x_970_, v_prec_705_);
return v___x_971_;
}
v___jp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_974_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__77));
lean_inc(v___y_973_);
v___x_975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_975_, 0, v___y_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = 0;
v___x_977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*1, v___x_976_);
v___x_978_ = l_Repr_addAppParen(v___x_977_, v_prec_705_);
return v___x_978_;
}
v___jp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_981_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__79));
lean_inc(v___y_980_);
v___x_982_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_982_, 0, v___y_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = 0;
v___x_984_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*1, v___x_983_);
v___x_985_ = l_Repr_addAppParen(v___x_984_, v_prec_705_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr___boxed(lean_object* v_x_1146_, lean_object* v_prec_1147_){
_start:
{
uint8_t v_x_2249__boxed_1148_; lean_object* v_res_1149_; 
v_x_2249__boxed_1148_ = lean_unbox(v_x_1146_);
v_res_1149_ = l_Std_Http_instReprMethod_repr(v_x_2249__boxed_1148_, v_prec_1147_);
lean_dec(v_prec_1147_);
return v_res_1149_;
}
}
static uint8_t _init_l_Std_Http_instInhabitedMethod_default(void){
_start:
{
uint8_t v___x_1152_; 
v___x_1152_ = 0;
return v___x_1152_;
}
}
static uint8_t _init_l_Std_Http_instInhabitedMethod(void){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = 0;
return v___x_1153_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqMethod_beq(uint8_t v_x_1154_, uint8_t v_y_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = l_Std_Http_Method_ctorIdx(v_x_1154_);
v___x_1157_ = l_Std_Http_Method_ctorIdx(v_y_1155_);
v___x_1158_ = lean_nat_dec_eq(v___x_1156_, v___x_1157_);
lean_dec(v___x_1157_);
lean_dec(v___x_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqMethod_beq___boxed(lean_object* v_x_1159_, lean_object* v_y_1160_){
_start:
{
uint8_t v_x_17__boxed_1161_; uint8_t v_y_18__boxed_1162_; uint8_t v_res_1163_; lean_object* v_r_1164_; 
v_x_17__boxed_1161_ = lean_unbox(v_x_1159_);
v_y_18__boxed_1162_ = lean_unbox(v_y_1160_);
v_res_1163_ = l_Std_Http_instBEqMethod_beq(v_x_17__boxed_1161_, v_y_18__boxed_1162_);
v_r_1164_ = lean_box(v_res_1163_);
return v_r_1164_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_ofNat(lean_object* v_n_1167_){
_start:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(19u);
v___x_1169_ = lean_nat_dec_le(v_n_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_unsigned_to_nat(29u);
v___x_1171_ = lean_nat_dec_le(v_n_1167_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(34u);
v___x_1173_ = lean_nat_dec_le(v_n_1167_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(36u);
v___x_1175_ = lean_nat_dec_le(v_n_1167_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_unsigned_to_nat(37u);
v___x_1177_ = lean_nat_dec_le(v_n_1167_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_unsigned_to_nat(38u);
v___x_1179_ = lean_nat_dec_le(v_n_1167_, v___x_1178_);
if (v___x_1179_ == 0)
{
uint8_t v___x_1180_; 
v___x_1180_ = 39;
return v___x_1180_;
}
else
{
uint8_t v___x_1181_; 
v___x_1181_ = 38;
return v___x_1181_;
}
}
else
{
uint8_t v___x_1182_; 
v___x_1182_ = 37;
return v___x_1182_;
}
}
else
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(35u);
v___x_1184_ = lean_nat_dec_le(v_n_1167_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint8_t v___x_1185_; 
v___x_1185_ = 36;
return v___x_1185_;
}
else
{
uint8_t v___x_1186_; 
v___x_1186_ = 35;
return v___x_1186_;
}
}
}
else
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = lean_unsigned_to_nat(31u);
v___x_1188_ = lean_nat_dec_le(v_n_1167_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(32u);
v___x_1190_ = lean_nat_dec_le(v_n_1167_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(33u);
v___x_1192_ = lean_nat_dec_le(v_n_1167_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = 34;
return v___x_1193_;
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = 33;
return v___x_1194_;
}
}
else
{
uint8_t v___x_1195_; 
v___x_1195_ = 32;
return v___x_1195_;
}
}
else
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(30u);
v___x_1197_ = lean_nat_dec_le(v_n_1167_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; 
v___x_1198_ = 31;
return v___x_1198_;
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = 30;
return v___x_1199_;
}
}
}
}
else
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_unsigned_to_nat(24u);
v___x_1201_ = lean_nat_dec_le(v_n_1167_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(26u);
v___x_1203_ = lean_nat_dec_le(v_n_1167_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(27u);
v___x_1205_ = lean_nat_dec_le(v_n_1167_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_unsigned_to_nat(28u);
v___x_1207_ = lean_nat_dec_le(v_n_1167_, v___x_1206_);
if (v___x_1207_ == 0)
{
uint8_t v___x_1208_; 
v___x_1208_ = 29;
return v___x_1208_;
}
else
{
uint8_t v___x_1209_; 
v___x_1209_ = 28;
return v___x_1209_;
}
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = 27;
return v___x_1210_;
}
}
else
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(25u);
v___x_1212_ = lean_nat_dec_le(v_n_1167_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint8_t v___x_1213_; 
v___x_1213_ = 26;
return v___x_1213_;
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = 25;
return v___x_1214_;
}
}
}
else
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_unsigned_to_nat(21u);
v___x_1216_ = lean_nat_dec_le(v_n_1167_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = lean_unsigned_to_nat(22u);
v___x_1218_ = lean_nat_dec_le(v_n_1167_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = lean_unsigned_to_nat(23u);
v___x_1220_ = lean_nat_dec_le(v_n_1167_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; 
v___x_1221_ = 24;
return v___x_1221_;
}
else
{
uint8_t v___x_1222_; 
v___x_1222_ = 23;
return v___x_1222_;
}
}
else
{
uint8_t v___x_1223_; 
v___x_1223_ = 22;
return v___x_1223_;
}
}
else
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_unsigned_to_nat(20u);
v___x_1225_ = lean_nat_dec_le(v_n_1167_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = 21;
return v___x_1226_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = 20;
return v___x_1227_;
}
}
}
}
}
else
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(9u);
v___x_1229_ = lean_nat_dec_le(v_n_1167_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(14u);
v___x_1231_ = lean_nat_dec_le(v_n_1167_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = lean_unsigned_to_nat(16u);
v___x_1233_ = lean_nat_dec_le(v_n_1167_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = lean_unsigned_to_nat(17u);
v___x_1235_ = lean_nat_dec_le(v_n_1167_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_unsigned_to_nat(18u);
v___x_1237_ = lean_nat_dec_le(v_n_1167_, v___x_1236_);
if (v___x_1237_ == 0)
{
uint8_t v___x_1238_; 
v___x_1238_ = 19;
return v___x_1238_;
}
else
{
uint8_t v___x_1239_; 
v___x_1239_ = 18;
return v___x_1239_;
}
}
else
{
uint8_t v___x_1240_; 
v___x_1240_ = 17;
return v___x_1240_;
}
}
else
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_unsigned_to_nat(15u);
v___x_1242_ = lean_nat_dec_le(v_n_1167_, v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = 16;
return v___x_1243_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = 15;
return v___x_1244_;
}
}
}
else
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_unsigned_to_nat(11u);
v___x_1246_ = lean_nat_dec_le(v_n_1167_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_unsigned_to_nat(12u);
v___x_1248_ = lean_nat_dec_le(v_n_1167_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = lean_unsigned_to_nat(13u);
v___x_1250_ = lean_nat_dec_le(v_n_1167_, v___x_1249_);
if (v___x_1250_ == 0)
{
uint8_t v___x_1251_; 
v___x_1251_ = 14;
return v___x_1251_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = 13;
return v___x_1252_;
}
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 12;
return v___x_1253_;
}
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(10u);
v___x_1255_ = lean_nat_dec_le(v_n_1167_, v___x_1254_);
if (v___x_1255_ == 0)
{
uint8_t v___x_1256_; 
v___x_1256_ = 11;
return v___x_1256_;
}
else
{
uint8_t v___x_1257_; 
v___x_1257_ = 10;
return v___x_1257_;
}
}
}
}
else
{
lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = lean_unsigned_to_nat(4u);
v___x_1259_ = lean_nat_dec_le(v_n_1167_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = lean_unsigned_to_nat(6u);
v___x_1261_ = lean_nat_dec_le(v_n_1167_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = lean_unsigned_to_nat(7u);
v___x_1263_ = lean_nat_dec_le(v_n_1167_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = lean_unsigned_to_nat(8u);
v___x_1265_ = lean_nat_dec_le(v_n_1167_, v___x_1264_);
if (v___x_1265_ == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = 9;
return v___x_1266_;
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = 8;
return v___x_1267_;
}
}
else
{
uint8_t v___x_1268_; 
v___x_1268_ = 7;
return v___x_1268_;
}
}
else
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_unsigned_to_nat(5u);
v___x_1270_ = lean_nat_dec_le(v_n_1167_, v___x_1269_);
if (v___x_1270_ == 0)
{
uint8_t v___x_1271_; 
v___x_1271_ = 6;
return v___x_1271_;
}
else
{
uint8_t v___x_1272_; 
v___x_1272_ = 5;
return v___x_1272_;
}
}
}
else
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_dec_le(v_n_1167_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_unsigned_to_nat(2u);
v___x_1276_ = lean_nat_dec_le(v_n_1167_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(3u);
v___x_1278_ = lean_nat_dec_le(v_n_1167_, v___x_1277_);
if (v___x_1278_ == 0)
{
uint8_t v___x_1279_; 
v___x_1279_ = 4;
return v___x_1279_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = 3;
return v___x_1280_;
}
}
else
{
uint8_t v___x_1281_; 
v___x_1281_ = 2;
return v___x_1281_;
}
}
else
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = lean_nat_dec_le(v_n_1167_, v___x_1282_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; 
v___x_1284_ = 1;
return v___x_1284_;
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofNat___boxed(lean_object* v_n_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Std_Http_Method_ofNat(v_n_1286_);
lean_dec(v_n_1286_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instDecidableEqMethod(uint8_t v_x_1289_, uint8_t v_y_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1291_ = l_Std_Http_Method_ctorIdx(v_x_1289_);
v___x_1292_ = l_Std_Http_Method_ctorIdx(v_y_1290_);
v___x_1293_ = lean_nat_dec_eq(v___x_1291_, v___x_1292_);
lean_dec(v___x_1292_);
lean_dec(v___x_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableEqMethod___boxed(lean_object* v_x_1294_, lean_object* v_y_1295_){
_start:
{
uint8_t v_x_13__boxed_1296_; uint8_t v_y_14__boxed_1297_; uint8_t v_res_1298_; lean_object* v_r_1299_; 
v_x_13__boxed_1296_ = lean_unbox(v_x_1294_);
v_y_14__boxed_1297_ = lean_unbox(v_y_1295_);
v_res_1298_ = l_Std_Http_instDecidableEqMethod(v_x_13__boxed_1296_, v_y_14__boxed_1297_);
v_r_1299_ = lean_box(v_res_1298_);
return v_r_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f(lean_object* v_x_1460_){
_start:
{
lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
v___x_1462_ = lean_string_dec_eq(v_x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
v___x_1464_ = lean_string_dec_eq(v_x_1460_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
v___x_1466_ = lean_string_dec_eq(v_x_1460_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
v___x_1468_ = lean_string_dec_eq(v_x_1460_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
v___x_1470_ = lean_string_dec_eq(v_x_1460_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
v___x_1472_ = lean_string_dec_eq(v_x_1460_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
v___x_1474_ = lean_string_dec_eq(v_x_1460_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
v___x_1476_ = lean_string_dec_eq(v_x_1460_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
v___x_1478_ = lean_string_dec_eq(v_x_1460_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
v___x_1480_ = lean_string_dec_eq(v_x_1460_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
v___x_1482_ = lean_string_dec_eq(v_x_1460_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
v___x_1484_ = lean_string_dec_eq(v_x_1460_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
v___x_1486_ = lean_string_dec_eq(v_x_1460_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
v___x_1488_ = lean_string_dec_eq(v_x_1460_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
v___x_1490_ = lean_string_dec_eq(v_x_1460_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
v___x_1492_ = lean_string_dec_eq(v_x_1460_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
v___x_1494_ = lean_string_dec_eq(v_x_1460_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
v___x_1496_ = lean_string_dec_eq(v_x_1460_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
v___x_1498_ = lean_string_dec_eq(v_x_1460_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
v___x_1500_ = lean_string_dec_eq(v_x_1460_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
v___x_1502_ = lean_string_dec_eq(v_x_1460_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
v___x_1504_ = lean_string_dec_eq(v_x_1460_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
v___x_1506_ = lean_string_dec_eq(v_x_1460_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
v___x_1508_ = lean_string_dec_eq(v_x_1460_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
v___x_1510_ = lean_string_dec_eq(v_x_1460_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
v___x_1512_ = lean_string_dec_eq(v_x_1460_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
v___x_1514_ = lean_string_dec_eq(v_x_1460_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
v___x_1516_ = lean_string_dec_eq(v_x_1460_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
v___x_1518_ = lean_string_dec_eq(v_x_1460_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
v___x_1520_ = lean_string_dec_eq(v_x_1460_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
v___x_1522_ = lean_string_dec_eq(v_x_1460_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
v___x_1524_ = lean_string_dec_eq(v_x_1460_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
v___x_1526_ = lean_string_dec_eq(v_x_1460_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
v___x_1528_ = lean_string_dec_eq(v_x_1460_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
v___x_1530_ = lean_string_dec_eq(v_x_1460_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
v___x_1532_ = lean_string_dec_eq(v_x_1460_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
v___x_1534_ = lean_string_dec_eq(v_x_1460_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
v___x_1536_ = lean_string_dec_eq(v_x_1460_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
v___x_1538_ = lean_string_dec_eq(v_x_1460_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
v___x_1540_ = lean_string_dec_eq(v_x_1460_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; 
v___x_1542_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__40));
return v___x_1542_;
}
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__41));
return v___x_1543_;
}
}
else
{
lean_object* v___x_1544_; 
v___x_1544_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__42));
return v___x_1544_;
}
}
else
{
lean_object* v___x_1545_; 
v___x_1545_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__43));
return v___x_1545_;
}
}
else
{
lean_object* v___x_1546_; 
v___x_1546_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__44));
return v___x_1546_;
}
}
else
{
lean_object* v___x_1547_; 
v___x_1547_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__45));
return v___x_1547_;
}
}
else
{
lean_object* v___x_1548_; 
v___x_1548_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__46));
return v___x_1548_;
}
}
else
{
lean_object* v___x_1549_; 
v___x_1549_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__47));
return v___x_1549_;
}
}
else
{
lean_object* v___x_1550_; 
v___x_1550_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__48));
return v___x_1550_;
}
}
else
{
lean_object* v___x_1551_; 
v___x_1551_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__49));
return v___x_1551_;
}
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__50));
return v___x_1552_;
}
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__51));
return v___x_1553_;
}
}
else
{
lean_object* v___x_1554_; 
v___x_1554_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__52));
return v___x_1554_;
}
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__53));
return v___x_1555_;
}
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__54));
return v___x_1556_;
}
}
else
{
lean_object* v___x_1557_; 
v___x_1557_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__55));
return v___x_1557_;
}
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__56));
return v___x_1558_;
}
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__57));
return v___x_1559_;
}
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__58));
return v___x_1560_;
}
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__59));
return v___x_1561_;
}
}
else
{
lean_object* v___x_1562_; 
v___x_1562_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__60));
return v___x_1562_;
}
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__61));
return v___x_1563_;
}
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__62));
return v___x_1564_;
}
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__63));
return v___x_1565_;
}
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__64));
return v___x_1566_;
}
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__65));
return v___x_1567_;
}
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__66));
return v___x_1568_;
}
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__67));
return v___x_1569_;
}
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__68));
return v___x_1570_;
}
}
else
{
lean_object* v___x_1571_; 
v___x_1571_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__69));
return v___x_1571_;
}
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__70));
return v___x_1572_;
}
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__71));
return v___x_1573_;
}
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__72));
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__73));
return v___x_1575_;
}
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__74));
return v___x_1576_;
}
}
else
{
lean_object* v___x_1577_; 
v___x_1577_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__75));
return v___x_1577_;
}
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__76));
return v___x_1578_;
}
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__77));
return v___x_1579_;
}
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__78));
return v___x_1580_;
}
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__79));
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f___boxed(lean_object* v_x_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Std_Http_Method_ofString_x3f(v_x_1582_);
lean_dec_ref(v_x_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Std_Http_Method_ofString_x21_spec__0(lean_object* v_msg_1584_){
_start:
{
uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1585_ = 0;
v___x_1586_ = lean_box(v___x_1585_);
v___x_1587_ = lean_panic_fn_borrowed(v___x_1586_, v_msg_1584_);
lean_dec(v___x_1586_);
v___x_1588_ = lean_unbox(v___x_1587_);
lean_dec(v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Method_ofString_x21_spec__0___boxed(lean_object* v_msg_1589_){
_start:
{
uint8_t v_res_1590_; lean_object* v_r_1591_; 
v_res_1590_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v_msg_1589_);
v_r_1591_ = lean_box(v_res_1590_);
return v_r_1591_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_ofString_x21(lean_object* v_s_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Std_Http_Method_ofString_x3f(v_s_1595_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1597_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__0));
v___x_1598_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__1));
v___x_1599_ = lean_unsigned_to_nat(337u);
v___x_1600_ = lean_unsigned_to_nat(12u);
v___x_1601_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__2));
v___x_1602_ = l_String_quote(v_s_1595_);
v___x_1603_ = lean_string_append(v___x_1601_, v___x_1602_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = l_mkPanicMessageWithDecl(v___x_1597_, v___x_1598_, v___x_1599_, v___x_1600_, v___x_1603_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v___x_1604_);
return v___x_1605_;
}
else
{
lean_object* v_val_1606_; uint8_t v___x_1607_; 
lean_dec_ref(v_s_1595_);
v_val_1606_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_val_1606_);
lean_dec_ref_known(v___x_1596_, 1);
v___x_1607_ = lean_unbox(v_val_1606_);
lean_dec(v_val_1606_);
return v___x_1607_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x21___boxed(lean_object* v_s_1608_){
_start:
{
uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_res_1609_ = l_Std_Http_Method_ofString_x21(v_s_1608_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_isIdempotent(uint8_t v_m_1611_){
_start:
{
uint8_t v___y_1613_; uint8_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = 8;
v___x_1623_ = l_Std_Http_instBEqMethod_beq(v_m_1611_, v___x_1622_);
if (v___x_1623_ == 0)
{
uint8_t v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = 9;
v___x_1625_ = l_Std_Http_instBEqMethod_beq(v_m_1611_, v___x_1624_);
v___y_1613_ = v___x_1625_;
goto v___jp_1612_;
}
else
{
v___y_1613_ = v___x_1623_;
goto v___jp_1612_;
}
v___jp_1612_:
{
if (v___y_1613_ == 0)
{
uint8_t v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = 27;
v___x_1615_ = l_Std_Http_instBEqMethod_beq(v_m_1611_, v___x_1614_);
if (v___x_1615_ == 0)
{
uint8_t v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = 7;
v___x_1617_ = l_Std_Http_instBEqMethod_beq(v_m_1611_, v___x_1616_);
if (v___x_1617_ == 0)
{
uint8_t v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = 20;
v___x_1619_ = l_Std_Http_instBEqMethod_beq(v_m_1611_, v___x_1618_);
if (v___x_1619_ == 0)
{
uint8_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = 32;
v___x_1621_ = l_Std_Http_instBEqMethod_beq(v_m_1611_, v___x_1620_);
return v___x_1621_;
}
else
{
return v___x_1619_;
}
}
else
{
return v___x_1617_;
}
}
else
{
return v___x_1615_;
}
}
else
{
return v___y_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_isIdempotent___boxed(lean_object* v_m_1626_){
_start:
{
uint8_t v_m_boxed_1627_; uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_m_boxed_1627_ = lean_unbox(v_m_1626_);
v_res_1628_ = l_Std_Http_Method_isIdempotent(v_m_boxed_1627_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_isSafe(uint8_t v_m_1630_){
_start:
{
uint8_t v___y_1632_; uint8_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = 8;
v___x_1638_ = l_Std_Http_instBEqMethod_beq(v_m_1630_, v___x_1637_);
if (v___x_1638_ == 0)
{
uint8_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = 9;
v___x_1640_ = l_Std_Http_instBEqMethod_beq(v_m_1630_, v___x_1639_);
v___y_1632_ = v___x_1640_;
goto v___jp_1631_;
}
else
{
v___y_1632_ = v___x_1638_;
goto v___jp_1631_;
}
v___jp_1631_:
{
if (v___y_1632_ == 0)
{
uint8_t v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = 20;
v___x_1634_ = l_Std_Http_instBEqMethod_beq(v_m_1630_, v___x_1633_);
if (v___x_1634_ == 0)
{
uint8_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = 32;
v___x_1636_ = l_Std_Http_instBEqMethod_beq(v_m_1630_, v___x_1635_);
return v___x_1636_;
}
else
{
return v___x_1634_;
}
}
else
{
return v___y_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_isSafe___boxed(lean_object* v_m_1641_){
_start:
{
uint8_t v_m_boxed_1642_; uint8_t v_res_1643_; lean_object* v_r_1644_; 
v_m_boxed_1642_ = lean_unbox(v_m_1641_);
v_res_1643_ = l_Std_Http_Method_isSafe(v_m_boxed_1642_);
v_r_1644_ = lean_box(v_res_1643_);
return v_r_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0(uint8_t v_x_1645_){
_start:
{
switch(v_x_1645_)
{
case 0:
{
lean_object* v___x_1646_; 
v___x_1646_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
return v___x_1646_;
}
case 1:
{
lean_object* v___x_1647_; 
v___x_1647_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
return v___x_1647_;
}
case 2:
{
lean_object* v___x_1648_; 
v___x_1648_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
return v___x_1648_;
}
case 3:
{
lean_object* v___x_1649_; 
v___x_1649_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
return v___x_1649_;
}
case 4:
{
lean_object* v___x_1650_; 
v___x_1650_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
return v___x_1650_;
}
case 5:
{
lean_object* v___x_1651_; 
v___x_1651_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
return v___x_1651_;
}
case 6:
{
lean_object* v___x_1652_; 
v___x_1652_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
return v___x_1652_;
}
case 7:
{
lean_object* v___x_1653_; 
v___x_1653_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
return v___x_1653_;
}
case 8:
{
lean_object* v___x_1654_; 
v___x_1654_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
return v___x_1654_;
}
case 9:
{
lean_object* v___x_1655_; 
v___x_1655_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
return v___x_1655_;
}
case 10:
{
lean_object* v___x_1656_; 
v___x_1656_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
return v___x_1656_;
}
case 11:
{
lean_object* v___x_1657_; 
v___x_1657_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
return v___x_1657_;
}
case 12:
{
lean_object* v___x_1658_; 
v___x_1658_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
return v___x_1658_;
}
case 13:
{
lean_object* v___x_1659_; 
v___x_1659_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
return v___x_1659_;
}
case 14:
{
lean_object* v___x_1660_; 
v___x_1660_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
return v___x_1660_;
}
case 15:
{
lean_object* v___x_1661_; 
v___x_1661_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
return v___x_1661_;
}
case 16:
{
lean_object* v___x_1662_; 
v___x_1662_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
return v___x_1662_;
}
case 17:
{
lean_object* v___x_1663_; 
v___x_1663_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
return v___x_1663_;
}
case 18:
{
lean_object* v___x_1664_; 
v___x_1664_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
return v___x_1664_;
}
case 19:
{
lean_object* v___x_1665_; 
v___x_1665_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
return v___x_1665_;
}
case 20:
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
return v___x_1666_;
}
case 21:
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
return v___x_1667_;
}
case 22:
{
lean_object* v___x_1668_; 
v___x_1668_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
return v___x_1668_;
}
case 23:
{
lean_object* v___x_1669_; 
v___x_1669_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
return v___x_1669_;
}
case 24:
{
lean_object* v___x_1670_; 
v___x_1670_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
return v___x_1670_;
}
case 25:
{
lean_object* v___x_1671_; 
v___x_1671_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
return v___x_1671_;
}
case 26:
{
lean_object* v___x_1672_; 
v___x_1672_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
return v___x_1672_;
}
case 27:
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
return v___x_1673_;
}
case 28:
{
lean_object* v___x_1674_; 
v___x_1674_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
return v___x_1674_;
}
case 29:
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
return v___x_1675_;
}
case 30:
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
return v___x_1676_;
}
case 31:
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
return v___x_1677_;
}
case 32:
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
return v___x_1678_;
}
case 33:
{
lean_object* v___x_1679_; 
v___x_1679_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
return v___x_1679_;
}
case 34:
{
lean_object* v___x_1680_; 
v___x_1680_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
return v___x_1680_;
}
case 35:
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
return v___x_1681_;
}
case 36:
{
lean_object* v___x_1682_; 
v___x_1682_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
return v___x_1682_;
}
case 37:
{
lean_object* v___x_1683_; 
v___x_1683_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
return v___x_1683_;
}
case 38:
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
return v___x_1684_;
}
default: 
{
lean_object* v___x_1685_; 
v___x_1685_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0___boxed(lean_object* v_x_1686_){
_start:
{
uint8_t v_x_366__boxed_1687_; lean_object* v_res_1688_; 
v_x_366__boxed_1687_ = lean_unbox(v_x_1686_);
v_res_1688_ = l_Std_Http_Method_instToString___lam__0(v_x_366__boxed_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0(lean_object* v_buffer_1691_, uint8_t v___y_1692_){
_start:
{
lean_object* v___y_1694_; 
switch(v___y_1692_)
{
case 0:
{
lean_object* v___x_1708_; 
v___x_1708_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
v___y_1694_ = v___x_1708_;
goto v___jp_1693_;
}
case 1:
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
v___y_1694_ = v___x_1709_;
goto v___jp_1693_;
}
case 2:
{
lean_object* v___x_1710_; 
v___x_1710_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
v___y_1694_ = v___x_1710_;
goto v___jp_1693_;
}
case 3:
{
lean_object* v___x_1711_; 
v___x_1711_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
v___y_1694_ = v___x_1711_;
goto v___jp_1693_;
}
case 4:
{
lean_object* v___x_1712_; 
v___x_1712_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
v___y_1694_ = v___x_1712_;
goto v___jp_1693_;
}
case 5:
{
lean_object* v___x_1713_; 
v___x_1713_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
v___y_1694_ = v___x_1713_;
goto v___jp_1693_;
}
case 6:
{
lean_object* v___x_1714_; 
v___x_1714_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
v___y_1694_ = v___x_1714_;
goto v___jp_1693_;
}
case 7:
{
lean_object* v___x_1715_; 
v___x_1715_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
v___y_1694_ = v___x_1715_;
goto v___jp_1693_;
}
case 8:
{
lean_object* v___x_1716_; 
v___x_1716_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
v___y_1694_ = v___x_1716_;
goto v___jp_1693_;
}
case 9:
{
lean_object* v___x_1717_; 
v___x_1717_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
v___y_1694_ = v___x_1717_;
goto v___jp_1693_;
}
case 10:
{
lean_object* v___x_1718_; 
v___x_1718_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
v___y_1694_ = v___x_1718_;
goto v___jp_1693_;
}
case 11:
{
lean_object* v___x_1719_; 
v___x_1719_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
v___y_1694_ = v___x_1719_;
goto v___jp_1693_;
}
case 12:
{
lean_object* v___x_1720_; 
v___x_1720_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
v___y_1694_ = v___x_1720_;
goto v___jp_1693_;
}
case 13:
{
lean_object* v___x_1721_; 
v___x_1721_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
v___y_1694_ = v___x_1721_;
goto v___jp_1693_;
}
case 14:
{
lean_object* v___x_1722_; 
v___x_1722_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
v___y_1694_ = v___x_1722_;
goto v___jp_1693_;
}
case 15:
{
lean_object* v___x_1723_; 
v___x_1723_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
v___y_1694_ = v___x_1723_;
goto v___jp_1693_;
}
case 16:
{
lean_object* v___x_1724_; 
v___x_1724_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
v___y_1694_ = v___x_1724_;
goto v___jp_1693_;
}
case 17:
{
lean_object* v___x_1725_; 
v___x_1725_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
v___y_1694_ = v___x_1725_;
goto v___jp_1693_;
}
case 18:
{
lean_object* v___x_1726_; 
v___x_1726_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
v___y_1694_ = v___x_1726_;
goto v___jp_1693_;
}
case 19:
{
lean_object* v___x_1727_; 
v___x_1727_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
v___y_1694_ = v___x_1727_;
goto v___jp_1693_;
}
case 20:
{
lean_object* v___x_1728_; 
v___x_1728_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
v___y_1694_ = v___x_1728_;
goto v___jp_1693_;
}
case 21:
{
lean_object* v___x_1729_; 
v___x_1729_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
v___y_1694_ = v___x_1729_;
goto v___jp_1693_;
}
case 22:
{
lean_object* v___x_1730_; 
v___x_1730_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
v___y_1694_ = v___x_1730_;
goto v___jp_1693_;
}
case 23:
{
lean_object* v___x_1731_; 
v___x_1731_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
v___y_1694_ = v___x_1731_;
goto v___jp_1693_;
}
case 24:
{
lean_object* v___x_1732_; 
v___x_1732_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
v___y_1694_ = v___x_1732_;
goto v___jp_1693_;
}
case 25:
{
lean_object* v___x_1733_; 
v___x_1733_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
v___y_1694_ = v___x_1733_;
goto v___jp_1693_;
}
case 26:
{
lean_object* v___x_1734_; 
v___x_1734_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
v___y_1694_ = v___x_1734_;
goto v___jp_1693_;
}
case 27:
{
lean_object* v___x_1735_; 
v___x_1735_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
v___y_1694_ = v___x_1735_;
goto v___jp_1693_;
}
case 28:
{
lean_object* v___x_1736_; 
v___x_1736_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
v___y_1694_ = v___x_1736_;
goto v___jp_1693_;
}
case 29:
{
lean_object* v___x_1737_; 
v___x_1737_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
v___y_1694_ = v___x_1737_;
goto v___jp_1693_;
}
case 30:
{
lean_object* v___x_1738_; 
v___x_1738_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
v___y_1694_ = v___x_1738_;
goto v___jp_1693_;
}
case 31:
{
lean_object* v___x_1739_; 
v___x_1739_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
v___y_1694_ = v___x_1739_;
goto v___jp_1693_;
}
case 32:
{
lean_object* v___x_1740_; 
v___x_1740_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
v___y_1694_ = v___x_1740_;
goto v___jp_1693_;
}
case 33:
{
lean_object* v___x_1741_; 
v___x_1741_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
v___y_1694_ = v___x_1741_;
goto v___jp_1693_;
}
case 34:
{
lean_object* v___x_1742_; 
v___x_1742_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
v___y_1694_ = v___x_1742_;
goto v___jp_1693_;
}
case 35:
{
lean_object* v___x_1743_; 
v___x_1743_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
v___y_1694_ = v___x_1743_;
goto v___jp_1693_;
}
case 36:
{
lean_object* v___x_1744_; 
v___x_1744_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
v___y_1694_ = v___x_1744_;
goto v___jp_1693_;
}
case 37:
{
lean_object* v___x_1745_; 
v___x_1745_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
v___y_1694_ = v___x_1745_;
goto v___jp_1693_;
}
case 38:
{
lean_object* v___x_1746_; 
v___x_1746_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
v___y_1694_ = v___x_1746_;
goto v___jp_1693_;
}
default: 
{
lean_object* v___x_1747_; 
v___x_1747_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
v___y_1694_ = v___x_1747_;
goto v___jp_1693_;
}
}
v___jp_1693_:
{
lean_object* v_data_1695_; lean_object* v_size_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1707_; 
v_data_1695_ = lean_ctor_get(v_buffer_1691_, 0);
v_size_1696_ = lean_ctor_get(v_buffer_1691_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_buffer_1691_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1698_ = v_buffer_1691_;
v_isShared_1699_ = v_isSharedCheck_1707_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_size_1696_);
lean_inc(v_data_1695_);
lean_dec(v_buffer_1691_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1707_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1700_ = lean_string_to_utf8(v___y_1694_);
lean_inc_ref(v___x_1700_);
v___x_1701_ = lean_array_push(v_data_1695_, v___x_1700_);
v___x_1702_ = lean_byte_array_size(v___x_1700_);
lean_dec_ref(v___x_1700_);
v___x_1703_ = lean_nat_add(v_size_1696_, v___x_1702_);
lean_dec(v_size_1696_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___x_1703_);
lean_ctor_set(v___x_1698_, 0, v___x_1701_);
v___x_1705_ = v___x_1698_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0___boxed(lean_object* v_buffer_1748_, lean_object* v___y_1749_){
_start:
{
uint8_t v___y_192__boxed_1750_; lean_object* v_res_1751_; 
v___y_192__boxed_1750_ = lean_unbox(v___y_1749_);
v_res_1751_ = l_Std_Http_Method_instEncodeV11___lam__0(v_buffer_1748_, v___y_192__boxed_1750_);
return v_res_1751_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Method(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
