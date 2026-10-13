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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Http_Method_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Http_Method_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Http_Method_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg(lean_object* v_acl_22_){
_start:
{
lean_inc(v_acl_22_);
return v_acl_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg___boxed(lean_object* v_acl_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Http_Method_acl_elim___redArg(v_acl_23_);
lean_dec(v_acl_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_acl_28_){
_start:
{
lean_inc(v_acl_28_);
return v_acl_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_acl_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Http_Method_acl_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_acl_32_);
lean_dec(v_acl_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg(lean_object* v_baselineControl_35_){
_start:
{
lean_inc(v_baselineControl_35_);
return v_baselineControl_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg___boxed(lean_object* v_baselineControl_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Http_Method_baselineControl_elim___redArg(v_baselineControl_36_);
lean_dec(v_baselineControl_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_baselineControl_41_){
_start:
{
lean_inc(v_baselineControl_41_);
return v_baselineControl_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_baselineControl_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Http_Method_baselineControl_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_baselineControl_45_);
lean_dec(v_baselineControl_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg(lean_object* v_bind_48_){
_start:
{
lean_inc(v_bind_48_);
return v_bind_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg___boxed(lean_object* v_bind_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Http_Method_bind_elim___redArg(v_bind_49_);
lean_dec(v_bind_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_bind_54_){
_start:
{
lean_inc(v_bind_54_);
return v_bind_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_bind_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Std_Http_Method_bind_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_bind_58_);
lean_dec(v_bind_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg(lean_object* v_checkin_61_){
_start:
{
lean_inc(v_checkin_61_);
return v_checkin_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg___boxed(lean_object* v_checkin_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_Http_Method_checkin_elim___redArg(v_checkin_62_);
lean_dec(v_checkin_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_checkin_67_){
_start:
{
lean_inc(v_checkin_67_);
return v_checkin_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_checkin_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Std_Http_Method_checkin_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_checkin_71_);
lean_dec(v_checkin_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg(lean_object* v_checkout_74_){
_start:
{
lean_inc(v_checkout_74_);
return v_checkout_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg___boxed(lean_object* v_checkout_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_Http_Method_checkout_elim___redArg(v_checkout_75_);
lean_dec(v_checkout_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_checkout_80_){
_start:
{
lean_inc(v_checkout_80_);
return v_checkout_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_checkout_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l_Std_Http_Method_checkout_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_checkout_84_);
lean_dec(v_checkout_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg(lean_object* v_connect_87_){
_start:
{
lean_inc(v_connect_87_);
return v_connect_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg___boxed(lean_object* v_connect_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Http_Method_connect_elim___redArg(v_connect_88_);
lean_dec(v_connect_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim(lean_object* v_motive_90_, uint8_t v_t_91_, lean_object* v_h_92_, lean_object* v_connect_93_){
_start:
{
lean_inc(v_connect_93_);
return v_connect_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_connect_97_){
_start:
{
uint8_t v_t_boxed_98_; lean_object* v_res_99_; 
v_t_boxed_98_ = lean_unbox(v_t_95_);
v_res_99_ = l_Std_Http_Method_connect_elim(v_motive_94_, v_t_boxed_98_, v_h_96_, v_connect_97_);
lean_dec(v_connect_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg(lean_object* v_copy_100_){
_start:
{
lean_inc(v_copy_100_);
return v_copy_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg___boxed(lean_object* v_copy_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Http_Method_copy_elim___redArg(v_copy_101_);
lean_dec(v_copy_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim(lean_object* v_motive_103_, uint8_t v_t_104_, lean_object* v_h_105_, lean_object* v_copy_106_){
_start:
{
lean_inc(v_copy_106_);
return v_copy_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___boxed(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_copy_110_){
_start:
{
uint8_t v_t_boxed_111_; lean_object* v_res_112_; 
v_t_boxed_111_ = lean_unbox(v_t_108_);
v_res_112_ = l_Std_Http_Method_copy_elim(v_motive_107_, v_t_boxed_111_, v_h_109_, v_copy_110_);
lean_dec(v_copy_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg(lean_object* v_delete_113_){
_start:
{
lean_inc(v_delete_113_);
return v_delete_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg___boxed(lean_object* v_delete_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Http_Method_delete_elim___redArg(v_delete_114_);
lean_dec(v_delete_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim(lean_object* v_motive_116_, uint8_t v_t_117_, lean_object* v_h_118_, lean_object* v_delete_119_){
_start:
{
lean_inc(v_delete_119_);
return v_delete_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___boxed(lean_object* v_motive_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_delete_123_){
_start:
{
uint8_t v_t_boxed_124_; lean_object* v_res_125_; 
v_t_boxed_124_ = lean_unbox(v_t_121_);
v_res_125_ = l_Std_Http_Method_delete_elim(v_motive_120_, v_t_boxed_124_, v_h_122_, v_delete_123_);
lean_dec(v_delete_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg(lean_object* v_get_126_){
_start:
{
lean_inc(v_get_126_);
return v_get_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg___boxed(lean_object* v_get_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Http_Method_get_elim___redArg(v_get_127_);
lean_dec(v_get_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim(lean_object* v_motive_129_, uint8_t v_t_130_, lean_object* v_h_131_, lean_object* v_get_132_){
_start:
{
lean_inc(v_get_132_);
return v_get_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___boxed(lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_get_136_){
_start:
{
uint8_t v_t_boxed_137_; lean_object* v_res_138_; 
v_t_boxed_137_ = lean_unbox(v_t_134_);
v_res_138_ = l_Std_Http_Method_get_elim(v_motive_133_, v_t_boxed_137_, v_h_135_, v_get_136_);
lean_dec(v_get_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg(lean_object* v_head_139_){
_start:
{
lean_inc(v_head_139_);
return v_head_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg___boxed(lean_object* v_head_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_Http_Method_head_elim___redArg(v_head_140_);
lean_dec(v_head_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim(lean_object* v_motive_142_, uint8_t v_t_143_, lean_object* v_h_144_, lean_object* v_head_145_){
_start:
{
lean_inc(v_head_145_);
return v_head_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___boxed(lean_object* v_motive_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_head_149_){
_start:
{
uint8_t v_t_boxed_150_; lean_object* v_res_151_; 
v_t_boxed_150_ = lean_unbox(v_t_147_);
v_res_151_ = l_Std_Http_Method_head_elim(v_motive_146_, v_t_boxed_150_, v_h_148_, v_head_149_);
lean_dec(v_head_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg(lean_object* v_label_152_){
_start:
{
lean_inc(v_label_152_);
return v_label_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg___boxed(lean_object* v_label_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Http_Method_label_elim___redArg(v_label_153_);
lean_dec(v_label_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim(lean_object* v_motive_155_, uint8_t v_t_156_, lean_object* v_h_157_, lean_object* v_label_158_){
_start:
{
lean_inc(v_label_158_);
return v_label_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___boxed(lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_label_162_){
_start:
{
uint8_t v_t_boxed_163_; lean_object* v_res_164_; 
v_t_boxed_163_ = lean_unbox(v_t_160_);
v_res_164_ = l_Std_Http_Method_label_elim(v_motive_159_, v_t_boxed_163_, v_h_161_, v_label_162_);
lean_dec(v_label_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg(lean_object* v_link_165_){
_start:
{
lean_inc(v_link_165_);
return v_link_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg___boxed(lean_object* v_link_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Http_Method_link_elim___redArg(v_link_166_);
lean_dec(v_link_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim(lean_object* v_motive_168_, uint8_t v_t_169_, lean_object* v_h_170_, lean_object* v_link_171_){
_start:
{
lean_inc(v_link_171_);
return v_link_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___boxed(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_link_175_){
_start:
{
uint8_t v_t_boxed_176_; lean_object* v_res_177_; 
v_t_boxed_176_ = lean_unbox(v_t_173_);
v_res_177_ = l_Std_Http_Method_link_elim(v_motive_172_, v_t_boxed_176_, v_h_174_, v_link_175_);
lean_dec(v_link_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg(lean_object* v_lock_178_){
_start:
{
lean_inc(v_lock_178_);
return v_lock_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg___boxed(lean_object* v_lock_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Http_Method_lock_elim___redArg(v_lock_179_);
lean_dec(v_lock_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim(lean_object* v_motive_181_, uint8_t v_t_182_, lean_object* v_h_183_, lean_object* v_lock_184_){
_start:
{
lean_inc(v_lock_184_);
return v_lock_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___boxed(lean_object* v_motive_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_lock_188_){
_start:
{
uint8_t v_t_boxed_189_; lean_object* v_res_190_; 
v_t_boxed_189_ = lean_unbox(v_t_186_);
v_res_190_ = l_Std_Http_Method_lock_elim(v_motive_185_, v_t_boxed_189_, v_h_187_, v_lock_188_);
lean_dec(v_lock_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg(lean_object* v_merge_191_){
_start:
{
lean_inc(v_merge_191_);
return v_merge_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg___boxed(lean_object* v_merge_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Http_Method_merge_elim___redArg(v_merge_192_);
lean_dec(v_merge_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim(lean_object* v_motive_194_, uint8_t v_t_195_, lean_object* v_h_196_, lean_object* v_merge_197_){
_start:
{
lean_inc(v_merge_197_);
return v_merge_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___boxed(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_merge_201_){
_start:
{
uint8_t v_t_boxed_202_; lean_object* v_res_203_; 
v_t_boxed_202_ = lean_unbox(v_t_199_);
v_res_203_ = l_Std_Http_Method_merge_elim(v_motive_198_, v_t_boxed_202_, v_h_200_, v_merge_201_);
lean_dec(v_merge_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg(lean_object* v_mkactivity_204_){
_start:
{
lean_inc(v_mkactivity_204_);
return v_mkactivity_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg___boxed(lean_object* v_mkactivity_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Http_Method_mkactivity_elim___redArg(v_mkactivity_205_);
lean_dec(v_mkactivity_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim(lean_object* v_motive_207_, uint8_t v_t_208_, lean_object* v_h_209_, lean_object* v_mkactivity_210_){
_start:
{
lean_inc(v_mkactivity_210_);
return v_mkactivity_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___boxed(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_mkactivity_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Std_Http_Method_mkactivity_elim(v_motive_211_, v_t_boxed_215_, v_h_213_, v_mkactivity_214_);
lean_dec(v_mkactivity_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg(lean_object* v_mkcalendar_217_){
_start:
{
lean_inc(v_mkcalendar_217_);
return v_mkcalendar_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg___boxed(lean_object* v_mkcalendar_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Http_Method_mkcalendar_elim___redArg(v_mkcalendar_218_);
lean_dec(v_mkcalendar_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_mkcalendar_223_){
_start:
{
lean_inc(v_mkcalendar_223_);
return v_mkcalendar_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_mkcalendar_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Std_Http_Method_mkcalendar_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_mkcalendar_227_);
lean_dec(v_mkcalendar_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg(lean_object* v_mkcol_230_){
_start:
{
lean_inc(v_mkcol_230_);
return v_mkcol_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg___boxed(lean_object* v_mkcol_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Http_Method_mkcol_elim___redArg(v_mkcol_231_);
lean_dec(v_mkcol_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_mkcol_236_){
_start:
{
lean_inc(v_mkcol_236_);
return v_mkcol_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_mkcol_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Std_Http_Method_mkcol_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_mkcol_240_);
lean_dec(v_mkcol_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg(lean_object* v_mkredirectref_243_){
_start:
{
lean_inc(v_mkredirectref_243_);
return v_mkredirectref_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg___boxed(lean_object* v_mkredirectref_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Http_Method_mkredirectref_elim___redArg(v_mkredirectref_244_);
lean_dec(v_mkredirectref_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_mkredirectref_249_){
_start:
{
lean_inc(v_mkredirectref_249_);
return v_mkredirectref_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_mkredirectref_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Std_Http_Method_mkredirectref_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_mkredirectref_253_);
lean_dec(v_mkredirectref_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg(lean_object* v_mkworkspace_256_){
_start:
{
lean_inc(v_mkworkspace_256_);
return v_mkworkspace_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg___boxed(lean_object* v_mkworkspace_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_Http_Method_mkworkspace_elim___redArg(v_mkworkspace_257_);
lean_dec(v_mkworkspace_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_mkworkspace_262_){
_start:
{
lean_inc(v_mkworkspace_262_);
return v_mkworkspace_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___boxed(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_mkworkspace_266_){
_start:
{
uint8_t v_t_boxed_267_; lean_object* v_res_268_; 
v_t_boxed_267_ = lean_unbox(v_t_264_);
v_res_268_ = l_Std_Http_Method_mkworkspace_elim(v_motive_263_, v_t_boxed_267_, v_h_265_, v_mkworkspace_266_);
lean_dec(v_mkworkspace_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg(lean_object* v_move_269_){
_start:
{
lean_inc(v_move_269_);
return v_move_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg___boxed(lean_object* v_move_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Http_Method_move_elim___redArg(v_move_270_);
lean_dec(v_move_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim(lean_object* v_motive_272_, uint8_t v_t_273_, lean_object* v_h_274_, lean_object* v_move_275_){
_start:
{
lean_inc(v_move_275_);
return v_move_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___boxed(lean_object* v_motive_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_move_279_){
_start:
{
uint8_t v_t_boxed_280_; lean_object* v_res_281_; 
v_t_boxed_280_ = lean_unbox(v_t_277_);
v_res_281_ = l_Std_Http_Method_move_elim(v_motive_276_, v_t_boxed_280_, v_h_278_, v_move_279_);
lean_dec(v_move_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg(lean_object* v_options_282_){
_start:
{
lean_inc(v_options_282_);
return v_options_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg___boxed(lean_object* v_options_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_Http_Method_options_elim___redArg(v_options_283_);
lean_dec(v_options_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim(lean_object* v_motive_285_, uint8_t v_t_286_, lean_object* v_h_287_, lean_object* v_options_288_){
_start:
{
lean_inc(v_options_288_);
return v_options_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___boxed(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_options_292_){
_start:
{
uint8_t v_t_boxed_293_; lean_object* v_res_294_; 
v_t_boxed_293_ = lean_unbox(v_t_290_);
v_res_294_ = l_Std_Http_Method_options_elim(v_motive_289_, v_t_boxed_293_, v_h_291_, v_options_292_);
lean_dec(v_options_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg(lean_object* v_orderpatch_295_){
_start:
{
lean_inc(v_orderpatch_295_);
return v_orderpatch_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg___boxed(lean_object* v_orderpatch_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_Http_Method_orderpatch_elim___redArg(v_orderpatch_296_);
lean_dec(v_orderpatch_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim(lean_object* v_motive_298_, uint8_t v_t_299_, lean_object* v_h_300_, lean_object* v_orderpatch_301_){
_start:
{
lean_inc(v_orderpatch_301_);
return v_orderpatch_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___boxed(lean_object* v_motive_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_orderpatch_305_){
_start:
{
uint8_t v_t_boxed_306_; lean_object* v_res_307_; 
v_t_boxed_306_ = lean_unbox(v_t_303_);
v_res_307_ = l_Std_Http_Method_orderpatch_elim(v_motive_302_, v_t_boxed_306_, v_h_304_, v_orderpatch_305_);
lean_dec(v_orderpatch_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg(lean_object* v_patch_308_){
_start:
{
lean_inc(v_patch_308_);
return v_patch_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg___boxed(lean_object* v_patch_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Http_Method_patch_elim___redArg(v_patch_309_);
lean_dec(v_patch_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim(lean_object* v_motive_311_, uint8_t v_t_312_, lean_object* v_h_313_, lean_object* v_patch_314_){
_start:
{
lean_inc(v_patch_314_);
return v_patch_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___boxed(lean_object* v_motive_315_, lean_object* v_t_316_, lean_object* v_h_317_, lean_object* v_patch_318_){
_start:
{
uint8_t v_t_boxed_319_; lean_object* v_res_320_; 
v_t_boxed_319_ = lean_unbox(v_t_316_);
v_res_320_ = l_Std_Http_Method_patch_elim(v_motive_315_, v_t_boxed_319_, v_h_317_, v_patch_318_);
lean_dec(v_patch_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg(lean_object* v_post_321_){
_start:
{
lean_inc(v_post_321_);
return v_post_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg___boxed(lean_object* v_post_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_Http_Method_post_elim___redArg(v_post_322_);
lean_dec(v_post_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim(lean_object* v_motive_324_, uint8_t v_t_325_, lean_object* v_h_326_, lean_object* v_post_327_){
_start:
{
lean_inc(v_post_327_);
return v_post_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___boxed(lean_object* v_motive_328_, lean_object* v_t_329_, lean_object* v_h_330_, lean_object* v_post_331_){
_start:
{
uint8_t v_t_boxed_332_; lean_object* v_res_333_; 
v_t_boxed_332_ = lean_unbox(v_t_329_);
v_res_333_ = l_Std_Http_Method_post_elim(v_motive_328_, v_t_boxed_332_, v_h_330_, v_post_331_);
lean_dec(v_post_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg(lean_object* v_pri_334_){
_start:
{
lean_inc(v_pri_334_);
return v_pri_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg___boxed(lean_object* v_pri_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Http_Method_pri_elim___redArg(v_pri_335_);
lean_dec(v_pri_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim(lean_object* v_motive_337_, uint8_t v_t_338_, lean_object* v_h_339_, lean_object* v_pri_340_){
_start:
{
lean_inc(v_pri_340_);
return v_pri_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___boxed(lean_object* v_motive_341_, lean_object* v_t_342_, lean_object* v_h_343_, lean_object* v_pri_344_){
_start:
{
uint8_t v_t_boxed_345_; lean_object* v_res_346_; 
v_t_boxed_345_ = lean_unbox(v_t_342_);
v_res_346_ = l_Std_Http_Method_pri_elim(v_motive_341_, v_t_boxed_345_, v_h_343_, v_pri_344_);
lean_dec(v_pri_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg(lean_object* v_propfind_347_){
_start:
{
lean_inc(v_propfind_347_);
return v_propfind_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg___boxed(lean_object* v_propfind_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_Http_Method_propfind_elim___redArg(v_propfind_348_);
lean_dec(v_propfind_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim(lean_object* v_motive_350_, uint8_t v_t_351_, lean_object* v_h_352_, lean_object* v_propfind_353_){
_start:
{
lean_inc(v_propfind_353_);
return v_propfind_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___boxed(lean_object* v_motive_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_propfind_357_){
_start:
{
uint8_t v_t_boxed_358_; lean_object* v_res_359_; 
v_t_boxed_358_ = lean_unbox(v_t_355_);
v_res_359_ = l_Std_Http_Method_propfind_elim(v_motive_354_, v_t_boxed_358_, v_h_356_, v_propfind_357_);
lean_dec(v_propfind_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg(lean_object* v_proppatch_360_){
_start:
{
lean_inc(v_proppatch_360_);
return v_proppatch_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg___boxed(lean_object* v_proppatch_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Http_Method_proppatch_elim___redArg(v_proppatch_361_);
lean_dec(v_proppatch_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim(lean_object* v_motive_363_, uint8_t v_t_364_, lean_object* v_h_365_, lean_object* v_proppatch_366_){
_start:
{
lean_inc(v_proppatch_366_);
return v_proppatch_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___boxed(lean_object* v_motive_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_proppatch_370_){
_start:
{
uint8_t v_t_boxed_371_; lean_object* v_res_372_; 
v_t_boxed_371_ = lean_unbox(v_t_368_);
v_res_372_ = l_Std_Http_Method_proppatch_elim(v_motive_367_, v_t_boxed_371_, v_h_369_, v_proppatch_370_);
lean_dec(v_proppatch_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg(lean_object* v_put_373_){
_start:
{
lean_inc(v_put_373_);
return v_put_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg___boxed(lean_object* v_put_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Http_Method_put_elim___redArg(v_put_374_);
lean_dec(v_put_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim(lean_object* v_motive_376_, uint8_t v_t_377_, lean_object* v_h_378_, lean_object* v_put_379_){
_start:
{
lean_inc(v_put_379_);
return v_put_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___boxed(lean_object* v_motive_380_, lean_object* v_t_381_, lean_object* v_h_382_, lean_object* v_put_383_){
_start:
{
uint8_t v_t_boxed_384_; lean_object* v_res_385_; 
v_t_boxed_384_ = lean_unbox(v_t_381_);
v_res_385_ = l_Std_Http_Method_put_elim(v_motive_380_, v_t_boxed_384_, v_h_382_, v_put_383_);
lean_dec(v_put_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg(lean_object* v_query_386_){
_start:
{
lean_inc(v_query_386_);
return v_query_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg___boxed(lean_object* v_query_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_Http_Method_query_elim___redArg(v_query_387_);
lean_dec(v_query_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim(lean_object* v_motive_389_, uint8_t v_t_390_, lean_object* v_h_391_, lean_object* v_query_392_){
_start:
{
lean_inc(v_query_392_);
return v_query_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___boxed(lean_object* v_motive_393_, lean_object* v_t_394_, lean_object* v_h_395_, lean_object* v_query_396_){
_start:
{
uint8_t v_t_boxed_397_; lean_object* v_res_398_; 
v_t_boxed_397_ = lean_unbox(v_t_394_);
v_res_398_ = l_Std_Http_Method_query_elim(v_motive_393_, v_t_boxed_397_, v_h_395_, v_query_396_);
lean_dec(v_query_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg(lean_object* v_rebind_399_){
_start:
{
lean_inc(v_rebind_399_);
return v_rebind_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg___boxed(lean_object* v_rebind_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_Http_Method_rebind_elim___redArg(v_rebind_400_);
lean_dec(v_rebind_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim(lean_object* v_motive_402_, uint8_t v_t_403_, lean_object* v_h_404_, lean_object* v_rebind_405_){
_start:
{
lean_inc(v_rebind_405_);
return v_rebind_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___boxed(lean_object* v_motive_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_rebind_409_){
_start:
{
uint8_t v_t_boxed_410_; lean_object* v_res_411_; 
v_t_boxed_410_ = lean_unbox(v_t_407_);
v_res_411_ = l_Std_Http_Method_rebind_elim(v_motive_406_, v_t_boxed_410_, v_h_408_, v_rebind_409_);
lean_dec(v_rebind_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg(lean_object* v_report_412_){
_start:
{
lean_inc(v_report_412_);
return v_report_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg___boxed(lean_object* v_report_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Http_Method_report_elim___redArg(v_report_413_);
lean_dec(v_report_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim(lean_object* v_motive_415_, uint8_t v_t_416_, lean_object* v_h_417_, lean_object* v_report_418_){
_start:
{
lean_inc(v_report_418_);
return v_report_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___boxed(lean_object* v_motive_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_report_422_){
_start:
{
uint8_t v_t_boxed_423_; lean_object* v_res_424_; 
v_t_boxed_423_ = lean_unbox(v_t_420_);
v_res_424_ = l_Std_Http_Method_report_elim(v_motive_419_, v_t_boxed_423_, v_h_421_, v_report_422_);
lean_dec(v_report_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg(lean_object* v_search_425_){
_start:
{
lean_inc(v_search_425_);
return v_search_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg___boxed(lean_object* v_search_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_Http_Method_search_elim___redArg(v_search_426_);
lean_dec(v_search_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim(lean_object* v_motive_428_, uint8_t v_t_429_, lean_object* v_h_430_, lean_object* v_search_431_){
_start:
{
lean_inc(v_search_431_);
return v_search_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___boxed(lean_object* v_motive_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_search_435_){
_start:
{
uint8_t v_t_boxed_436_; lean_object* v_res_437_; 
v_t_boxed_436_ = lean_unbox(v_t_433_);
v_res_437_ = l_Std_Http_Method_search_elim(v_motive_432_, v_t_boxed_436_, v_h_434_, v_search_435_);
lean_dec(v_search_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg(lean_object* v_trace_438_){
_start:
{
lean_inc(v_trace_438_);
return v_trace_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg___boxed(lean_object* v_trace_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_Http_Method_trace_elim___redArg(v_trace_439_);
lean_dec(v_trace_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim(lean_object* v_motive_441_, uint8_t v_t_442_, lean_object* v_h_443_, lean_object* v_trace_444_){
_start:
{
lean_inc(v_trace_444_);
return v_trace_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___boxed(lean_object* v_motive_445_, lean_object* v_t_446_, lean_object* v_h_447_, lean_object* v_trace_448_){
_start:
{
uint8_t v_t_boxed_449_; lean_object* v_res_450_; 
v_t_boxed_449_ = lean_unbox(v_t_446_);
v_res_450_ = l_Std_Http_Method_trace_elim(v_motive_445_, v_t_boxed_449_, v_h_447_, v_trace_448_);
lean_dec(v_trace_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg(lean_object* v_unbind_451_){
_start:
{
lean_inc(v_unbind_451_);
return v_unbind_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg___boxed(lean_object* v_unbind_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_Http_Method_unbind_elim___redArg(v_unbind_452_);
lean_dec(v_unbind_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim(lean_object* v_motive_454_, uint8_t v_t_455_, lean_object* v_h_456_, lean_object* v_unbind_457_){
_start:
{
lean_inc(v_unbind_457_);
return v_unbind_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___boxed(lean_object* v_motive_458_, lean_object* v_t_459_, lean_object* v_h_460_, lean_object* v_unbind_461_){
_start:
{
uint8_t v_t_boxed_462_; lean_object* v_res_463_; 
v_t_boxed_462_ = lean_unbox(v_t_459_);
v_res_463_ = l_Std_Http_Method_unbind_elim(v_motive_458_, v_t_boxed_462_, v_h_460_, v_unbind_461_);
lean_dec(v_unbind_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg(lean_object* v_uncheckout_464_){
_start:
{
lean_inc(v_uncheckout_464_);
return v_uncheckout_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg___boxed(lean_object* v_uncheckout_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_Http_Method_uncheckout_elim___redArg(v_uncheckout_465_);
lean_dec(v_uncheckout_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim(lean_object* v_motive_467_, uint8_t v_t_468_, lean_object* v_h_469_, lean_object* v_uncheckout_470_){
_start:
{
lean_inc(v_uncheckout_470_);
return v_uncheckout_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___boxed(lean_object* v_motive_471_, lean_object* v_t_472_, lean_object* v_h_473_, lean_object* v_uncheckout_474_){
_start:
{
uint8_t v_t_boxed_475_; lean_object* v_res_476_; 
v_t_boxed_475_ = lean_unbox(v_t_472_);
v_res_476_ = l_Std_Http_Method_uncheckout_elim(v_motive_471_, v_t_boxed_475_, v_h_473_, v_uncheckout_474_);
lean_dec(v_uncheckout_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg(lean_object* v_unlink_477_){
_start:
{
lean_inc(v_unlink_477_);
return v_unlink_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg___boxed(lean_object* v_unlink_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Http_Method_unlink_elim___redArg(v_unlink_478_);
lean_dec(v_unlink_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim(lean_object* v_motive_480_, uint8_t v_t_481_, lean_object* v_h_482_, lean_object* v_unlink_483_){
_start:
{
lean_inc(v_unlink_483_);
return v_unlink_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___boxed(lean_object* v_motive_484_, lean_object* v_t_485_, lean_object* v_h_486_, lean_object* v_unlink_487_){
_start:
{
uint8_t v_t_boxed_488_; lean_object* v_res_489_; 
v_t_boxed_488_ = lean_unbox(v_t_485_);
v_res_489_ = l_Std_Http_Method_unlink_elim(v_motive_484_, v_t_boxed_488_, v_h_486_, v_unlink_487_);
lean_dec(v_unlink_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___redArg(lean_object* v_unlock_490_){
_start:
{
lean_inc(v_unlock_490_);
return v_unlock_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___redArg___boxed(lean_object* v_unlock_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Http_Method_unlock_elim___redArg(v_unlock_491_);
lean_dec(v_unlock_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim(lean_object* v_motive_493_, uint8_t v_t_494_, lean_object* v_h_495_, lean_object* v_unlock_496_){
_start:
{
lean_inc(v_unlock_496_);
return v_unlock_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___boxed(lean_object* v_motive_497_, lean_object* v_t_498_, lean_object* v_h_499_, lean_object* v_unlock_500_){
_start:
{
uint8_t v_t_boxed_501_; lean_object* v_res_502_; 
v_t_boxed_501_ = lean_unbox(v_t_498_);
v_res_502_ = l_Std_Http_Method_unlock_elim(v_motive_497_, v_t_boxed_501_, v_h_499_, v_unlock_500_);
lean_dec(v_unlock_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg(lean_object* v_update_503_){
_start:
{
lean_inc(v_update_503_);
return v_update_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg___boxed(lean_object* v_update_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_Http_Method_update_elim___redArg(v_update_504_);
lean_dec(v_update_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim(lean_object* v_motive_506_, uint8_t v_t_507_, lean_object* v_h_508_, lean_object* v_update_509_){
_start:
{
lean_inc(v_update_509_);
return v_update_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___boxed(lean_object* v_motive_510_, lean_object* v_t_511_, lean_object* v_h_512_, lean_object* v_update_513_){
_start:
{
uint8_t v_t_boxed_514_; lean_object* v_res_515_; 
v_t_boxed_514_ = lean_unbox(v_t_511_);
v_res_515_ = l_Std_Http_Method_update_elim(v_motive_510_, v_t_boxed_514_, v_h_512_, v_update_513_);
lean_dec(v_update_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg(lean_object* v_updateredirectref_516_){
_start:
{
lean_inc(v_updateredirectref_516_);
return v_updateredirectref_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg___boxed(lean_object* v_updateredirectref_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Http_Method_updateredirectref_elim___redArg(v_updateredirectref_517_);
lean_dec(v_updateredirectref_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim(lean_object* v_motive_519_, uint8_t v_t_520_, lean_object* v_h_521_, lean_object* v_updateredirectref_522_){
_start:
{
lean_inc(v_updateredirectref_522_);
return v_updateredirectref_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___boxed(lean_object* v_motive_523_, lean_object* v_t_524_, lean_object* v_h_525_, lean_object* v_updateredirectref_526_){
_start:
{
uint8_t v_t_boxed_527_; lean_object* v_res_528_; 
v_t_boxed_527_ = lean_unbox(v_t_524_);
v_res_528_ = l_Std_Http_Method_updateredirectref_elim(v_motive_523_, v_t_boxed_527_, v_h_525_, v_updateredirectref_526_);
lean_dec(v_updateredirectref_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg(lean_object* v_versionControl_529_){
_start:
{
lean_inc(v_versionControl_529_);
return v_versionControl_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg___boxed(lean_object* v_versionControl_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Http_Method_versionControl_elim___redArg(v_versionControl_530_);
lean_dec(v_versionControl_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim(lean_object* v_motive_532_, uint8_t v_t_533_, lean_object* v_h_534_, lean_object* v_versionControl_535_){
_start:
{
lean_inc(v_versionControl_535_);
return v_versionControl_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___boxed(lean_object* v_motive_536_, lean_object* v_t_537_, lean_object* v_h_538_, lean_object* v_versionControl_539_){
_start:
{
uint8_t v_t_boxed_540_; lean_object* v_res_541_; 
v_t_boxed_540_ = lean_unbox(v_t_537_);
v_res_541_ = l_Std_Http_Method_versionControl_elim(v_motive_536_, v_t_boxed_540_, v_h_538_, v_versionControl_539_);
lean_dec(v_versionControl_539_);
return v_res_541_;
}
}
static lean_object* _init_l_Std_Http_instReprMethod_repr___closed__80(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(2u);
v___x_663_ = lean_nat_to_int(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Std_Http_instReprMethod_repr___closed__81(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_to_int(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr(uint8_t v_x_666_, lean_object* v_prec_667_){
_start:
{
lean_object* v___y_669_; lean_object* v___y_676_; lean_object* v___y_683_; lean_object* v___y_690_; lean_object* v___y_697_; lean_object* v___y_704_; lean_object* v___y_711_; lean_object* v___y_718_; lean_object* v___y_725_; lean_object* v___y_732_; lean_object* v___y_739_; lean_object* v___y_746_; lean_object* v___y_753_; lean_object* v___y_760_; lean_object* v___y_767_; lean_object* v___y_774_; lean_object* v___y_781_; lean_object* v___y_788_; lean_object* v___y_795_; lean_object* v___y_802_; lean_object* v___y_809_; lean_object* v___y_816_; lean_object* v___y_823_; lean_object* v___y_830_; lean_object* v___y_837_; lean_object* v___y_844_; lean_object* v___y_851_; lean_object* v___y_858_; lean_object* v___y_865_; lean_object* v___y_872_; lean_object* v___y_879_; lean_object* v___y_886_; lean_object* v___y_893_; lean_object* v___y_900_; lean_object* v___y_907_; lean_object* v___y_914_; lean_object* v___y_921_; lean_object* v___y_928_; lean_object* v___y_935_; lean_object* v___y_942_; 
switch(v_x_666_)
{
case 0:
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(1024u);
v___x_949_ = lean_nat_dec_le(v___x_948_, v_prec_667_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_669_ = v___x_950_;
goto v___jp_668_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_669_ = v___x_951_;
goto v___jp_668_;
}
}
case 1:
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = lean_unsigned_to_nat(1024u);
v___x_953_ = lean_nat_dec_le(v___x_952_, v_prec_667_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
v___x_954_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_676_ = v___x_954_;
goto v___jp_675_;
}
else
{
lean_object* v___x_955_; 
v___x_955_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_676_ = v___x_955_;
goto v___jp_675_;
}
}
case 2:
{
lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(1024u);
v___x_957_ = lean_nat_dec_le(v___x_956_, v_prec_667_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
v___x_958_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_683_ = v___x_958_;
goto v___jp_682_;
}
else
{
lean_object* v___x_959_; 
v___x_959_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_683_ = v___x_959_;
goto v___jp_682_;
}
}
case 3:
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(1024u);
v___x_961_ = lean_nat_dec_le(v___x_960_, v_prec_667_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_690_ = v___x_962_;
goto v___jp_689_;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_690_ = v___x_963_;
goto v___jp_689_;
}
}
case 4:
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_unsigned_to_nat(1024u);
v___x_965_ = lean_nat_dec_le(v___x_964_, v_prec_667_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
v___x_966_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_697_ = v___x_966_;
goto v___jp_696_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_697_ = v___x_967_;
goto v___jp_696_;
}
}
case 5:
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(1024u);
v___x_969_ = lean_nat_dec_le(v___x_968_, v_prec_667_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
v___x_970_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_704_ = v___x_970_;
goto v___jp_703_;
}
else
{
lean_object* v___x_971_; 
v___x_971_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_704_ = v___x_971_;
goto v___jp_703_;
}
}
case 6:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(1024u);
v___x_973_ = lean_nat_dec_le(v___x_972_, v_prec_667_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_711_ = v___x_974_;
goto v___jp_710_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_711_ = v___x_975_;
goto v___jp_710_;
}
}
case 7:
{
lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_976_ = lean_unsigned_to_nat(1024u);
v___x_977_ = lean_nat_dec_le(v___x_976_, v_prec_667_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_718_ = v___x_978_;
goto v___jp_717_;
}
else
{
lean_object* v___x_979_; 
v___x_979_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_718_ = v___x_979_;
goto v___jp_717_;
}
}
case 8:
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(1024u);
v___x_981_ = lean_nat_dec_le(v___x_980_, v_prec_667_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_725_ = v___x_982_;
goto v___jp_724_;
}
else
{
lean_object* v___x_983_; 
v___x_983_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_725_ = v___x_983_;
goto v___jp_724_;
}
}
case 9:
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(1024u);
v___x_985_ = lean_nat_dec_le(v___x_984_, v_prec_667_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
v___x_986_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_732_ = v___x_986_;
goto v___jp_731_;
}
else
{
lean_object* v___x_987_; 
v___x_987_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_732_ = v___x_987_;
goto v___jp_731_;
}
}
case 10:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_unsigned_to_nat(1024u);
v___x_989_ = lean_nat_dec_le(v___x_988_, v_prec_667_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; 
v___x_990_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_739_ = v___x_990_;
goto v___jp_738_;
}
else
{
lean_object* v___x_991_; 
v___x_991_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_739_ = v___x_991_;
goto v___jp_738_;
}
}
case 11:
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(1024u);
v___x_993_ = lean_nat_dec_le(v___x_992_, v_prec_667_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_746_ = v___x_994_;
goto v___jp_745_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_746_ = v___x_995_;
goto v___jp_745_;
}
}
case 12:
{
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = lean_unsigned_to_nat(1024u);
v___x_997_ = lean_nat_dec_le(v___x_996_, v_prec_667_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; 
v___x_998_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_753_ = v___x_998_;
goto v___jp_752_;
}
else
{
lean_object* v___x_999_; 
v___x_999_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_753_ = v___x_999_;
goto v___jp_752_;
}
}
case 13:
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(1024u);
v___x_1001_ = lean_nat_dec_le(v___x_1000_, v_prec_667_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_760_ = v___x_1002_;
goto v___jp_759_;
}
else
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_760_ = v___x_1003_;
goto v___jp_759_;
}
}
case 14:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(1024u);
v___x_1005_ = lean_nat_dec_le(v___x_1004_, v_prec_667_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_767_ = v___x_1006_;
goto v___jp_766_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_767_ = v___x_1007_;
goto v___jp_766_;
}
}
case 15:
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = lean_unsigned_to_nat(1024u);
v___x_1009_ = lean_nat_dec_le(v___x_1008_, v_prec_667_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_774_ = v___x_1010_;
goto v___jp_773_;
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_774_ = v___x_1011_;
goto v___jp_773_;
}
}
case 16:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(1024u);
v___x_1013_ = lean_nat_dec_le(v___x_1012_, v_prec_667_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_781_ = v___x_1014_;
goto v___jp_780_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_781_ = v___x_1015_;
goto v___jp_780_;
}
}
case 17:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(1024u);
v___x_1017_ = lean_nat_dec_le(v___x_1016_, v_prec_667_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_788_ = v___x_1018_;
goto v___jp_787_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_788_ = v___x_1019_;
goto v___jp_787_;
}
}
case 18:
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(1024u);
v___x_1021_ = lean_nat_dec_le(v___x_1020_, v_prec_667_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_795_ = v___x_1022_;
goto v___jp_794_;
}
else
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_795_ = v___x_1023_;
goto v___jp_794_;
}
}
case 19:
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(1024u);
v___x_1025_ = lean_nat_dec_le(v___x_1024_, v_prec_667_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_802_ = v___x_1026_;
goto v___jp_801_;
}
else
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_802_ = v___x_1027_;
goto v___jp_801_;
}
}
case 20:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_unsigned_to_nat(1024u);
v___x_1029_ = lean_nat_dec_le(v___x_1028_, v_prec_667_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_809_ = v___x_1030_;
goto v___jp_808_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_809_ = v___x_1031_;
goto v___jp_808_;
}
}
case 21:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_unsigned_to_nat(1024u);
v___x_1033_ = lean_nat_dec_le(v___x_1032_, v_prec_667_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_816_ = v___x_1034_;
goto v___jp_815_;
}
else
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_816_ = v___x_1035_;
goto v___jp_815_;
}
}
case 22:
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(1024u);
v___x_1037_ = lean_nat_dec_le(v___x_1036_, v_prec_667_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_823_ = v___x_1038_;
goto v___jp_822_;
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_823_ = v___x_1039_;
goto v___jp_822_;
}
}
case 23:
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_unsigned_to_nat(1024u);
v___x_1041_ = lean_nat_dec_le(v___x_1040_, v_prec_667_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_830_ = v___x_1042_;
goto v___jp_829_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_830_ = v___x_1043_;
goto v___jp_829_;
}
}
case 24:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(1024u);
v___x_1045_ = lean_nat_dec_le(v___x_1044_, v_prec_667_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_837_ = v___x_1046_;
goto v___jp_836_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_837_ = v___x_1047_;
goto v___jp_836_;
}
}
case 25:
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_unsigned_to_nat(1024u);
v___x_1049_ = lean_nat_dec_le(v___x_1048_, v_prec_667_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_844_ = v___x_1050_;
goto v___jp_843_;
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_844_ = v___x_1051_;
goto v___jp_843_;
}
}
case 26:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(1024u);
v___x_1053_ = lean_nat_dec_le(v___x_1052_, v_prec_667_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_851_ = v___x_1054_;
goto v___jp_850_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_851_ = v___x_1055_;
goto v___jp_850_;
}
}
case 27:
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(1024u);
v___x_1057_ = lean_nat_dec_le(v___x_1056_, v_prec_667_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_858_ = v___x_1058_;
goto v___jp_857_;
}
else
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_858_ = v___x_1059_;
goto v___jp_857_;
}
}
case 28:
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(1024u);
v___x_1061_ = lean_nat_dec_le(v___x_1060_, v_prec_667_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_865_ = v___x_1062_;
goto v___jp_864_;
}
else
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_865_ = v___x_1063_;
goto v___jp_864_;
}
}
case 29:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(1024u);
v___x_1065_ = lean_nat_dec_le(v___x_1064_, v_prec_667_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_872_ = v___x_1066_;
goto v___jp_871_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_872_ = v___x_1067_;
goto v___jp_871_;
}
}
case 30:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_unsigned_to_nat(1024u);
v___x_1069_ = lean_nat_dec_le(v___x_1068_, v_prec_667_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_879_ = v___x_1070_;
goto v___jp_878_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_879_ = v___x_1071_;
goto v___jp_878_;
}
}
case 31:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(1024u);
v___x_1073_ = lean_nat_dec_le(v___x_1072_, v_prec_667_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_886_ = v___x_1074_;
goto v___jp_885_;
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_886_ = v___x_1075_;
goto v___jp_885_;
}
}
case 32:
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_unsigned_to_nat(1024u);
v___x_1077_ = lean_nat_dec_le(v___x_1076_, v_prec_667_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_893_ = v___x_1078_;
goto v___jp_892_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_893_ = v___x_1079_;
goto v___jp_892_;
}
}
case 33:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(1024u);
v___x_1081_ = lean_nat_dec_le(v___x_1080_, v_prec_667_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_900_ = v___x_1082_;
goto v___jp_899_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_900_ = v___x_1083_;
goto v___jp_899_;
}
}
case 34:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_unsigned_to_nat(1024u);
v___x_1085_ = lean_nat_dec_le(v___x_1084_, v_prec_667_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_907_ = v___x_1086_;
goto v___jp_906_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_907_ = v___x_1087_;
goto v___jp_906_;
}
}
case 35:
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_unsigned_to_nat(1024u);
v___x_1089_ = lean_nat_dec_le(v___x_1088_, v_prec_667_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_914_ = v___x_1090_;
goto v___jp_913_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_914_ = v___x_1091_;
goto v___jp_913_;
}
}
case 36:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(1024u);
v___x_1093_ = lean_nat_dec_le(v___x_1092_, v_prec_667_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_921_ = v___x_1094_;
goto v___jp_920_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_921_ = v___x_1095_;
goto v___jp_920_;
}
}
case 37:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_unsigned_to_nat(1024u);
v___x_1097_ = lean_nat_dec_le(v___x_1096_, v_prec_667_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_928_ = v___x_1098_;
goto v___jp_927_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_928_ = v___x_1099_;
goto v___jp_927_;
}
}
case 38:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_unsigned_to_nat(1024u);
v___x_1101_ = lean_nat_dec_le(v___x_1100_, v_prec_667_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_935_ = v___x_1102_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_935_ = v___x_1103_;
goto v___jp_934_;
}
}
default: 
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(1024u);
v___x_1105_ = lean_nat_dec_le(v___x_1104_, v_prec_667_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_942_ = v___x_1106_;
goto v___jp_941_;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_942_ = v___x_1107_;
goto v___jp_941_;
}
}
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_670_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__1));
lean_inc(v___y_669_);
v___x_671_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_671_, 0, v___y_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = 0;
v___x_673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*1, v___x_672_);
v___x_674_ = l_Repr_addAppParen(v___x_673_, v_prec_667_);
return v___x_674_;
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__3));
lean_inc(v___y_676_);
v___x_678_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = 0;
v___x_680_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*1, v___x_679_);
v___x_681_ = l_Repr_addAppParen(v___x_680_, v_prec_667_);
return v___x_681_;
}
v___jp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_684_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__5));
lean_inc(v___y_683_);
v___x_685_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_685_, 0, v___y_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = 0;
v___x_687_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*1, v___x_686_);
v___x_688_ = l_Repr_addAppParen(v___x_687_, v_prec_667_);
return v___x_688_;
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_691_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__7));
lean_inc(v___y_690_);
v___x_692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_692_, 0, v___y_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = 0;
v___x_694_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*1, v___x_693_);
v___x_695_ = l_Repr_addAppParen(v___x_694_, v_prec_667_);
return v___x_695_;
}
v___jp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_698_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__9));
lean_inc(v___y_697_);
v___x_699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_699_, 0, v___y_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = 0;
v___x_701_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*1, v___x_700_);
v___x_702_ = l_Repr_addAppParen(v___x_701_, v_prec_667_);
return v___x_702_;
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_705_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__11));
lean_inc(v___y_704_);
v___x_706_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_706_, 0, v___y_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = 0;
v___x_708_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*1, v___x_707_);
v___x_709_ = l_Repr_addAppParen(v___x_708_, v_prec_667_);
return v___x_709_;
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_712_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__13));
lean_inc(v___y_711_);
v___x_713_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_713_, 0, v___y_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = 0;
v___x_715_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*1, v___x_714_);
v___x_716_ = l_Repr_addAppParen(v___x_715_, v_prec_667_);
return v___x_716_;
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_719_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__15));
lean_inc(v___y_718_);
v___x_720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_720_, 0, v___y_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = 0;
v___x_722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*1, v___x_721_);
v___x_723_ = l_Repr_addAppParen(v___x_722_, v_prec_667_);
return v___x_723_;
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_726_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__17));
lean_inc(v___y_725_);
v___x_727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_727_, 0, v___y_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = 0;
v___x_729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*1, v___x_728_);
v___x_730_ = l_Repr_addAppParen(v___x_729_, v_prec_667_);
return v___x_730_;
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_733_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__19));
lean_inc(v___y_732_);
v___x_734_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_734_, 0, v___y_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = 0;
v___x_736_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*1, v___x_735_);
v___x_737_ = l_Repr_addAppParen(v___x_736_, v_prec_667_);
return v___x_737_;
}
v___jp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_740_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__21));
lean_inc(v___y_739_);
v___x_741_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_741_, 0, v___y_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = 0;
v___x_743_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*1, v___x_742_);
v___x_744_ = l_Repr_addAppParen(v___x_743_, v_prec_667_);
return v___x_744_;
}
v___jp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_747_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__23));
lean_inc(v___y_746_);
v___x_748_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_748_, 0, v___y_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = 0;
v___x_750_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*1, v___x_749_);
v___x_751_ = l_Repr_addAppParen(v___x_750_, v_prec_667_);
return v___x_751_;
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_754_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__25));
lean_inc(v___y_753_);
v___x_755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_755_, 0, v___y_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = 0;
v___x_757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*1, v___x_756_);
v___x_758_ = l_Repr_addAppParen(v___x_757_, v_prec_667_);
return v___x_758_;
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_761_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__27));
lean_inc(v___y_760_);
v___x_762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_762_, 0, v___y_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = 0;
v___x_764_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*1, v___x_763_);
v___x_765_ = l_Repr_addAppParen(v___x_764_, v_prec_667_);
return v___x_765_;
}
v___jp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_768_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__29));
lean_inc(v___y_767_);
v___x_769_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_769_, 0, v___y_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = 0;
v___x_771_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*1, v___x_770_);
v___x_772_ = l_Repr_addAppParen(v___x_771_, v_prec_667_);
return v___x_772_;
}
v___jp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_775_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__31));
lean_inc(v___y_774_);
v___x_776_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_776_, 0, v___y_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = 0;
v___x_778_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set_uint8(v___x_778_, sizeof(void*)*1, v___x_777_);
v___x_779_ = l_Repr_addAppParen(v___x_778_, v_prec_667_);
return v___x_779_;
}
v___jp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_782_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__33));
lean_inc(v___y_781_);
v___x_783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_783_, 0, v___y_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = 0;
v___x_785_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_784_);
v___x_786_ = l_Repr_addAppParen(v___x_785_, v_prec_667_);
return v___x_786_;
}
v___jp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_789_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__35));
lean_inc(v___y_788_);
v___x_790_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_790_, 0, v___y_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = 0;
v___x_792_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*1, v___x_791_);
v___x_793_ = l_Repr_addAppParen(v___x_792_, v_prec_667_);
return v___x_793_;
}
v___jp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_796_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__37));
lean_inc(v___y_795_);
v___x_797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_797_, 0, v___y_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = 0;
v___x_799_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*1, v___x_798_);
v___x_800_ = l_Repr_addAppParen(v___x_799_, v_prec_667_);
return v___x_800_;
}
v___jp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_803_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__39));
lean_inc(v___y_802_);
v___x_804_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_804_, 0, v___y_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = 0;
v___x_806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*1, v___x_805_);
v___x_807_ = l_Repr_addAppParen(v___x_806_, v_prec_667_);
return v___x_807_;
}
v___jp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_810_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__41));
lean_inc(v___y_809_);
v___x_811_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_811_, 0, v___y_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = 0;
v___x_813_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1, v___x_812_);
v___x_814_ = l_Repr_addAppParen(v___x_813_, v_prec_667_);
return v___x_814_;
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_817_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__43));
lean_inc(v___y_816_);
v___x_818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_818_, 0, v___y_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = 0;
v___x_820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*1, v___x_819_);
v___x_821_ = l_Repr_addAppParen(v___x_820_, v_prec_667_);
return v___x_821_;
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_824_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__45));
lean_inc(v___y_823_);
v___x_825_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_825_, 0, v___y_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = 0;
v___x_827_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*1, v___x_826_);
v___x_828_ = l_Repr_addAppParen(v___x_827_, v_prec_667_);
return v___x_828_;
}
v___jp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_831_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__47));
lean_inc(v___y_830_);
v___x_832_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = 0;
v___x_834_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*1, v___x_833_);
v___x_835_ = l_Repr_addAppParen(v___x_834_, v_prec_667_);
return v___x_835_;
}
v___jp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_838_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__49));
lean_inc(v___y_837_);
v___x_839_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_839_, 0, v___y_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = 0;
v___x_841_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*1, v___x_840_);
v___x_842_ = l_Repr_addAppParen(v___x_841_, v_prec_667_);
return v___x_842_;
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_845_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__51));
lean_inc(v___y_844_);
v___x_846_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_846_, 0, v___y_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = 0;
v___x_848_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*1, v___x_847_);
v___x_849_ = l_Repr_addAppParen(v___x_848_, v_prec_667_);
return v___x_849_;
}
v___jp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_852_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__53));
lean_inc(v___y_851_);
v___x_853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_853_, 0, v___y_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = 0;
v___x_855_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*1, v___x_854_);
v___x_856_ = l_Repr_addAppParen(v___x_855_, v_prec_667_);
return v___x_856_;
}
v___jp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_859_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__55));
lean_inc(v___y_858_);
v___x_860_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = 0;
v___x_862_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*1, v___x_861_);
v___x_863_ = l_Repr_addAppParen(v___x_862_, v_prec_667_);
return v___x_863_;
}
v___jp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_866_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__57));
lean_inc(v___y_865_);
v___x_867_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_867_, 0, v___y_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = 0;
v___x_869_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*1, v___x_868_);
v___x_870_ = l_Repr_addAppParen(v___x_869_, v_prec_667_);
return v___x_870_;
}
v___jp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_873_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__59));
lean_inc(v___y_872_);
v___x_874_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_874_, 0, v___y_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = 0;
v___x_876_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1, v___x_875_);
v___x_877_ = l_Repr_addAppParen(v___x_876_, v_prec_667_);
return v___x_877_;
}
v___jp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_880_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__61));
lean_inc(v___y_879_);
v___x_881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_881_, 0, v___y_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = 0;
v___x_883_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1, v___x_882_);
v___x_884_ = l_Repr_addAppParen(v___x_883_, v_prec_667_);
return v___x_884_;
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__63));
lean_inc(v___y_886_);
v___x_888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_888_, 0, v___y_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = 0;
v___x_890_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*1, v___x_889_);
v___x_891_ = l_Repr_addAppParen(v___x_890_, v_prec_667_);
return v___x_891_;
}
v___jp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_894_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__65));
lean_inc(v___y_893_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___y_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = 0;
v___x_897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_896_);
v___x_898_ = l_Repr_addAppParen(v___x_897_, v_prec_667_);
return v___x_898_;
}
v___jp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_901_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__67));
lean_inc(v___y_900_);
v___x_902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_902_, 0, v___y_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = 0;
v___x_904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1, v___x_903_);
v___x_905_ = l_Repr_addAppParen(v___x_904_, v_prec_667_);
return v___x_905_;
}
v___jp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_908_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__69));
lean_inc(v___y_907_);
v___x_909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_909_, 0, v___y_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = 0;
v___x_911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*1, v___x_910_);
v___x_912_ = l_Repr_addAppParen(v___x_911_, v_prec_667_);
return v___x_912_;
}
v___jp_913_:
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__71));
lean_inc(v___y_914_);
v___x_916_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_916_, 0, v___y_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = 0;
v___x_918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*1, v___x_917_);
v___x_919_ = l_Repr_addAppParen(v___x_918_, v_prec_667_);
return v___x_919_;
}
v___jp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_922_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__73));
lean_inc(v___y_921_);
v___x_923_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_923_, 0, v___y_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = 0;
v___x_925_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*1, v___x_924_);
v___x_926_ = l_Repr_addAppParen(v___x_925_, v_prec_667_);
return v___x_926_;
}
v___jp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_929_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__75));
lean_inc(v___y_928_);
v___x_930_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_930_, 0, v___y_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = 0;
v___x_932_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*1, v___x_931_);
v___x_933_ = l_Repr_addAppParen(v___x_932_, v_prec_667_);
return v___x_933_;
}
v___jp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_936_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__77));
lean_inc(v___y_935_);
v___x_937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_937_, 0, v___y_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = 0;
v___x_939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*1, v___x_938_);
v___x_940_ = l_Repr_addAppParen(v___x_939_, v_prec_667_);
return v___x_940_;
}
v___jp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_943_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__79));
lean_inc(v___y_942_);
v___x_944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_944_, 0, v___y_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = 0;
v___x_946_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*1, v___x_945_);
v___x_947_ = l_Repr_addAppParen(v___x_946_, v_prec_667_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr___boxed(lean_object* v_x_1108_, lean_object* v_prec_1109_){
_start:
{
uint8_t v_x_2169__boxed_1110_; lean_object* v_res_1111_; 
v_x_2169__boxed_1110_ = lean_unbox(v_x_1108_);
v_res_1111_ = l_Std_Http_instReprMethod_repr(v_x_2169__boxed_1110_, v_prec_1109_);
lean_dec(v_prec_1109_);
return v_res_1111_;
}
}
static uint8_t _init_l_Std_Http_instInhabitedMethod_default(void){
_start:
{
uint8_t v___x_1114_; 
v___x_1114_ = 0;
return v___x_1114_;
}
}
static uint8_t _init_l_Std_Http_instInhabitedMethod(void){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = 0;
return v___x_1115_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instBEqMethod_beq(uint8_t v_x_1116_, uint8_t v_y_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1118_ = lean_box(v_x_1116_);
v___x_1119_ = lean_obj_tag_nat(v___x_1118_);
lean_dec(v___x_1118_);
v___x_1120_ = lean_box(v_y_1117_);
v___x_1121_ = lean_obj_tag_nat(v___x_1120_);
lean_dec(v___x_1120_);
v___x_1122_ = lean_nat_dec_eq(v___x_1119_, v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqMethod_beq___boxed(lean_object* v_x_1123_, lean_object* v_y_1124_){
_start:
{
uint8_t v_x_24__boxed_1125_; uint8_t v_y_25__boxed_1126_; uint8_t v_res_1127_; lean_object* v_r_1128_; 
v_x_24__boxed_1125_ = lean_unbox(v_x_1123_);
v_y_25__boxed_1126_ = lean_unbox(v_y_1124_);
v_res_1127_ = l_Std_Http_instBEqMethod_beq(v_x_24__boxed_1125_, v_y_25__boxed_1126_);
v_r_1128_ = lean_box(v_res_1127_);
return v_r_1128_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_ofNat(lean_object* v_n_1131_){
_start:
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(19u);
v___x_1133_ = lean_nat_dec_le(v_n_1131_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_unsigned_to_nat(29u);
v___x_1135_ = lean_nat_dec_le(v_n_1131_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(34u);
v___x_1137_ = lean_nat_dec_le(v_n_1131_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(36u);
v___x_1139_ = lean_nat_dec_le(v_n_1131_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_unsigned_to_nat(37u);
v___x_1141_ = lean_nat_dec_le(v_n_1131_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(38u);
v___x_1143_ = lean_nat_dec_le(v_n_1131_, v___x_1142_);
if (v___x_1143_ == 0)
{
uint8_t v___x_1144_; 
v___x_1144_ = 39;
return v___x_1144_;
}
else
{
uint8_t v___x_1145_; 
v___x_1145_ = 38;
return v___x_1145_;
}
}
else
{
uint8_t v___x_1146_; 
v___x_1146_ = 37;
return v___x_1146_;
}
}
else
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_unsigned_to_nat(35u);
v___x_1148_ = lean_nat_dec_le(v_n_1131_, v___x_1147_);
if (v___x_1148_ == 0)
{
uint8_t v___x_1149_; 
v___x_1149_ = 36;
return v___x_1149_;
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = 35;
return v___x_1150_;
}
}
}
else
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_unsigned_to_nat(31u);
v___x_1152_ = lean_nat_dec_le(v_n_1131_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(32u);
v___x_1154_ = lean_nat_dec_le(v_n_1131_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_unsigned_to_nat(33u);
v___x_1156_ = lean_nat_dec_le(v_n_1131_, v___x_1155_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; 
v___x_1157_ = 34;
return v___x_1157_;
}
else
{
uint8_t v___x_1158_; 
v___x_1158_ = 33;
return v___x_1158_;
}
}
else
{
uint8_t v___x_1159_; 
v___x_1159_ = 32;
return v___x_1159_;
}
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(30u);
v___x_1161_ = lean_nat_dec_le(v_n_1131_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = 31;
return v___x_1162_;
}
else
{
uint8_t v___x_1163_; 
v___x_1163_ = 30;
return v___x_1163_;
}
}
}
}
else
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(24u);
v___x_1165_ = lean_nat_dec_le(v_n_1131_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(26u);
v___x_1167_ = lean_nat_dec_le(v_n_1131_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(27u);
v___x_1169_ = lean_nat_dec_le(v_n_1131_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_unsigned_to_nat(28u);
v___x_1171_ = lean_nat_dec_le(v_n_1131_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint8_t v___x_1172_; 
v___x_1172_ = 29;
return v___x_1172_;
}
else
{
uint8_t v___x_1173_; 
v___x_1173_ = 28;
return v___x_1173_;
}
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = 27;
return v___x_1174_;
}
}
else
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(25u);
v___x_1176_ = lean_nat_dec_le(v_n_1131_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; 
v___x_1177_ = 26;
return v___x_1177_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = 25;
return v___x_1178_;
}
}
}
else
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_unsigned_to_nat(21u);
v___x_1180_ = lean_nat_dec_le(v_n_1131_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_unsigned_to_nat(22u);
v___x_1182_ = lean_nat_dec_le(v_n_1131_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(23u);
v___x_1184_ = lean_nat_dec_le(v_n_1131_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint8_t v___x_1185_; 
v___x_1185_ = 24;
return v___x_1185_;
}
else
{
uint8_t v___x_1186_; 
v___x_1186_ = 23;
return v___x_1186_;
}
}
else
{
uint8_t v___x_1187_; 
v___x_1187_ = 22;
return v___x_1187_;
}
}
else
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(20u);
v___x_1189_ = lean_nat_dec_le(v_n_1131_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = 21;
return v___x_1190_;
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = 20;
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_unsigned_to_nat(9u);
v___x_1193_ = lean_nat_dec_le(v_n_1131_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(14u);
v___x_1195_ = lean_nat_dec_le(v_n_1131_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(16u);
v___x_1197_ = lean_nat_dec_le(v_n_1131_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = lean_unsigned_to_nat(17u);
v___x_1199_ = lean_nat_dec_le(v_n_1131_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_unsigned_to_nat(18u);
v___x_1201_ = lean_nat_dec_le(v_n_1131_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
v___x_1202_ = 19;
return v___x_1202_;
}
else
{
uint8_t v___x_1203_; 
v___x_1203_ = 18;
return v___x_1203_;
}
}
else
{
uint8_t v___x_1204_; 
v___x_1204_ = 17;
return v___x_1204_;
}
}
else
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(15u);
v___x_1206_ = lean_nat_dec_le(v_n_1131_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; 
v___x_1207_ = 16;
return v___x_1207_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = 15;
return v___x_1208_;
}
}
}
else
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(11u);
v___x_1210_ = lean_nat_dec_le(v_n_1131_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(12u);
v___x_1212_ = lean_nat_dec_le(v_n_1131_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_unsigned_to_nat(13u);
v___x_1214_ = lean_nat_dec_le(v_n_1131_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; 
v___x_1215_ = 14;
return v___x_1215_;
}
else
{
uint8_t v___x_1216_; 
v___x_1216_ = 13;
return v___x_1216_;
}
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = 12;
return v___x_1217_;
}
}
else
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_unsigned_to_nat(10u);
v___x_1219_ = lean_nat_dec_le(v_n_1131_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint8_t v___x_1220_; 
v___x_1220_ = 11;
return v___x_1220_;
}
else
{
uint8_t v___x_1221_; 
v___x_1221_ = 10;
return v___x_1221_;
}
}
}
}
else
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_unsigned_to_nat(4u);
v___x_1223_ = lean_nat_dec_le(v_n_1131_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_unsigned_to_nat(6u);
v___x_1225_ = lean_nat_dec_le(v_n_1131_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_unsigned_to_nat(7u);
v___x_1227_ = lean_nat_dec_le(v_n_1131_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(8u);
v___x_1229_ = lean_nat_dec_le(v_n_1131_, v___x_1228_);
if (v___x_1229_ == 0)
{
uint8_t v___x_1230_; 
v___x_1230_ = 9;
return v___x_1230_;
}
else
{
uint8_t v___x_1231_; 
v___x_1231_ = 8;
return v___x_1231_;
}
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = 7;
return v___x_1232_;
}
}
else
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(5u);
v___x_1234_ = lean_nat_dec_le(v_n_1131_, v___x_1233_);
if (v___x_1234_ == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = 6;
return v___x_1235_;
}
else
{
uint8_t v___x_1236_; 
v___x_1236_ = 5;
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_dec_le(v_n_1131_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_unsigned_to_nat(2u);
v___x_1240_ = lean_nat_dec_le(v_n_1131_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_unsigned_to_nat(3u);
v___x_1242_ = lean_nat_dec_le(v_n_1131_, v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = 4;
return v___x_1243_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = 3;
return v___x_1244_;
}
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = 2;
return v___x_1245_;
}
}
else
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_nat_dec_le(v_n_1131_, v___x_1246_);
if (v___x_1247_ == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = 1;
return v___x_1248_;
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = 0;
return v___x_1249_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofNat___boxed(lean_object* v_n_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Std_Http_Method_ofNat(v_n_1250_);
lean_dec(v_n_1250_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instDecidableEqMethod(uint8_t v_x_1253_, uint8_t v_y_1254_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1255_ = lean_box(v_x_1253_);
v___x_1256_ = lean_obj_tag_nat(v___x_1255_);
lean_dec(v___x_1255_);
v___x_1257_ = lean_box(v_y_1254_);
v___x_1258_ = lean_obj_tag_nat(v___x_1257_);
lean_dec(v___x_1257_);
v___x_1259_ = lean_nat_dec_eq(v___x_1256_, v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableEqMethod___boxed(lean_object* v_x_1260_, lean_object* v_y_1261_){
_start:
{
uint8_t v_x_23__boxed_1262_; uint8_t v_y_24__boxed_1263_; uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_x_23__boxed_1262_ = lean_unbox(v_x_1260_);
v_y_24__boxed_1263_ = lean_unbox(v_y_1261_);
v_res_1264_ = l_Std_Http_instDecidableEqMethod(v_x_23__boxed_1262_, v_y_24__boxed_1263_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f(lean_object* v_x_1426_){
_start:
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
v___x_1428_ = lean_string_dec_eq(v_x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
v___x_1430_ = lean_string_dec_eq(v_x_1426_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
v___x_1432_ = lean_string_dec_eq(v_x_1426_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
v___x_1434_ = lean_string_dec_eq(v_x_1426_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
v___x_1436_ = lean_string_dec_eq(v_x_1426_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
v___x_1438_ = lean_string_dec_eq(v_x_1426_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; uint8_t v___x_1440_; 
v___x_1439_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
v___x_1440_ = lean_string_dec_eq(v_x_1426_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
v___x_1442_ = lean_string_dec_eq(v_x_1426_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
v___x_1444_ = lean_string_dec_eq(v_x_1426_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
v___x_1446_ = lean_string_dec_eq(v_x_1426_, v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
v___x_1448_ = lean_string_dec_eq(v_x_1426_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1449_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
v___x_1450_ = lean_string_dec_eq(v_x_1426_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
v___x_1452_ = lean_string_dec_eq(v_x_1426_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
v___x_1454_ = lean_string_dec_eq(v_x_1426_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
v___x_1456_ = lean_string_dec_eq(v_x_1426_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
v___x_1458_ = lean_string_dec_eq(v_x_1426_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
v___x_1460_ = lean_string_dec_eq(v_x_1426_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
v___x_1462_ = lean_string_dec_eq(v_x_1426_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
v___x_1464_ = lean_string_dec_eq(v_x_1426_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
v___x_1466_ = lean_string_dec_eq(v_x_1426_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
v___x_1468_ = lean_string_dec_eq(v_x_1426_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
v___x_1470_ = lean_string_dec_eq(v_x_1426_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
v___x_1472_ = lean_string_dec_eq(v_x_1426_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
v___x_1474_ = lean_string_dec_eq(v_x_1426_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
v___x_1476_ = lean_string_dec_eq(v_x_1426_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
v___x_1478_ = lean_string_dec_eq(v_x_1426_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
v___x_1480_ = lean_string_dec_eq(v_x_1426_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
v___x_1482_ = lean_string_dec_eq(v_x_1426_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
v___x_1484_ = lean_string_dec_eq(v_x_1426_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
v___x_1486_ = lean_string_dec_eq(v_x_1426_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
v___x_1488_ = lean_string_dec_eq(v_x_1426_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
v___x_1490_ = lean_string_dec_eq(v_x_1426_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
v___x_1492_ = lean_string_dec_eq(v_x_1426_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
v___x_1494_ = lean_string_dec_eq(v_x_1426_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
v___x_1496_ = lean_string_dec_eq(v_x_1426_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
v___x_1498_ = lean_string_dec_eq(v_x_1426_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
v___x_1500_ = lean_string_dec_eq(v_x_1426_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
v___x_1502_ = lean_string_dec_eq(v_x_1426_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
v___x_1504_ = lean_string_dec_eq(v_x_1426_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
v___x_1506_ = lean_string_dec_eq(v_x_1426_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_box(0);
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__40));
return v___x_1508_;
}
}
else
{
lean_object* v___x_1509_; 
v___x_1509_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__41));
return v___x_1509_;
}
}
else
{
lean_object* v___x_1510_; 
v___x_1510_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__42));
return v___x_1510_;
}
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__43));
return v___x_1511_;
}
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__44));
return v___x_1512_;
}
}
else
{
lean_object* v___x_1513_; 
v___x_1513_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__45));
return v___x_1513_;
}
}
else
{
lean_object* v___x_1514_; 
v___x_1514_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__46));
return v___x_1514_;
}
}
else
{
lean_object* v___x_1515_; 
v___x_1515_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__47));
return v___x_1515_;
}
}
else
{
lean_object* v___x_1516_; 
v___x_1516_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__48));
return v___x_1516_;
}
}
else
{
lean_object* v___x_1517_; 
v___x_1517_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__49));
return v___x_1517_;
}
}
else
{
lean_object* v___x_1518_; 
v___x_1518_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__50));
return v___x_1518_;
}
}
else
{
lean_object* v___x_1519_; 
v___x_1519_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__51));
return v___x_1519_;
}
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__52));
return v___x_1520_;
}
}
else
{
lean_object* v___x_1521_; 
v___x_1521_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__53));
return v___x_1521_;
}
}
else
{
lean_object* v___x_1522_; 
v___x_1522_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__54));
return v___x_1522_;
}
}
else
{
lean_object* v___x_1523_; 
v___x_1523_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__55));
return v___x_1523_;
}
}
else
{
lean_object* v___x_1524_; 
v___x_1524_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__56));
return v___x_1524_;
}
}
else
{
lean_object* v___x_1525_; 
v___x_1525_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__57));
return v___x_1525_;
}
}
else
{
lean_object* v___x_1526_; 
v___x_1526_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__58));
return v___x_1526_;
}
}
else
{
lean_object* v___x_1527_; 
v___x_1527_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__59));
return v___x_1527_;
}
}
else
{
lean_object* v___x_1528_; 
v___x_1528_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__60));
return v___x_1528_;
}
}
else
{
lean_object* v___x_1529_; 
v___x_1529_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__61));
return v___x_1529_;
}
}
else
{
lean_object* v___x_1530_; 
v___x_1530_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__62));
return v___x_1530_;
}
}
else
{
lean_object* v___x_1531_; 
v___x_1531_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__63));
return v___x_1531_;
}
}
else
{
lean_object* v___x_1532_; 
v___x_1532_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__64));
return v___x_1532_;
}
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__65));
return v___x_1533_;
}
}
else
{
lean_object* v___x_1534_; 
v___x_1534_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__66));
return v___x_1534_;
}
}
else
{
lean_object* v___x_1535_; 
v___x_1535_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__67));
return v___x_1535_;
}
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__68));
return v___x_1536_;
}
}
else
{
lean_object* v___x_1537_; 
v___x_1537_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__69));
return v___x_1537_;
}
}
else
{
lean_object* v___x_1538_; 
v___x_1538_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__70));
return v___x_1538_;
}
}
else
{
lean_object* v___x_1539_; 
v___x_1539_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__71));
return v___x_1539_;
}
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__72));
return v___x_1540_;
}
}
else
{
lean_object* v___x_1541_; 
v___x_1541_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__73));
return v___x_1541_;
}
}
else
{
lean_object* v___x_1542_; 
v___x_1542_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__74));
return v___x_1542_;
}
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__75));
return v___x_1543_;
}
}
else
{
lean_object* v___x_1544_; 
v___x_1544_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__76));
return v___x_1544_;
}
}
else
{
lean_object* v___x_1545_; 
v___x_1545_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__77));
return v___x_1545_;
}
}
else
{
lean_object* v___x_1546_; 
v___x_1546_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__78));
return v___x_1546_;
}
}
else
{
lean_object* v___x_1547_; 
v___x_1547_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__79));
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f___boxed(lean_object* v_x_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Std_Http_Method_ofString_x3f(v_x_1548_);
lean_dec_ref(v_x_1548_);
return v_res_1549_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Std_Http_Method_ofString_x21_spec__0(lean_object* v_msg_1550_){
_start:
{
uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1551_ = 0;
v___x_1552_ = lean_box(v___x_1551_);
v___x_1553_ = lean_panic_fn_borrowed(v___x_1552_, v_msg_1550_);
lean_dec(v___x_1552_);
v___x_1554_ = lean_unbox(v___x_1553_);
lean_dec(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Method_ofString_x21_spec__0___boxed(lean_object* v_msg_1555_){
_start:
{
uint8_t v_res_1556_; lean_object* v_r_1557_; 
v_res_1556_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v_msg_1555_);
v_r_1557_ = lean_box(v_res_1556_);
return v_r_1557_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_ofString_x21(lean_object* v_s_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Std_Http_Method_ofString_x3f(v_s_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1563_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__0));
v___x_1564_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__1));
v___x_1565_ = lean_unsigned_to_nat(337u);
v___x_1566_ = lean_unsigned_to_nat(12u);
v___x_1567_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__2));
v___x_1568_ = l_String_quote(v_s_1561_);
v___x_1569_ = lean_string_append(v___x_1567_, v___x_1568_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = l_mkPanicMessageWithDecl(v___x_1563_, v___x_1564_, v___x_1565_, v___x_1566_, v___x_1569_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v___x_1570_);
return v___x_1571_;
}
else
{
lean_object* v_val_1572_; uint8_t v___x_1573_; 
lean_dec_ref(v_s_1561_);
v_val_1572_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1573_ = lean_unbox(v_val_1572_);
lean_dec(v_val_1572_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x21___boxed(lean_object* v_s_1574_){
_start:
{
uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_res_1575_ = l_Std_Http_Method_ofString_x21(v_s_1574_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_isIdempotent(uint8_t v_m_1577_){
_start:
{
uint8_t v___y_1579_; uint8_t v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = 8;
v___x_1589_ = l_Std_Http_instBEqMethod_beq(v_m_1577_, v___x_1588_);
if (v___x_1589_ == 0)
{
uint8_t v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = 9;
v___x_1591_ = l_Std_Http_instBEqMethod_beq(v_m_1577_, v___x_1590_);
v___y_1579_ = v___x_1591_;
goto v___jp_1578_;
}
else
{
v___y_1579_ = v___x_1589_;
goto v___jp_1578_;
}
v___jp_1578_:
{
if (v___y_1579_ == 0)
{
uint8_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = 27;
v___x_1581_ = l_Std_Http_instBEqMethod_beq(v_m_1577_, v___x_1580_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = 7;
v___x_1583_ = l_Std_Http_instBEqMethod_beq(v_m_1577_, v___x_1582_);
if (v___x_1583_ == 0)
{
uint8_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = 20;
v___x_1585_ = l_Std_Http_instBEqMethod_beq(v_m_1577_, v___x_1584_);
if (v___x_1585_ == 0)
{
uint8_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = 32;
v___x_1587_ = l_Std_Http_instBEqMethod_beq(v_m_1577_, v___x_1586_);
return v___x_1587_;
}
else
{
return v___x_1585_;
}
}
else
{
return v___x_1583_;
}
}
else
{
return v___x_1581_;
}
}
else
{
return v___y_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_isIdempotent___boxed(lean_object* v_m_1592_){
_start:
{
uint8_t v_m_boxed_1593_; uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_m_boxed_1593_ = lean_unbox(v_m_1592_);
v_res_1594_ = l_Std_Http_Method_isIdempotent(v_m_boxed_1593_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Method_isSafe(uint8_t v_m_1596_){
_start:
{
uint8_t v___y_1598_; uint8_t v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = 8;
v___x_1604_ = l_Std_Http_instBEqMethod_beq(v_m_1596_, v___x_1603_);
if (v___x_1604_ == 0)
{
uint8_t v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = 9;
v___x_1606_ = l_Std_Http_instBEqMethod_beq(v_m_1596_, v___x_1605_);
v___y_1598_ = v___x_1606_;
goto v___jp_1597_;
}
else
{
v___y_1598_ = v___x_1604_;
goto v___jp_1597_;
}
v___jp_1597_:
{
if (v___y_1598_ == 0)
{
uint8_t v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = 20;
v___x_1600_ = l_Std_Http_instBEqMethod_beq(v_m_1596_, v___x_1599_);
if (v___x_1600_ == 0)
{
uint8_t v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = 32;
v___x_1602_ = l_Std_Http_instBEqMethod_beq(v_m_1596_, v___x_1601_);
return v___x_1602_;
}
else
{
return v___x_1600_;
}
}
else
{
return v___y_1598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_isSafe___boxed(lean_object* v_m_1607_){
_start:
{
uint8_t v_m_boxed_1608_; uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_m_boxed_1608_ = lean_unbox(v_m_1607_);
v_res_1609_ = l_Std_Http_Method_isSafe(v_m_boxed_1608_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0(uint8_t v_x_1611_){
_start:
{
switch(v_x_1611_)
{
case 0:
{
lean_object* v___x_1612_; 
v___x_1612_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
return v___x_1612_;
}
case 1:
{
lean_object* v___x_1613_; 
v___x_1613_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
return v___x_1613_;
}
case 2:
{
lean_object* v___x_1614_; 
v___x_1614_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
return v___x_1614_;
}
case 3:
{
lean_object* v___x_1615_; 
v___x_1615_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
return v___x_1615_;
}
case 4:
{
lean_object* v___x_1616_; 
v___x_1616_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
return v___x_1616_;
}
case 5:
{
lean_object* v___x_1617_; 
v___x_1617_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
return v___x_1617_;
}
case 6:
{
lean_object* v___x_1618_; 
v___x_1618_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
return v___x_1618_;
}
case 7:
{
lean_object* v___x_1619_; 
v___x_1619_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
return v___x_1619_;
}
case 8:
{
lean_object* v___x_1620_; 
v___x_1620_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
return v___x_1620_;
}
case 9:
{
lean_object* v___x_1621_; 
v___x_1621_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
return v___x_1621_;
}
case 10:
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
return v___x_1622_;
}
case 11:
{
lean_object* v___x_1623_; 
v___x_1623_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
return v___x_1623_;
}
case 12:
{
lean_object* v___x_1624_; 
v___x_1624_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
return v___x_1624_;
}
case 13:
{
lean_object* v___x_1625_; 
v___x_1625_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
return v___x_1625_;
}
case 14:
{
lean_object* v___x_1626_; 
v___x_1626_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
return v___x_1626_;
}
case 15:
{
lean_object* v___x_1627_; 
v___x_1627_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
return v___x_1627_;
}
case 16:
{
lean_object* v___x_1628_; 
v___x_1628_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
return v___x_1628_;
}
case 17:
{
lean_object* v___x_1629_; 
v___x_1629_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
return v___x_1629_;
}
case 18:
{
lean_object* v___x_1630_; 
v___x_1630_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
return v___x_1630_;
}
case 19:
{
lean_object* v___x_1631_; 
v___x_1631_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
return v___x_1631_;
}
case 20:
{
lean_object* v___x_1632_; 
v___x_1632_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
return v___x_1632_;
}
case 21:
{
lean_object* v___x_1633_; 
v___x_1633_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
return v___x_1633_;
}
case 22:
{
lean_object* v___x_1634_; 
v___x_1634_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
return v___x_1634_;
}
case 23:
{
lean_object* v___x_1635_; 
v___x_1635_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
return v___x_1635_;
}
case 24:
{
lean_object* v___x_1636_; 
v___x_1636_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
return v___x_1636_;
}
case 25:
{
lean_object* v___x_1637_; 
v___x_1637_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
return v___x_1637_;
}
case 26:
{
lean_object* v___x_1638_; 
v___x_1638_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
return v___x_1638_;
}
case 27:
{
lean_object* v___x_1639_; 
v___x_1639_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
return v___x_1639_;
}
case 28:
{
lean_object* v___x_1640_; 
v___x_1640_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
return v___x_1640_;
}
case 29:
{
lean_object* v___x_1641_; 
v___x_1641_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
return v___x_1641_;
}
case 30:
{
lean_object* v___x_1642_; 
v___x_1642_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
return v___x_1642_;
}
case 31:
{
lean_object* v___x_1643_; 
v___x_1643_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
return v___x_1643_;
}
case 32:
{
lean_object* v___x_1644_; 
v___x_1644_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
return v___x_1644_;
}
case 33:
{
lean_object* v___x_1645_; 
v___x_1645_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
return v___x_1645_;
}
case 34:
{
lean_object* v___x_1646_; 
v___x_1646_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
return v___x_1646_;
}
case 35:
{
lean_object* v___x_1647_; 
v___x_1647_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
return v___x_1647_;
}
case 36:
{
lean_object* v___x_1648_; 
v___x_1648_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
return v___x_1648_;
}
case 37:
{
lean_object* v___x_1649_; 
v___x_1649_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
return v___x_1649_;
}
case 38:
{
lean_object* v___x_1650_; 
v___x_1650_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
return v___x_1650_;
}
default: 
{
lean_object* v___x_1651_; 
v___x_1651_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
return v___x_1651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0___boxed(lean_object* v_x_1652_){
_start:
{
uint8_t v_x_366__boxed_1653_; lean_object* v_res_1654_; 
v_x_366__boxed_1653_ = lean_unbox(v_x_1652_);
v_res_1654_ = l_Std_Http_Method_instToString___lam__0(v_x_366__boxed_1653_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0(lean_object* v_buffer_1657_, uint8_t v___y_1658_){
_start:
{
lean_object* v___y_1660_; 
switch(v___y_1658_)
{
case 0:
{
lean_object* v___x_1674_; 
v___x_1674_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
v___y_1660_ = v___x_1674_;
goto v___jp_1659_;
}
case 1:
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
v___y_1660_ = v___x_1675_;
goto v___jp_1659_;
}
case 2:
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
v___y_1660_ = v___x_1676_;
goto v___jp_1659_;
}
case 3:
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
v___y_1660_ = v___x_1677_;
goto v___jp_1659_;
}
case 4:
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
v___y_1660_ = v___x_1678_;
goto v___jp_1659_;
}
case 5:
{
lean_object* v___x_1679_; 
v___x_1679_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
v___y_1660_ = v___x_1679_;
goto v___jp_1659_;
}
case 6:
{
lean_object* v___x_1680_; 
v___x_1680_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
v___y_1660_ = v___x_1680_;
goto v___jp_1659_;
}
case 7:
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
v___y_1660_ = v___x_1681_;
goto v___jp_1659_;
}
case 8:
{
lean_object* v___x_1682_; 
v___x_1682_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
v___y_1660_ = v___x_1682_;
goto v___jp_1659_;
}
case 9:
{
lean_object* v___x_1683_; 
v___x_1683_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
v___y_1660_ = v___x_1683_;
goto v___jp_1659_;
}
case 10:
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
v___y_1660_ = v___x_1684_;
goto v___jp_1659_;
}
case 11:
{
lean_object* v___x_1685_; 
v___x_1685_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
v___y_1660_ = v___x_1685_;
goto v___jp_1659_;
}
case 12:
{
lean_object* v___x_1686_; 
v___x_1686_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
v___y_1660_ = v___x_1686_;
goto v___jp_1659_;
}
case 13:
{
lean_object* v___x_1687_; 
v___x_1687_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
v___y_1660_ = v___x_1687_;
goto v___jp_1659_;
}
case 14:
{
lean_object* v___x_1688_; 
v___x_1688_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
v___y_1660_ = v___x_1688_;
goto v___jp_1659_;
}
case 15:
{
lean_object* v___x_1689_; 
v___x_1689_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
v___y_1660_ = v___x_1689_;
goto v___jp_1659_;
}
case 16:
{
lean_object* v___x_1690_; 
v___x_1690_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
v___y_1660_ = v___x_1690_;
goto v___jp_1659_;
}
case 17:
{
lean_object* v___x_1691_; 
v___x_1691_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
v___y_1660_ = v___x_1691_;
goto v___jp_1659_;
}
case 18:
{
lean_object* v___x_1692_; 
v___x_1692_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
v___y_1660_ = v___x_1692_;
goto v___jp_1659_;
}
case 19:
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
v___y_1660_ = v___x_1693_;
goto v___jp_1659_;
}
case 20:
{
lean_object* v___x_1694_; 
v___x_1694_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
v___y_1660_ = v___x_1694_;
goto v___jp_1659_;
}
case 21:
{
lean_object* v___x_1695_; 
v___x_1695_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
v___y_1660_ = v___x_1695_;
goto v___jp_1659_;
}
case 22:
{
lean_object* v___x_1696_; 
v___x_1696_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
v___y_1660_ = v___x_1696_;
goto v___jp_1659_;
}
case 23:
{
lean_object* v___x_1697_; 
v___x_1697_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
v___y_1660_ = v___x_1697_;
goto v___jp_1659_;
}
case 24:
{
lean_object* v___x_1698_; 
v___x_1698_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
v___y_1660_ = v___x_1698_;
goto v___jp_1659_;
}
case 25:
{
lean_object* v___x_1699_; 
v___x_1699_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
v___y_1660_ = v___x_1699_;
goto v___jp_1659_;
}
case 26:
{
lean_object* v___x_1700_; 
v___x_1700_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
v___y_1660_ = v___x_1700_;
goto v___jp_1659_;
}
case 27:
{
lean_object* v___x_1701_; 
v___x_1701_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
v___y_1660_ = v___x_1701_;
goto v___jp_1659_;
}
case 28:
{
lean_object* v___x_1702_; 
v___x_1702_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
v___y_1660_ = v___x_1702_;
goto v___jp_1659_;
}
case 29:
{
lean_object* v___x_1703_; 
v___x_1703_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
v___y_1660_ = v___x_1703_;
goto v___jp_1659_;
}
case 30:
{
lean_object* v___x_1704_; 
v___x_1704_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
v___y_1660_ = v___x_1704_;
goto v___jp_1659_;
}
case 31:
{
lean_object* v___x_1705_; 
v___x_1705_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
v___y_1660_ = v___x_1705_;
goto v___jp_1659_;
}
case 32:
{
lean_object* v___x_1706_; 
v___x_1706_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
v___y_1660_ = v___x_1706_;
goto v___jp_1659_;
}
case 33:
{
lean_object* v___x_1707_; 
v___x_1707_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
v___y_1660_ = v___x_1707_;
goto v___jp_1659_;
}
case 34:
{
lean_object* v___x_1708_; 
v___x_1708_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
v___y_1660_ = v___x_1708_;
goto v___jp_1659_;
}
case 35:
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
v___y_1660_ = v___x_1709_;
goto v___jp_1659_;
}
case 36:
{
lean_object* v___x_1710_; 
v___x_1710_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
v___y_1660_ = v___x_1710_;
goto v___jp_1659_;
}
case 37:
{
lean_object* v___x_1711_; 
v___x_1711_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
v___y_1660_ = v___x_1711_;
goto v___jp_1659_;
}
case 38:
{
lean_object* v___x_1712_; 
v___x_1712_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
v___y_1660_ = v___x_1712_;
goto v___jp_1659_;
}
default: 
{
lean_object* v___x_1713_; 
v___x_1713_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
v___y_1660_ = v___x_1713_;
goto v___jp_1659_;
}
}
v___jp_1659_:
{
lean_object* v_data_1661_; lean_object* v_size_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1673_; 
v_data_1661_ = lean_ctor_get(v_buffer_1657_, 0);
v_size_1662_ = lean_ctor_get(v_buffer_1657_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_buffer_1657_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1664_ = v_buffer_1657_;
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_size_1662_);
lean_inc(v_data_1661_);
lean_dec(v_buffer_1657_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1666_ = lean_string_to_utf8(v___y_1660_);
lean_inc_ref(v___x_1666_);
v___x_1667_ = lean_array_push(v_data_1661_, v___x_1666_);
v___x_1668_ = lean_byte_array_size(v___x_1666_);
lean_dec_ref(v___x_1666_);
v___x_1669_ = lean_nat_add(v_size_1662_, v___x_1668_);
lean_dec(v_size_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1669_);
lean_ctor_set(v___x_1664_, 0, v___x_1667_);
v___x_1671_ = v___x_1664_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0___boxed(lean_object* v_buffer_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v___y_192__boxed_1716_; lean_object* v_res_1717_; 
v___y_192__boxed_1716_ = lean_unbox(v___y_1715_);
v_res_1717_ = l_Std_Http_Method_instEncodeV11___lam__0(v_buffer_1714_, v___y_192__boxed_1716_);
return v_res_1717_;
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
