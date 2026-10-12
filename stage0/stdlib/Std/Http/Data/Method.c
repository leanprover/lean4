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
lean_object* l_Std_Http_Method_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Http_Method_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Http_Method_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Http_Method_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Http_Method_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Http_Method_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Http_Method_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Http_Method_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Http_Method_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg(lean_object* v_acl_24_){
_start:
{
lean_inc(v_acl_24_);
return v_acl_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___redArg___boxed(lean_object* v_acl_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Http_Method_acl_elim___redArg(v_acl_25_);
lean_dec(v_acl_25_);
return v_res_26_;
}
}
lean_object* l_Std_Http_Method_acl_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_acl_30_){
_start:
{
lean_inc(v_acl_30_);
return v_acl_30_;
}
}
LEAN_EXPORT void l_Std_Http_Method_acl_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_acl_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Http_Method_acl_elim(lean_box(0), v_t_28_, lean_box(0), v_acl_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_acl_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_acl_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Http_Method_acl_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_acl_35_);
lean_dec(v_acl_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg(lean_object* v_baselineControl_38_){
_start:
{
lean_inc(v_baselineControl_38_);
return v_baselineControl_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___redArg___boxed(lean_object* v_baselineControl_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Http_Method_baselineControl_elim___redArg(v_baselineControl_39_);
lean_dec(v_baselineControl_39_);
return v_res_40_;
}
}
lean_object* l_Std_Http_Method_baselineControl_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_baselineControl_44_){
_start:
{
lean_inc(v_baselineControl_44_);
return v_baselineControl_44_;
}
}
LEAN_EXPORT void l_Std_Http_Method_baselineControl_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_baselineControl_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Http_Method_baselineControl_elim(lean_box(0), v_t_42_, lean_box(0), v_baselineControl_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_baselineControl_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_baselineControl_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Http_Method_baselineControl_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_baselineControl_49_);
lean_dec(v_baselineControl_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg(lean_object* v_bind_52_){
_start:
{
lean_inc(v_bind_52_);
return v_bind_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___redArg___boxed(lean_object* v_bind_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Http_Method_bind_elim___redArg(v_bind_53_);
lean_dec(v_bind_53_);
return v_res_54_;
}
}
lean_object* l_Std_Http_Method_bind_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_bind_58_){
_start:
{
lean_inc(v_bind_58_);
return v_bind_58_;
}
}
LEAN_EXPORT void l_Std_Http_Method_bind_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_bind_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Std_Http_Method_bind_elim(lean_box(0), v_t_56_, lean_box(0), v_bind_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_bind_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_bind_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Std_Http_Method_bind_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_bind_63_);
lean_dec(v_bind_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg(lean_object* v_checkin_66_){
_start:
{
lean_inc(v_checkin_66_);
return v_checkin_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___redArg___boxed(lean_object* v_checkin_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Http_Method_checkin_elim___redArg(v_checkin_67_);
lean_dec(v_checkin_67_);
return v_res_68_;
}
}
lean_object* l_Std_Http_Method_checkin_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_checkin_72_){
_start:
{
lean_inc(v_checkin_72_);
return v_checkin_72_;
}
}
LEAN_EXPORT void l_Std_Http_Method_checkin_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_checkin_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Std_Http_Method_checkin_elim(lean_box(0), v_t_70_, lean_box(0), v_checkin_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkin_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_checkin_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Std_Http_Method_checkin_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_checkin_77_);
lean_dec(v_checkin_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg(lean_object* v_checkout_80_){
_start:
{
lean_inc(v_checkout_80_);
return v_checkout_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___redArg___boxed(lean_object* v_checkout_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_Http_Method_checkout_elim___redArg(v_checkout_81_);
lean_dec(v_checkout_81_);
return v_res_82_;
}
}
lean_object* l_Std_Http_Method_checkout_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_checkout_86_){
_start:
{
lean_inc(v_checkout_86_);
return v_checkout_86_;
}
}
LEAN_EXPORT void l_Std_Http_Method_checkout_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_84_ = stack[1].m_num;
lean_object* v_checkout_86_ = stack[3].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Std_Http_Method_checkout_elim(lean_box(0), v_t_84_, lean_box(0), v_checkout_86_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_checkout_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_checkout_91_){
_start:
{
uint8_t v_t_boxed_92_; lean_object* v_res_93_; 
v_t_boxed_92_ = lean_unbox(v_t_89_);
v_res_93_ = l_Std_Http_Method_checkout_elim(v_motive_88_, v_t_boxed_92_, v_h_90_, v_checkout_91_);
lean_dec(v_checkout_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg(lean_object* v_connect_94_){
_start:
{
lean_inc(v_connect_94_);
return v_connect_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___redArg___boxed(lean_object* v_connect_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Http_Method_connect_elim___redArg(v_connect_95_);
lean_dec(v_connect_95_);
return v_res_96_;
}
}
lean_object* l_Std_Http_Method_connect_elim(lean_object* v_motive_97_, uint8_t v_t_98_, lean_object* v_h_99_, lean_object* v_connect_100_){
_start:
{
lean_inc(v_connect_100_);
return v_connect_100_;
}
}
LEAN_EXPORT void l_Std_Http_Method_connect_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_98_ = stack[1].m_num;
lean_object* v_connect_100_ = stack[3].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Std_Http_Method_connect_elim(lean_box(0), v_t_98_, lean_box(0), v_connect_100_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_connect_elim___boxed(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_connect_105_){
_start:
{
uint8_t v_t_boxed_106_; lean_object* v_res_107_; 
v_t_boxed_106_ = lean_unbox(v_t_103_);
v_res_107_ = l_Std_Http_Method_connect_elim(v_motive_102_, v_t_boxed_106_, v_h_104_, v_connect_105_);
lean_dec(v_connect_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg(lean_object* v_copy_108_){
_start:
{
lean_inc(v_copy_108_);
return v_copy_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___redArg___boxed(lean_object* v_copy_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Http_Method_copy_elim___redArg(v_copy_109_);
lean_dec(v_copy_109_);
return v_res_110_;
}
}
lean_object* l_Std_Http_Method_copy_elim(lean_object* v_motive_111_, uint8_t v_t_112_, lean_object* v_h_113_, lean_object* v_copy_114_){
_start:
{
lean_inc(v_copy_114_);
return v_copy_114_;
}
}
LEAN_EXPORT void l_Std_Http_Method_copy_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_112_ = stack[1].m_num;
lean_object* v_copy_114_ = stack[3].m_obj;
lean_object* v_res_115_;
v_res_115_ = l_Std_Http_Method_copy_elim(lean_box(0), v_t_112_, lean_box(0), v_copy_114_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_copy_elim___boxed(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_copy_119_){
_start:
{
uint8_t v_t_boxed_120_; lean_object* v_res_121_; 
v_t_boxed_120_ = lean_unbox(v_t_117_);
v_res_121_ = l_Std_Http_Method_copy_elim(v_motive_116_, v_t_boxed_120_, v_h_118_, v_copy_119_);
lean_dec(v_copy_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg(lean_object* v_delete_122_){
_start:
{
lean_inc(v_delete_122_);
return v_delete_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___redArg___boxed(lean_object* v_delete_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Http_Method_delete_elim___redArg(v_delete_123_);
lean_dec(v_delete_123_);
return v_res_124_;
}
}
lean_object* l_Std_Http_Method_delete_elim(lean_object* v_motive_125_, uint8_t v_t_126_, lean_object* v_h_127_, lean_object* v_delete_128_){
_start:
{
lean_inc(v_delete_128_);
return v_delete_128_;
}
}
LEAN_EXPORT void l_Std_Http_Method_delete_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_126_ = stack[1].m_num;
lean_object* v_delete_128_ = stack[3].m_obj;
lean_object* v_res_129_;
v_res_129_ = l_Std_Http_Method_delete_elim(lean_box(0), v_t_126_, lean_box(0), v_delete_128_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_delete_elim___boxed(lean_object* v_motive_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_delete_133_){
_start:
{
uint8_t v_t_boxed_134_; lean_object* v_res_135_; 
v_t_boxed_134_ = lean_unbox(v_t_131_);
v_res_135_ = l_Std_Http_Method_delete_elim(v_motive_130_, v_t_boxed_134_, v_h_132_, v_delete_133_);
lean_dec(v_delete_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg(lean_object* v_get_136_){
_start:
{
lean_inc(v_get_136_);
return v_get_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___redArg___boxed(lean_object* v_get_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Http_Method_get_elim___redArg(v_get_137_);
lean_dec(v_get_137_);
return v_res_138_;
}
}
lean_object* l_Std_Http_Method_get_elim(lean_object* v_motive_139_, uint8_t v_t_140_, lean_object* v_h_141_, lean_object* v_get_142_){
_start:
{
lean_inc(v_get_142_);
return v_get_142_;
}
}
LEAN_EXPORT void l_Std_Http_Method_get_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_140_ = stack[1].m_num;
lean_object* v_get_142_ = stack[3].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Std_Http_Method_get_elim(lean_box(0), v_t_140_, lean_box(0), v_get_142_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_get_elim___boxed(lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_get_147_){
_start:
{
uint8_t v_t_boxed_148_; lean_object* v_res_149_; 
v_t_boxed_148_ = lean_unbox(v_t_145_);
v_res_149_ = l_Std_Http_Method_get_elim(v_motive_144_, v_t_boxed_148_, v_h_146_, v_get_147_);
lean_dec(v_get_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg(lean_object* v_head_150_){
_start:
{
lean_inc(v_head_150_);
return v_head_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___redArg___boxed(lean_object* v_head_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_Http_Method_head_elim___redArg(v_head_151_);
lean_dec(v_head_151_);
return v_res_152_;
}
}
lean_object* l_Std_Http_Method_head_elim(lean_object* v_motive_153_, uint8_t v_t_154_, lean_object* v_h_155_, lean_object* v_head_156_){
_start:
{
lean_inc(v_head_156_);
return v_head_156_;
}
}
LEAN_EXPORT void l_Std_Http_Method_head_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_154_ = stack[1].m_num;
lean_object* v_head_156_ = stack[3].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Std_Http_Method_head_elim(lean_box(0), v_t_154_, lean_box(0), v_head_156_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_head_elim___boxed(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_head_161_){
_start:
{
uint8_t v_t_boxed_162_; lean_object* v_res_163_; 
v_t_boxed_162_ = lean_unbox(v_t_159_);
v_res_163_ = l_Std_Http_Method_head_elim(v_motive_158_, v_t_boxed_162_, v_h_160_, v_head_161_);
lean_dec(v_head_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg(lean_object* v_label_164_){
_start:
{
lean_inc(v_label_164_);
return v_label_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___redArg___boxed(lean_object* v_label_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Http_Method_label_elim___redArg(v_label_165_);
lean_dec(v_label_165_);
return v_res_166_;
}
}
lean_object* l_Std_Http_Method_label_elim(lean_object* v_motive_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_label_170_){
_start:
{
lean_inc(v_label_170_);
return v_label_170_;
}
}
LEAN_EXPORT void l_Std_Http_Method_label_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_168_ = stack[1].m_num;
lean_object* v_label_170_ = stack[3].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Std_Http_Method_label_elim(lean_box(0), v_t_168_, lean_box(0), v_label_170_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_label_elim___boxed(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_label_175_){
_start:
{
uint8_t v_t_boxed_176_; lean_object* v_res_177_; 
v_t_boxed_176_ = lean_unbox(v_t_173_);
v_res_177_ = l_Std_Http_Method_label_elim(v_motive_172_, v_t_boxed_176_, v_h_174_, v_label_175_);
lean_dec(v_label_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg(lean_object* v_link_178_){
_start:
{
lean_inc(v_link_178_);
return v_link_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___redArg___boxed(lean_object* v_link_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Http_Method_link_elim___redArg(v_link_179_);
lean_dec(v_link_179_);
return v_res_180_;
}
}
lean_object* l_Std_Http_Method_link_elim(lean_object* v_motive_181_, uint8_t v_t_182_, lean_object* v_h_183_, lean_object* v_link_184_){
_start:
{
lean_inc(v_link_184_);
return v_link_184_;
}
}
LEAN_EXPORT void l_Std_Http_Method_link_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_182_ = stack[1].m_num;
lean_object* v_link_184_ = stack[3].m_obj;
lean_object* v_res_185_;
v_res_185_ = l_Std_Http_Method_link_elim(lean_box(0), v_t_182_, lean_box(0), v_link_184_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_link_elim___boxed(lean_object* v_motive_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_link_189_){
_start:
{
uint8_t v_t_boxed_190_; lean_object* v_res_191_; 
v_t_boxed_190_ = lean_unbox(v_t_187_);
v_res_191_ = l_Std_Http_Method_link_elim(v_motive_186_, v_t_boxed_190_, v_h_188_, v_link_189_);
lean_dec(v_link_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg(lean_object* v_lock_192_){
_start:
{
lean_inc(v_lock_192_);
return v_lock_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___redArg___boxed(lean_object* v_lock_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Http_Method_lock_elim___redArg(v_lock_193_);
lean_dec(v_lock_193_);
return v_res_194_;
}
}
lean_object* l_Std_Http_Method_lock_elim(lean_object* v_motive_195_, uint8_t v_t_196_, lean_object* v_h_197_, lean_object* v_lock_198_){
_start:
{
lean_inc(v_lock_198_);
return v_lock_198_;
}
}
LEAN_EXPORT void l_Std_Http_Method_lock_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_196_ = stack[1].m_num;
lean_object* v_lock_198_ = stack[3].m_obj;
lean_object* v_res_199_;
v_res_199_ = l_Std_Http_Method_lock_elim(lean_box(0), v_t_196_, lean_box(0), v_lock_198_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_lock_elim___boxed(lean_object* v_motive_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_lock_203_){
_start:
{
uint8_t v_t_boxed_204_; lean_object* v_res_205_; 
v_t_boxed_204_ = lean_unbox(v_t_201_);
v_res_205_ = l_Std_Http_Method_lock_elim(v_motive_200_, v_t_boxed_204_, v_h_202_, v_lock_203_);
lean_dec(v_lock_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg(lean_object* v_merge_206_){
_start:
{
lean_inc(v_merge_206_);
return v_merge_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___redArg___boxed(lean_object* v_merge_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Http_Method_merge_elim___redArg(v_merge_207_);
lean_dec(v_merge_207_);
return v_res_208_;
}
}
lean_object* l_Std_Http_Method_merge_elim(lean_object* v_motive_209_, uint8_t v_t_210_, lean_object* v_h_211_, lean_object* v_merge_212_){
_start:
{
lean_inc(v_merge_212_);
return v_merge_212_;
}
}
LEAN_EXPORT void l_Std_Http_Method_merge_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_210_ = stack[1].m_num;
lean_object* v_merge_212_ = stack[3].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Std_Http_Method_merge_elim(lean_box(0), v_t_210_, lean_box(0), v_merge_212_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_merge_elim___boxed(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_merge_217_){
_start:
{
uint8_t v_t_boxed_218_; lean_object* v_res_219_; 
v_t_boxed_218_ = lean_unbox(v_t_215_);
v_res_219_ = l_Std_Http_Method_merge_elim(v_motive_214_, v_t_boxed_218_, v_h_216_, v_merge_217_);
lean_dec(v_merge_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg(lean_object* v_mkactivity_220_){
_start:
{
lean_inc(v_mkactivity_220_);
return v_mkactivity_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___redArg___boxed(lean_object* v_mkactivity_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Http_Method_mkactivity_elim___redArg(v_mkactivity_221_);
lean_dec(v_mkactivity_221_);
return v_res_222_;
}
}
lean_object* l_Std_Http_Method_mkactivity_elim(lean_object* v_motive_223_, uint8_t v_t_224_, lean_object* v_h_225_, lean_object* v_mkactivity_226_){
_start:
{
lean_inc(v_mkactivity_226_);
return v_mkactivity_226_;
}
}
LEAN_EXPORT void l_Std_Http_Method_mkactivity_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_224_ = stack[1].m_num;
lean_object* v_mkactivity_226_ = stack[3].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Std_Http_Method_mkactivity_elim(lean_box(0), v_t_224_, lean_box(0), v_mkactivity_226_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkactivity_elim___boxed(lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_mkactivity_231_){
_start:
{
uint8_t v_t_boxed_232_; lean_object* v_res_233_; 
v_t_boxed_232_ = lean_unbox(v_t_229_);
v_res_233_ = l_Std_Http_Method_mkactivity_elim(v_motive_228_, v_t_boxed_232_, v_h_230_, v_mkactivity_231_);
lean_dec(v_mkactivity_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg(lean_object* v_mkcalendar_234_){
_start:
{
lean_inc(v_mkcalendar_234_);
return v_mkcalendar_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___redArg___boxed(lean_object* v_mkcalendar_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Http_Method_mkcalendar_elim___redArg(v_mkcalendar_235_);
lean_dec(v_mkcalendar_235_);
return v_res_236_;
}
}
lean_object* l_Std_Http_Method_mkcalendar_elim(lean_object* v_motive_237_, uint8_t v_t_238_, lean_object* v_h_239_, lean_object* v_mkcalendar_240_){
_start:
{
lean_inc(v_mkcalendar_240_);
return v_mkcalendar_240_;
}
}
LEAN_EXPORT void l_Std_Http_Method_mkcalendar_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_238_ = stack[1].m_num;
lean_object* v_mkcalendar_240_ = stack[3].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Std_Http_Method_mkcalendar_elim(lean_box(0), v_t_238_, lean_box(0), v_mkcalendar_240_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcalendar_elim___boxed(lean_object* v_motive_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_mkcalendar_245_){
_start:
{
uint8_t v_t_boxed_246_; lean_object* v_res_247_; 
v_t_boxed_246_ = lean_unbox(v_t_243_);
v_res_247_ = l_Std_Http_Method_mkcalendar_elim(v_motive_242_, v_t_boxed_246_, v_h_244_, v_mkcalendar_245_);
lean_dec(v_mkcalendar_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg(lean_object* v_mkcol_248_){
_start:
{
lean_inc(v_mkcol_248_);
return v_mkcol_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___redArg___boxed(lean_object* v_mkcol_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_Http_Method_mkcol_elim___redArg(v_mkcol_249_);
lean_dec(v_mkcol_249_);
return v_res_250_;
}
}
lean_object* l_Std_Http_Method_mkcol_elim(lean_object* v_motive_251_, uint8_t v_t_252_, lean_object* v_h_253_, lean_object* v_mkcol_254_){
_start:
{
lean_inc(v_mkcol_254_);
return v_mkcol_254_;
}
}
LEAN_EXPORT void l_Std_Http_Method_mkcol_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_252_ = stack[1].m_num;
lean_object* v_mkcol_254_ = stack[3].m_obj;
lean_object* v_res_255_;
v_res_255_ = l_Std_Http_Method_mkcol_elim(lean_box(0), v_t_252_, lean_box(0), v_mkcol_254_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkcol_elim___boxed(lean_object* v_motive_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_mkcol_259_){
_start:
{
uint8_t v_t_boxed_260_; lean_object* v_res_261_; 
v_t_boxed_260_ = lean_unbox(v_t_257_);
v_res_261_ = l_Std_Http_Method_mkcol_elim(v_motive_256_, v_t_boxed_260_, v_h_258_, v_mkcol_259_);
lean_dec(v_mkcol_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg(lean_object* v_mkredirectref_262_){
_start:
{
lean_inc(v_mkredirectref_262_);
return v_mkredirectref_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___redArg___boxed(lean_object* v_mkredirectref_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Http_Method_mkredirectref_elim___redArg(v_mkredirectref_263_);
lean_dec(v_mkredirectref_263_);
return v_res_264_;
}
}
lean_object* l_Std_Http_Method_mkredirectref_elim(lean_object* v_motive_265_, uint8_t v_t_266_, lean_object* v_h_267_, lean_object* v_mkredirectref_268_){
_start:
{
lean_inc(v_mkredirectref_268_);
return v_mkredirectref_268_;
}
}
LEAN_EXPORT void l_Std_Http_Method_mkredirectref_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_266_ = stack[1].m_num;
lean_object* v_mkredirectref_268_ = stack[3].m_obj;
lean_object* v_res_269_;
v_res_269_ = l_Std_Http_Method_mkredirectref_elim(lean_box(0), v_t_266_, lean_box(0), v_mkredirectref_268_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkredirectref_elim___boxed(lean_object* v_motive_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_mkredirectref_273_){
_start:
{
uint8_t v_t_boxed_274_; lean_object* v_res_275_; 
v_t_boxed_274_ = lean_unbox(v_t_271_);
v_res_275_ = l_Std_Http_Method_mkredirectref_elim(v_motive_270_, v_t_boxed_274_, v_h_272_, v_mkredirectref_273_);
lean_dec(v_mkredirectref_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg(lean_object* v_mkworkspace_276_){
_start:
{
lean_inc(v_mkworkspace_276_);
return v_mkworkspace_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___redArg___boxed(lean_object* v_mkworkspace_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Std_Http_Method_mkworkspace_elim___redArg(v_mkworkspace_277_);
lean_dec(v_mkworkspace_277_);
return v_res_278_;
}
}
lean_object* l_Std_Http_Method_mkworkspace_elim(lean_object* v_motive_279_, uint8_t v_t_280_, lean_object* v_h_281_, lean_object* v_mkworkspace_282_){
_start:
{
lean_inc(v_mkworkspace_282_);
return v_mkworkspace_282_;
}
}
LEAN_EXPORT void l_Std_Http_Method_mkworkspace_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_280_ = stack[1].m_num;
lean_object* v_mkworkspace_282_ = stack[3].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_Std_Http_Method_mkworkspace_elim(lean_box(0), v_t_280_, lean_box(0), v_mkworkspace_282_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_mkworkspace_elim___boxed(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_mkworkspace_287_){
_start:
{
uint8_t v_t_boxed_288_; lean_object* v_res_289_; 
v_t_boxed_288_ = lean_unbox(v_t_285_);
v_res_289_ = l_Std_Http_Method_mkworkspace_elim(v_motive_284_, v_t_boxed_288_, v_h_286_, v_mkworkspace_287_);
lean_dec(v_mkworkspace_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg(lean_object* v_move_290_){
_start:
{
lean_inc(v_move_290_);
return v_move_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___redArg___boxed(lean_object* v_move_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_Http_Method_move_elim___redArg(v_move_291_);
lean_dec(v_move_291_);
return v_res_292_;
}
}
lean_object* l_Std_Http_Method_move_elim(lean_object* v_motive_293_, uint8_t v_t_294_, lean_object* v_h_295_, lean_object* v_move_296_){
_start:
{
lean_inc(v_move_296_);
return v_move_296_;
}
}
LEAN_EXPORT void l_Std_Http_Method_move_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_294_ = stack[1].m_num;
lean_object* v_move_296_ = stack[3].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Std_Http_Method_move_elim(lean_box(0), v_t_294_, lean_box(0), v_move_296_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_move_elim___boxed(lean_object* v_motive_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_move_301_){
_start:
{
uint8_t v_t_boxed_302_; lean_object* v_res_303_; 
v_t_boxed_302_ = lean_unbox(v_t_299_);
v_res_303_ = l_Std_Http_Method_move_elim(v_motive_298_, v_t_boxed_302_, v_h_300_, v_move_301_);
lean_dec(v_move_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg(lean_object* v_options_304_){
_start:
{
lean_inc(v_options_304_);
return v_options_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___redArg___boxed(lean_object* v_options_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Http_Method_options_elim___redArg(v_options_305_);
lean_dec(v_options_305_);
return v_res_306_;
}
}
lean_object* l_Std_Http_Method_options_elim(lean_object* v_motive_307_, uint8_t v_t_308_, lean_object* v_h_309_, lean_object* v_options_310_){
_start:
{
lean_inc(v_options_310_);
return v_options_310_;
}
}
LEAN_EXPORT void l_Std_Http_Method_options_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_308_ = stack[1].m_num;
lean_object* v_options_310_ = stack[3].m_obj;
lean_object* v_res_311_;
v_res_311_ = l_Std_Http_Method_options_elim(lean_box(0), v_t_308_, lean_box(0), v_options_310_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_options_elim___boxed(lean_object* v_motive_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_options_315_){
_start:
{
uint8_t v_t_boxed_316_; lean_object* v_res_317_; 
v_t_boxed_316_ = lean_unbox(v_t_313_);
v_res_317_ = l_Std_Http_Method_options_elim(v_motive_312_, v_t_boxed_316_, v_h_314_, v_options_315_);
lean_dec(v_options_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg(lean_object* v_orderpatch_318_){
_start:
{
lean_inc(v_orderpatch_318_);
return v_orderpatch_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___redArg___boxed(lean_object* v_orderpatch_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Http_Method_orderpatch_elim___redArg(v_orderpatch_319_);
lean_dec(v_orderpatch_319_);
return v_res_320_;
}
}
lean_object* l_Std_Http_Method_orderpatch_elim(lean_object* v_motive_321_, uint8_t v_t_322_, lean_object* v_h_323_, lean_object* v_orderpatch_324_){
_start:
{
lean_inc(v_orderpatch_324_);
return v_orderpatch_324_;
}
}
LEAN_EXPORT void l_Std_Http_Method_orderpatch_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_322_ = stack[1].m_num;
lean_object* v_orderpatch_324_ = stack[3].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Std_Http_Method_orderpatch_elim(lean_box(0), v_t_322_, lean_box(0), v_orderpatch_324_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_orderpatch_elim___boxed(lean_object* v_motive_326_, lean_object* v_t_327_, lean_object* v_h_328_, lean_object* v_orderpatch_329_){
_start:
{
uint8_t v_t_boxed_330_; lean_object* v_res_331_; 
v_t_boxed_330_ = lean_unbox(v_t_327_);
v_res_331_ = l_Std_Http_Method_orderpatch_elim(v_motive_326_, v_t_boxed_330_, v_h_328_, v_orderpatch_329_);
lean_dec(v_orderpatch_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg(lean_object* v_patch_332_){
_start:
{
lean_inc(v_patch_332_);
return v_patch_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___redArg___boxed(lean_object* v_patch_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_Http_Method_patch_elim___redArg(v_patch_333_);
lean_dec(v_patch_333_);
return v_res_334_;
}
}
lean_object* l_Std_Http_Method_patch_elim(lean_object* v_motive_335_, uint8_t v_t_336_, lean_object* v_h_337_, lean_object* v_patch_338_){
_start:
{
lean_inc(v_patch_338_);
return v_patch_338_;
}
}
LEAN_EXPORT void l_Std_Http_Method_patch_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_336_ = stack[1].m_num;
lean_object* v_patch_338_ = stack[3].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_Std_Http_Method_patch_elim(lean_box(0), v_t_336_, lean_box(0), v_patch_338_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_patch_elim___boxed(lean_object* v_motive_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_patch_343_){
_start:
{
uint8_t v_t_boxed_344_; lean_object* v_res_345_; 
v_t_boxed_344_ = lean_unbox(v_t_341_);
v_res_345_ = l_Std_Http_Method_patch_elim(v_motive_340_, v_t_boxed_344_, v_h_342_, v_patch_343_);
lean_dec(v_patch_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg(lean_object* v_post_346_){
_start:
{
lean_inc(v_post_346_);
return v_post_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___redArg___boxed(lean_object* v_post_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Http_Method_post_elim___redArg(v_post_347_);
lean_dec(v_post_347_);
return v_res_348_;
}
}
lean_object* l_Std_Http_Method_post_elim(lean_object* v_motive_349_, uint8_t v_t_350_, lean_object* v_h_351_, lean_object* v_post_352_){
_start:
{
lean_inc(v_post_352_);
return v_post_352_;
}
}
LEAN_EXPORT void l_Std_Http_Method_post_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_350_ = stack[1].m_num;
lean_object* v_post_352_ = stack[3].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Std_Http_Method_post_elim(lean_box(0), v_t_350_, lean_box(0), v_post_352_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_post_elim___boxed(lean_object* v_motive_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_post_357_){
_start:
{
uint8_t v_t_boxed_358_; lean_object* v_res_359_; 
v_t_boxed_358_ = lean_unbox(v_t_355_);
v_res_359_ = l_Std_Http_Method_post_elim(v_motive_354_, v_t_boxed_358_, v_h_356_, v_post_357_);
lean_dec(v_post_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg(lean_object* v_pri_360_){
_start:
{
lean_inc(v_pri_360_);
return v_pri_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___redArg___boxed(lean_object* v_pri_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Http_Method_pri_elim___redArg(v_pri_361_);
lean_dec(v_pri_361_);
return v_res_362_;
}
}
lean_object* l_Std_Http_Method_pri_elim(lean_object* v_motive_363_, uint8_t v_t_364_, lean_object* v_h_365_, lean_object* v_pri_366_){
_start:
{
lean_inc(v_pri_366_);
return v_pri_366_;
}
}
LEAN_EXPORT void l_Std_Http_Method_pri_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_364_ = stack[1].m_num;
lean_object* v_pri_366_ = stack[3].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Std_Http_Method_pri_elim(lean_box(0), v_t_364_, lean_box(0), v_pri_366_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_pri_elim___boxed(lean_object* v_motive_368_, lean_object* v_t_369_, lean_object* v_h_370_, lean_object* v_pri_371_){
_start:
{
uint8_t v_t_boxed_372_; lean_object* v_res_373_; 
v_t_boxed_372_ = lean_unbox(v_t_369_);
v_res_373_ = l_Std_Http_Method_pri_elim(v_motive_368_, v_t_boxed_372_, v_h_370_, v_pri_371_);
lean_dec(v_pri_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg(lean_object* v_propfind_374_){
_start:
{
lean_inc(v_propfind_374_);
return v_propfind_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___redArg___boxed(lean_object* v_propfind_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Http_Method_propfind_elim___redArg(v_propfind_375_);
lean_dec(v_propfind_375_);
return v_res_376_;
}
}
lean_object* l_Std_Http_Method_propfind_elim(lean_object* v_motive_377_, uint8_t v_t_378_, lean_object* v_h_379_, lean_object* v_propfind_380_){
_start:
{
lean_inc(v_propfind_380_);
return v_propfind_380_;
}
}
LEAN_EXPORT void l_Std_Http_Method_propfind_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_378_ = stack[1].m_num;
lean_object* v_propfind_380_ = stack[3].m_obj;
lean_object* v_res_381_;
v_res_381_ = l_Std_Http_Method_propfind_elim(lean_box(0), v_t_378_, lean_box(0), v_propfind_380_);
stack->m_obj
 = v_res_381_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_propfind_elim___boxed(lean_object* v_motive_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_propfind_385_){
_start:
{
uint8_t v_t_boxed_386_; lean_object* v_res_387_; 
v_t_boxed_386_ = lean_unbox(v_t_383_);
v_res_387_ = l_Std_Http_Method_propfind_elim(v_motive_382_, v_t_boxed_386_, v_h_384_, v_propfind_385_);
lean_dec(v_propfind_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg(lean_object* v_proppatch_388_){
_start:
{
lean_inc(v_proppatch_388_);
return v_proppatch_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___redArg___boxed(lean_object* v_proppatch_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Http_Method_proppatch_elim___redArg(v_proppatch_389_);
lean_dec(v_proppatch_389_);
return v_res_390_;
}
}
lean_object* l_Std_Http_Method_proppatch_elim(lean_object* v_motive_391_, uint8_t v_t_392_, lean_object* v_h_393_, lean_object* v_proppatch_394_){
_start:
{
lean_inc(v_proppatch_394_);
return v_proppatch_394_;
}
}
LEAN_EXPORT void l_Std_Http_Method_proppatch_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_392_ = stack[1].m_num;
lean_object* v_proppatch_394_ = stack[3].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_Std_Http_Method_proppatch_elim(lean_box(0), v_t_392_, lean_box(0), v_proppatch_394_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_proppatch_elim___boxed(lean_object* v_motive_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_proppatch_399_){
_start:
{
uint8_t v_t_boxed_400_; lean_object* v_res_401_; 
v_t_boxed_400_ = lean_unbox(v_t_397_);
v_res_401_ = l_Std_Http_Method_proppatch_elim(v_motive_396_, v_t_boxed_400_, v_h_398_, v_proppatch_399_);
lean_dec(v_proppatch_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg(lean_object* v_put_402_){
_start:
{
lean_inc(v_put_402_);
return v_put_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___redArg___boxed(lean_object* v_put_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_Http_Method_put_elim___redArg(v_put_403_);
lean_dec(v_put_403_);
return v_res_404_;
}
}
lean_object* l_Std_Http_Method_put_elim(lean_object* v_motive_405_, uint8_t v_t_406_, lean_object* v_h_407_, lean_object* v_put_408_){
_start:
{
lean_inc(v_put_408_);
return v_put_408_;
}
}
LEAN_EXPORT void l_Std_Http_Method_put_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_406_ = stack[1].m_num;
lean_object* v_put_408_ = stack[3].m_obj;
lean_object* v_res_409_;
v_res_409_ = l_Std_Http_Method_put_elim(lean_box(0), v_t_406_, lean_box(0), v_put_408_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_put_elim___boxed(lean_object* v_motive_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_put_413_){
_start:
{
uint8_t v_t_boxed_414_; lean_object* v_res_415_; 
v_t_boxed_414_ = lean_unbox(v_t_411_);
v_res_415_ = l_Std_Http_Method_put_elim(v_motive_410_, v_t_boxed_414_, v_h_412_, v_put_413_);
lean_dec(v_put_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg(lean_object* v_query_416_){
_start:
{
lean_inc(v_query_416_);
return v_query_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___redArg___boxed(lean_object* v_query_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Http_Method_query_elim___redArg(v_query_417_);
lean_dec(v_query_417_);
return v_res_418_;
}
}
lean_object* l_Std_Http_Method_query_elim(lean_object* v_motive_419_, uint8_t v_t_420_, lean_object* v_h_421_, lean_object* v_query_422_){
_start:
{
lean_inc(v_query_422_);
return v_query_422_;
}
}
LEAN_EXPORT void l_Std_Http_Method_query_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_420_ = stack[1].m_num;
lean_object* v_query_422_ = stack[3].m_obj;
lean_object* v_res_423_;
v_res_423_ = l_Std_Http_Method_query_elim(lean_box(0), v_t_420_, lean_box(0), v_query_422_);
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_query_elim___boxed(lean_object* v_motive_424_, lean_object* v_t_425_, lean_object* v_h_426_, lean_object* v_query_427_){
_start:
{
uint8_t v_t_boxed_428_; lean_object* v_res_429_; 
v_t_boxed_428_ = lean_unbox(v_t_425_);
v_res_429_ = l_Std_Http_Method_query_elim(v_motive_424_, v_t_boxed_428_, v_h_426_, v_query_427_);
lean_dec(v_query_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg(lean_object* v_rebind_430_){
_start:
{
lean_inc(v_rebind_430_);
return v_rebind_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___redArg___boxed(lean_object* v_rebind_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_Http_Method_rebind_elim___redArg(v_rebind_431_);
lean_dec(v_rebind_431_);
return v_res_432_;
}
}
lean_object* l_Std_Http_Method_rebind_elim(lean_object* v_motive_433_, uint8_t v_t_434_, lean_object* v_h_435_, lean_object* v_rebind_436_){
_start:
{
lean_inc(v_rebind_436_);
return v_rebind_436_;
}
}
LEAN_EXPORT void l_Std_Http_Method_rebind_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_434_ = stack[1].m_num;
lean_object* v_rebind_436_ = stack[3].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Std_Http_Method_rebind_elim(lean_box(0), v_t_434_, lean_box(0), v_rebind_436_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_rebind_elim___boxed(lean_object* v_motive_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_rebind_441_){
_start:
{
uint8_t v_t_boxed_442_; lean_object* v_res_443_; 
v_t_boxed_442_ = lean_unbox(v_t_439_);
v_res_443_ = l_Std_Http_Method_rebind_elim(v_motive_438_, v_t_boxed_442_, v_h_440_, v_rebind_441_);
lean_dec(v_rebind_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg(lean_object* v_report_444_){
_start:
{
lean_inc(v_report_444_);
return v_report_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___redArg___boxed(lean_object* v_report_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Http_Method_report_elim___redArg(v_report_445_);
lean_dec(v_report_445_);
return v_res_446_;
}
}
lean_object* l_Std_Http_Method_report_elim(lean_object* v_motive_447_, uint8_t v_t_448_, lean_object* v_h_449_, lean_object* v_report_450_){
_start:
{
lean_inc(v_report_450_);
return v_report_450_;
}
}
LEAN_EXPORT void l_Std_Http_Method_report_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_448_ = stack[1].m_num;
lean_object* v_report_450_ = stack[3].m_obj;
lean_object* v_res_451_;
v_res_451_ = l_Std_Http_Method_report_elim(lean_box(0), v_t_448_, lean_box(0), v_report_450_);
stack->m_obj
 = v_res_451_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_report_elim___boxed(lean_object* v_motive_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_report_455_){
_start:
{
uint8_t v_t_boxed_456_; lean_object* v_res_457_; 
v_t_boxed_456_ = lean_unbox(v_t_453_);
v_res_457_ = l_Std_Http_Method_report_elim(v_motive_452_, v_t_boxed_456_, v_h_454_, v_report_455_);
lean_dec(v_report_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg(lean_object* v_search_458_){
_start:
{
lean_inc(v_search_458_);
return v_search_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___redArg___boxed(lean_object* v_search_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_Http_Method_search_elim___redArg(v_search_459_);
lean_dec(v_search_459_);
return v_res_460_;
}
}
lean_object* l_Std_Http_Method_search_elim(lean_object* v_motive_461_, uint8_t v_t_462_, lean_object* v_h_463_, lean_object* v_search_464_){
_start:
{
lean_inc(v_search_464_);
return v_search_464_;
}
}
LEAN_EXPORT void l_Std_Http_Method_search_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_462_ = stack[1].m_num;
lean_object* v_search_464_ = stack[3].m_obj;
lean_object* v_res_465_;
v_res_465_ = l_Std_Http_Method_search_elim(lean_box(0), v_t_462_, lean_box(0), v_search_464_);
stack->m_obj
 = v_res_465_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_search_elim___boxed(lean_object* v_motive_466_, lean_object* v_t_467_, lean_object* v_h_468_, lean_object* v_search_469_){
_start:
{
uint8_t v_t_boxed_470_; lean_object* v_res_471_; 
v_t_boxed_470_ = lean_unbox(v_t_467_);
v_res_471_ = l_Std_Http_Method_search_elim(v_motive_466_, v_t_boxed_470_, v_h_468_, v_search_469_);
lean_dec(v_search_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg(lean_object* v_trace_472_){
_start:
{
lean_inc(v_trace_472_);
return v_trace_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___redArg___boxed(lean_object* v_trace_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Http_Method_trace_elim___redArg(v_trace_473_);
lean_dec(v_trace_473_);
return v_res_474_;
}
}
lean_object* l_Std_Http_Method_trace_elim(lean_object* v_motive_475_, uint8_t v_t_476_, lean_object* v_h_477_, lean_object* v_trace_478_){
_start:
{
lean_inc(v_trace_478_);
return v_trace_478_;
}
}
LEAN_EXPORT void l_Std_Http_Method_trace_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_476_ = stack[1].m_num;
lean_object* v_trace_478_ = stack[3].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_Std_Http_Method_trace_elim(lean_box(0), v_t_476_, lean_box(0), v_trace_478_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_trace_elim___boxed(lean_object* v_motive_480_, lean_object* v_t_481_, lean_object* v_h_482_, lean_object* v_trace_483_){
_start:
{
uint8_t v_t_boxed_484_; lean_object* v_res_485_; 
v_t_boxed_484_ = lean_unbox(v_t_481_);
v_res_485_ = l_Std_Http_Method_trace_elim(v_motive_480_, v_t_boxed_484_, v_h_482_, v_trace_483_);
lean_dec(v_trace_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg(lean_object* v_unbind_486_){
_start:
{
lean_inc(v_unbind_486_);
return v_unbind_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___redArg___boxed(lean_object* v_unbind_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_Http_Method_unbind_elim___redArg(v_unbind_487_);
lean_dec(v_unbind_487_);
return v_res_488_;
}
}
lean_object* l_Std_Http_Method_unbind_elim(lean_object* v_motive_489_, uint8_t v_t_490_, lean_object* v_h_491_, lean_object* v_unbind_492_){
_start:
{
lean_inc(v_unbind_492_);
return v_unbind_492_;
}
}
LEAN_EXPORT void l_Std_Http_Method_unbind_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_490_ = stack[1].m_num;
lean_object* v_unbind_492_ = stack[3].m_obj;
lean_object* v_res_493_;
v_res_493_ = l_Std_Http_Method_unbind_elim(lean_box(0), v_t_490_, lean_box(0), v_unbind_492_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unbind_elim___boxed(lean_object* v_motive_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_unbind_497_){
_start:
{
uint8_t v_t_boxed_498_; lean_object* v_res_499_; 
v_t_boxed_498_ = lean_unbox(v_t_495_);
v_res_499_ = l_Std_Http_Method_unbind_elim(v_motive_494_, v_t_boxed_498_, v_h_496_, v_unbind_497_);
lean_dec(v_unbind_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg(lean_object* v_uncheckout_500_){
_start:
{
lean_inc(v_uncheckout_500_);
return v_uncheckout_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___redArg___boxed(lean_object* v_uncheckout_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_Http_Method_uncheckout_elim___redArg(v_uncheckout_501_);
lean_dec(v_uncheckout_501_);
return v_res_502_;
}
}
lean_object* l_Std_Http_Method_uncheckout_elim(lean_object* v_motive_503_, uint8_t v_t_504_, lean_object* v_h_505_, lean_object* v_uncheckout_506_){
_start:
{
lean_inc(v_uncheckout_506_);
return v_uncheckout_506_;
}
}
LEAN_EXPORT void l_Std_Http_Method_uncheckout_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_504_ = stack[1].m_num;
lean_object* v_uncheckout_506_ = stack[3].m_obj;
lean_object* v_res_507_;
v_res_507_ = l_Std_Http_Method_uncheckout_elim(lean_box(0), v_t_504_, lean_box(0), v_uncheckout_506_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_uncheckout_elim___boxed(lean_object* v_motive_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_uncheckout_511_){
_start:
{
uint8_t v_t_boxed_512_; lean_object* v_res_513_; 
v_t_boxed_512_ = lean_unbox(v_t_509_);
v_res_513_ = l_Std_Http_Method_uncheckout_elim(v_motive_508_, v_t_boxed_512_, v_h_510_, v_uncheckout_511_);
lean_dec(v_uncheckout_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg(lean_object* v_unlink_514_){
_start:
{
lean_inc(v_unlink_514_);
return v_unlink_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlink_elim___redArg___boxed(lean_object* v_unlink_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_Http_Method_unlink_elim___redArg(v_unlink_515_);
lean_dec(v_unlink_515_);
return v_res_516_;
}
}
lean_object* l_Std_Http_Method_unlink_elim(lean_object* v_motive_517_, uint8_t v_t_518_, lean_object* v_h_519_, lean_object* v_unlink_520_){
_start:
{
lean_inc(v_unlink_520_);
return v_unlink_520_;
}
}
LEAN_EXPORT void l_Std_Http_Method_unlink_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_518_ = stack[1].m_num;
lean_object* v_unlink_520_ = stack[3].m_obj;
lean_object* v_res_521_;
v_res_521_ = l_Std_Http_Method_unlink_elim(lean_box(0), v_t_518_, lean_box(0), v_unlink_520_);
stack->m_obj
 = v_res_521_;
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
lean_object* l_Std_Http_Method_unlock_elim(lean_object* v_motive_531_, uint8_t v_t_532_, lean_object* v_h_533_, lean_object* v_unlock_534_){
_start:
{
lean_inc(v_unlock_534_);
return v_unlock_534_;
}
}
LEAN_EXPORT void l_Std_Http_Method_unlock_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_532_ = stack[1].m_num;
lean_object* v_unlock_534_ = stack[3].m_obj;
lean_object* v_res_535_;
v_res_535_ = l_Std_Http_Method_unlock_elim(lean_box(0), v_t_532_, lean_box(0), v_unlock_534_);
stack->m_obj
 = v_res_535_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_unlock_elim___boxed(lean_object* v_motive_536_, lean_object* v_t_537_, lean_object* v_h_538_, lean_object* v_unlock_539_){
_start:
{
uint8_t v_t_boxed_540_; lean_object* v_res_541_; 
v_t_boxed_540_ = lean_unbox(v_t_537_);
v_res_541_ = l_Std_Http_Method_unlock_elim(v_motive_536_, v_t_boxed_540_, v_h_538_, v_unlock_539_);
lean_dec(v_unlock_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg(lean_object* v_update_542_){
_start:
{
lean_inc(v_update_542_);
return v_update_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___redArg___boxed(lean_object* v_update_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_Http_Method_update_elim___redArg(v_update_543_);
lean_dec(v_update_543_);
return v_res_544_;
}
}
lean_object* l_Std_Http_Method_update_elim(lean_object* v_motive_545_, uint8_t v_t_546_, lean_object* v_h_547_, lean_object* v_update_548_){
_start:
{
lean_inc(v_update_548_);
return v_update_548_;
}
}
LEAN_EXPORT void l_Std_Http_Method_update_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_546_ = stack[1].m_num;
lean_object* v_update_548_ = stack[3].m_obj;
lean_object* v_res_549_;
v_res_549_ = l_Std_Http_Method_update_elim(lean_box(0), v_t_546_, lean_box(0), v_update_548_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_update_elim___boxed(lean_object* v_motive_550_, lean_object* v_t_551_, lean_object* v_h_552_, lean_object* v_update_553_){
_start:
{
uint8_t v_t_boxed_554_; lean_object* v_res_555_; 
v_t_boxed_554_ = lean_unbox(v_t_551_);
v_res_555_ = l_Std_Http_Method_update_elim(v_motive_550_, v_t_boxed_554_, v_h_552_, v_update_553_);
lean_dec(v_update_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg(lean_object* v_updateredirectref_556_){
_start:
{
lean_inc(v_updateredirectref_556_);
return v_updateredirectref_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___redArg___boxed(lean_object* v_updateredirectref_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Http_Method_updateredirectref_elim___redArg(v_updateredirectref_557_);
lean_dec(v_updateredirectref_557_);
return v_res_558_;
}
}
lean_object* l_Std_Http_Method_updateredirectref_elim(lean_object* v_motive_559_, uint8_t v_t_560_, lean_object* v_h_561_, lean_object* v_updateredirectref_562_){
_start:
{
lean_inc(v_updateredirectref_562_);
return v_updateredirectref_562_;
}
}
LEAN_EXPORT void l_Std_Http_Method_updateredirectref_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_560_ = stack[1].m_num;
lean_object* v_updateredirectref_562_ = stack[3].m_obj;
lean_object* v_res_563_;
v_res_563_ = l_Std_Http_Method_updateredirectref_elim(lean_box(0), v_t_560_, lean_box(0), v_updateredirectref_562_);
stack->m_obj
 = v_res_563_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_updateredirectref_elim___boxed(lean_object* v_motive_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_updateredirectref_567_){
_start:
{
uint8_t v_t_boxed_568_; lean_object* v_res_569_; 
v_t_boxed_568_ = lean_unbox(v_t_565_);
v_res_569_ = l_Std_Http_Method_updateredirectref_elim(v_motive_564_, v_t_boxed_568_, v_h_566_, v_updateredirectref_567_);
lean_dec(v_updateredirectref_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg(lean_object* v_versionControl_570_){
_start:
{
lean_inc(v_versionControl_570_);
return v_versionControl_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___redArg___boxed(lean_object* v_versionControl_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_Http_Method_versionControl_elim___redArg(v_versionControl_571_);
lean_dec(v_versionControl_571_);
return v_res_572_;
}
}
lean_object* l_Std_Http_Method_versionControl_elim(lean_object* v_motive_573_, uint8_t v_t_574_, lean_object* v_h_575_, lean_object* v_versionControl_576_){
_start:
{
lean_inc(v_versionControl_576_);
return v_versionControl_576_;
}
}
LEAN_EXPORT void l_Std_Http_Method_versionControl_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_574_ = stack[1].m_num;
lean_object* v_versionControl_576_ = stack[3].m_obj;
lean_object* v_res_577_;
v_res_577_ = l_Std_Http_Method_versionControl_elim(lean_box(0), v_t_574_, lean_box(0), v_versionControl_576_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_versionControl_elim___boxed(lean_object* v_motive_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_versionControl_581_){
_start:
{
uint8_t v_t_boxed_582_; lean_object* v_res_583_; 
v_t_boxed_582_ = lean_unbox(v_t_579_);
v_res_583_ = l_Std_Http_Method_versionControl_elim(v_motive_578_, v_t_boxed_582_, v_h_580_, v_versionControl_581_);
lean_dec(v_versionControl_581_);
return v_res_583_;
}
}
static lean_object* _init_l_Std_Http_instReprMethod_repr___closed__80(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(2u);
v___x_705_ = lean_nat_to_int(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Std_Http_instReprMethod_repr___closed__81(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_to_int(v___x_706_);
return v___x_707_;
}
}
lean_object* l_Std_Http_instReprMethod_repr(uint8_t v_x_708_, lean_object* v_prec_709_){
_start:
{
lean_object* v___y_711_; lean_object* v___y_718_; lean_object* v___y_725_; lean_object* v___y_732_; lean_object* v___y_739_; lean_object* v___y_746_; lean_object* v___y_753_; lean_object* v___y_760_; lean_object* v___y_767_; lean_object* v___y_774_; lean_object* v___y_781_; lean_object* v___y_788_; lean_object* v___y_795_; lean_object* v___y_802_; lean_object* v___y_809_; lean_object* v___y_816_; lean_object* v___y_823_; lean_object* v___y_830_; lean_object* v___y_837_; lean_object* v___y_844_; lean_object* v___y_851_; lean_object* v___y_858_; lean_object* v___y_865_; lean_object* v___y_872_; lean_object* v___y_879_; lean_object* v___y_886_; lean_object* v___y_893_; lean_object* v___y_900_; lean_object* v___y_907_; lean_object* v___y_914_; lean_object* v___y_921_; lean_object* v___y_928_; lean_object* v___y_935_; lean_object* v___y_942_; lean_object* v___y_949_; lean_object* v___y_956_; lean_object* v___y_963_; lean_object* v___y_970_; lean_object* v___y_977_; lean_object* v___y_984_; 
switch(v_x_708_)
{
case 0:
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(1024u);
v___x_991_ = lean_nat_dec_le(v___x_990_, v_prec_709_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_711_ = v___x_992_;
goto v___jp_710_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_711_ = v___x_993_;
goto v___jp_710_;
}
}
case 1:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_unsigned_to_nat(1024u);
v___x_995_ = lean_nat_dec_le(v___x_994_, v_prec_709_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
v___x_996_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_718_ = v___x_996_;
goto v___jp_717_;
}
else
{
lean_object* v___x_997_; 
v___x_997_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_718_ = v___x_997_;
goto v___jp_717_;
}
}
case 2:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_unsigned_to_nat(1024u);
v___x_999_ = lean_nat_dec_le(v___x_998_, v_prec_709_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_725_ = v___x_1000_;
goto v___jp_724_;
}
else
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_725_ = v___x_1001_;
goto v___jp_724_;
}
}
case 3:
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(1024u);
v___x_1003_ = lean_nat_dec_le(v___x_1002_, v_prec_709_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_732_ = v___x_1004_;
goto v___jp_731_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_732_ = v___x_1005_;
goto v___jp_731_;
}
}
case 4:
{
lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = lean_unsigned_to_nat(1024u);
v___x_1007_ = lean_nat_dec_le(v___x_1006_, v_prec_709_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_739_ = v___x_1008_;
goto v___jp_738_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_739_ = v___x_1009_;
goto v___jp_738_;
}
}
case 5:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(1024u);
v___x_1011_ = lean_nat_dec_le(v___x_1010_, v_prec_709_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_746_ = v___x_1012_;
goto v___jp_745_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_746_ = v___x_1013_;
goto v___jp_745_;
}
}
case 6:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_unsigned_to_nat(1024u);
v___x_1015_ = lean_nat_dec_le(v___x_1014_, v_prec_709_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_753_ = v___x_1016_;
goto v___jp_752_;
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_753_ = v___x_1017_;
goto v___jp_752_;
}
}
case 7:
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(1024u);
v___x_1019_ = lean_nat_dec_le(v___x_1018_, v_prec_709_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_760_ = v___x_1020_;
goto v___jp_759_;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_760_ = v___x_1021_;
goto v___jp_759_;
}
}
case 8:
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(1024u);
v___x_1023_ = lean_nat_dec_le(v___x_1022_, v_prec_709_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_767_ = v___x_1024_;
goto v___jp_766_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_767_ = v___x_1025_;
goto v___jp_766_;
}
}
case 9:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = lean_unsigned_to_nat(1024u);
v___x_1027_ = lean_nat_dec_le(v___x_1026_, v_prec_709_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_774_ = v___x_1028_;
goto v___jp_773_;
}
else
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_774_ = v___x_1029_;
goto v___jp_773_;
}
}
case 10:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_unsigned_to_nat(1024u);
v___x_1031_ = lean_nat_dec_le(v___x_1030_, v_prec_709_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_781_ = v___x_1032_;
goto v___jp_780_;
}
else
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_781_ = v___x_1033_;
goto v___jp_780_;
}
}
case 11:
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_unsigned_to_nat(1024u);
v___x_1035_ = lean_nat_dec_le(v___x_1034_, v_prec_709_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_788_ = v___x_1036_;
goto v___jp_787_;
}
else
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_788_ = v___x_1037_;
goto v___jp_787_;
}
}
case 12:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_unsigned_to_nat(1024u);
v___x_1039_ = lean_nat_dec_le(v___x_1038_, v_prec_709_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_795_ = v___x_1040_;
goto v___jp_794_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_795_ = v___x_1041_;
goto v___jp_794_;
}
}
case 13:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(1024u);
v___x_1043_ = lean_nat_dec_le(v___x_1042_, v_prec_709_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_802_ = v___x_1044_;
goto v___jp_801_;
}
else
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_802_ = v___x_1045_;
goto v___jp_801_;
}
}
case 14:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_unsigned_to_nat(1024u);
v___x_1047_ = lean_nat_dec_le(v___x_1046_, v_prec_709_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_809_ = v___x_1048_;
goto v___jp_808_;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_809_ = v___x_1049_;
goto v___jp_808_;
}
}
case 15:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(1024u);
v___x_1051_ = lean_nat_dec_le(v___x_1050_, v_prec_709_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_816_ = v___x_1052_;
goto v___jp_815_;
}
else
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_816_ = v___x_1053_;
goto v___jp_815_;
}
}
case 16:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_unsigned_to_nat(1024u);
v___x_1055_ = lean_nat_dec_le(v___x_1054_, v_prec_709_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_823_ = v___x_1056_;
goto v___jp_822_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_823_ = v___x_1057_;
goto v___jp_822_;
}
}
case 17:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(1024u);
v___x_1059_ = lean_nat_dec_le(v___x_1058_, v_prec_709_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_830_ = v___x_1060_;
goto v___jp_829_;
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_830_ = v___x_1061_;
goto v___jp_829_;
}
}
case 18:
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(1024u);
v___x_1063_ = lean_nat_dec_le(v___x_1062_, v_prec_709_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_837_ = v___x_1064_;
goto v___jp_836_;
}
else
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_837_ = v___x_1065_;
goto v___jp_836_;
}
}
case 19:
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(1024u);
v___x_1067_ = lean_nat_dec_le(v___x_1066_, v_prec_709_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_844_ = v___x_1068_;
goto v___jp_843_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_844_ = v___x_1069_;
goto v___jp_843_;
}
}
case 20:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_unsigned_to_nat(1024u);
v___x_1071_ = lean_nat_dec_le(v___x_1070_, v_prec_709_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_851_ = v___x_1072_;
goto v___jp_850_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_851_ = v___x_1073_;
goto v___jp_850_;
}
}
case 21:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(1024u);
v___x_1075_ = lean_nat_dec_le(v___x_1074_, v_prec_709_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_858_ = v___x_1076_;
goto v___jp_857_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_858_ = v___x_1077_;
goto v___jp_857_;
}
}
case 22:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(1024u);
v___x_1079_ = lean_nat_dec_le(v___x_1078_, v_prec_709_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_865_ = v___x_1080_;
goto v___jp_864_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_865_ = v___x_1081_;
goto v___jp_864_;
}
}
case 23:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_unsigned_to_nat(1024u);
v___x_1083_ = lean_nat_dec_le(v___x_1082_, v_prec_709_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_872_ = v___x_1084_;
goto v___jp_871_;
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_872_ = v___x_1085_;
goto v___jp_871_;
}
}
case 24:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_unsigned_to_nat(1024u);
v___x_1087_ = lean_nat_dec_le(v___x_1086_, v_prec_709_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_879_ = v___x_1088_;
goto v___jp_878_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_879_ = v___x_1089_;
goto v___jp_878_;
}
}
case 25:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_unsigned_to_nat(1024u);
v___x_1091_ = lean_nat_dec_le(v___x_1090_, v_prec_709_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_886_ = v___x_1092_;
goto v___jp_885_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_886_ = v___x_1093_;
goto v___jp_885_;
}
}
case 26:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = lean_unsigned_to_nat(1024u);
v___x_1095_ = lean_nat_dec_le(v___x_1094_, v_prec_709_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_893_ = v___x_1096_;
goto v___jp_892_;
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_893_ = v___x_1097_;
goto v___jp_892_;
}
}
case 27:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_unsigned_to_nat(1024u);
v___x_1099_ = lean_nat_dec_le(v___x_1098_, v_prec_709_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_900_ = v___x_1100_;
goto v___jp_899_;
}
else
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_900_ = v___x_1101_;
goto v___jp_899_;
}
}
case 28:
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_unsigned_to_nat(1024u);
v___x_1103_ = lean_nat_dec_le(v___x_1102_, v_prec_709_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_907_ = v___x_1104_;
goto v___jp_906_;
}
else
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_907_ = v___x_1105_;
goto v___jp_906_;
}
}
case 29:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_unsigned_to_nat(1024u);
v___x_1107_ = lean_nat_dec_le(v___x_1106_, v_prec_709_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_914_ = v___x_1108_;
goto v___jp_913_;
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_914_ = v___x_1109_;
goto v___jp_913_;
}
}
case 30:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_unsigned_to_nat(1024u);
v___x_1111_ = lean_nat_dec_le(v___x_1110_, v_prec_709_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_921_ = v___x_1112_;
goto v___jp_920_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_921_ = v___x_1113_;
goto v___jp_920_;
}
}
case 31:
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = lean_unsigned_to_nat(1024u);
v___x_1115_ = lean_nat_dec_le(v___x_1114_, v_prec_709_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_928_ = v___x_1116_;
goto v___jp_927_;
}
else
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_928_ = v___x_1117_;
goto v___jp_927_;
}
}
case 32:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = lean_unsigned_to_nat(1024u);
v___x_1119_ = lean_nat_dec_le(v___x_1118_, v_prec_709_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_935_ = v___x_1120_;
goto v___jp_934_;
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_935_ = v___x_1121_;
goto v___jp_934_;
}
}
case 33:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(1024u);
v___x_1123_ = lean_nat_dec_le(v___x_1122_, v_prec_709_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_942_ = v___x_1124_;
goto v___jp_941_;
}
else
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_942_ = v___x_1125_;
goto v___jp_941_;
}
}
case 34:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(1024u);
v___x_1127_ = lean_nat_dec_le(v___x_1126_, v_prec_709_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_949_ = v___x_1128_;
goto v___jp_948_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_949_ = v___x_1129_;
goto v___jp_948_;
}
}
case 35:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(1024u);
v___x_1131_ = lean_nat_dec_le(v___x_1130_, v_prec_709_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_956_ = v___x_1132_;
goto v___jp_955_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_956_ = v___x_1133_;
goto v___jp_955_;
}
}
case 36:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_unsigned_to_nat(1024u);
v___x_1135_ = lean_nat_dec_le(v___x_1134_, v_prec_709_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_963_ = v___x_1136_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_963_ = v___x_1137_;
goto v___jp_962_;
}
}
case 37:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(1024u);
v___x_1139_ = lean_nat_dec_le(v___x_1138_, v_prec_709_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_970_ = v___x_1140_;
goto v___jp_969_;
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_970_ = v___x_1141_;
goto v___jp_969_;
}
}
case 38:
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(1024u);
v___x_1143_ = lean_nat_dec_le(v___x_1142_, v_prec_709_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_977_ = v___x_1144_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_977_ = v___x_1145_;
goto v___jp_976_;
}
}
default: 
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = lean_unsigned_to_nat(1024u);
v___x_1147_ = lean_nat_dec_le(v___x_1146_, v_prec_709_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__80, &l_Std_Http_instReprMethod_repr___closed__80_once, _init_l_Std_Http_instReprMethod_repr___closed__80);
v___y_984_ = v___x_1148_;
goto v___jp_983_;
}
else
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_obj_once(&l_Std_Http_instReprMethod_repr___closed__81, &l_Std_Http_instReprMethod_repr___closed__81_once, _init_l_Std_Http_instReprMethod_repr___closed__81);
v___y_984_ = v___x_1149_;
goto v___jp_983_;
}
}
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_712_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__1));
lean_inc(v___y_711_);
v___x_713_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_713_, 0, v___y_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = 0;
v___x_715_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*1, v___x_714_);
v___x_716_ = l_Repr_addAppParen(v___x_715_, v_prec_709_);
return v___x_716_;
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_719_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__3));
lean_inc(v___y_718_);
v___x_720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_720_, 0, v___y_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = 0;
v___x_722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*1, v___x_721_);
v___x_723_ = l_Repr_addAppParen(v___x_722_, v_prec_709_);
return v___x_723_;
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_726_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__5));
lean_inc(v___y_725_);
v___x_727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_727_, 0, v___y_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = 0;
v___x_729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*1, v___x_728_);
v___x_730_ = l_Repr_addAppParen(v___x_729_, v_prec_709_);
return v___x_730_;
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_733_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__7));
lean_inc(v___y_732_);
v___x_734_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_734_, 0, v___y_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = 0;
v___x_736_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*1, v___x_735_);
v___x_737_ = l_Repr_addAppParen(v___x_736_, v_prec_709_);
return v___x_737_;
}
v___jp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_740_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__9));
lean_inc(v___y_739_);
v___x_741_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_741_, 0, v___y_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = 0;
v___x_743_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*1, v___x_742_);
v___x_744_ = l_Repr_addAppParen(v___x_743_, v_prec_709_);
return v___x_744_;
}
v___jp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_747_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__11));
lean_inc(v___y_746_);
v___x_748_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_748_, 0, v___y_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = 0;
v___x_750_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*1, v___x_749_);
v___x_751_ = l_Repr_addAppParen(v___x_750_, v_prec_709_);
return v___x_751_;
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_754_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__13));
lean_inc(v___y_753_);
v___x_755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_755_, 0, v___y_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = 0;
v___x_757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*1, v___x_756_);
v___x_758_ = l_Repr_addAppParen(v___x_757_, v_prec_709_);
return v___x_758_;
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_761_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__15));
lean_inc(v___y_760_);
v___x_762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_762_, 0, v___y_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = 0;
v___x_764_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*1, v___x_763_);
v___x_765_ = l_Repr_addAppParen(v___x_764_, v_prec_709_);
return v___x_765_;
}
v___jp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_768_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__17));
lean_inc(v___y_767_);
v___x_769_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_769_, 0, v___y_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = 0;
v___x_771_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*1, v___x_770_);
v___x_772_ = l_Repr_addAppParen(v___x_771_, v_prec_709_);
return v___x_772_;
}
v___jp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_775_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__19));
lean_inc(v___y_774_);
v___x_776_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_776_, 0, v___y_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = 0;
v___x_778_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set_uint8(v___x_778_, sizeof(void*)*1, v___x_777_);
v___x_779_ = l_Repr_addAppParen(v___x_778_, v_prec_709_);
return v___x_779_;
}
v___jp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_782_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__21));
lean_inc(v___y_781_);
v___x_783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_783_, 0, v___y_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = 0;
v___x_785_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_784_);
v___x_786_ = l_Repr_addAppParen(v___x_785_, v_prec_709_);
return v___x_786_;
}
v___jp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_789_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__23));
lean_inc(v___y_788_);
v___x_790_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_790_, 0, v___y_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = 0;
v___x_792_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*1, v___x_791_);
v___x_793_ = l_Repr_addAppParen(v___x_792_, v_prec_709_);
return v___x_793_;
}
v___jp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_796_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__25));
lean_inc(v___y_795_);
v___x_797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_797_, 0, v___y_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = 0;
v___x_799_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*1, v___x_798_);
v___x_800_ = l_Repr_addAppParen(v___x_799_, v_prec_709_);
return v___x_800_;
}
v___jp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_803_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__27));
lean_inc(v___y_802_);
v___x_804_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_804_, 0, v___y_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = 0;
v___x_806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*1, v___x_805_);
v___x_807_ = l_Repr_addAppParen(v___x_806_, v_prec_709_);
return v___x_807_;
}
v___jp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_810_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__29));
lean_inc(v___y_809_);
v___x_811_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_811_, 0, v___y_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = 0;
v___x_813_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*1, v___x_812_);
v___x_814_ = l_Repr_addAppParen(v___x_813_, v_prec_709_);
return v___x_814_;
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_817_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__31));
lean_inc(v___y_816_);
v___x_818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_818_, 0, v___y_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = 0;
v___x_820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*1, v___x_819_);
v___x_821_ = l_Repr_addAppParen(v___x_820_, v_prec_709_);
return v___x_821_;
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_824_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__33));
lean_inc(v___y_823_);
v___x_825_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_825_, 0, v___y_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = 0;
v___x_827_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*1, v___x_826_);
v___x_828_ = l_Repr_addAppParen(v___x_827_, v_prec_709_);
return v___x_828_;
}
v___jp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_831_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__35));
lean_inc(v___y_830_);
v___x_832_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = 0;
v___x_834_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*1, v___x_833_);
v___x_835_ = l_Repr_addAppParen(v___x_834_, v_prec_709_);
return v___x_835_;
}
v___jp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_838_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__37));
lean_inc(v___y_837_);
v___x_839_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_839_, 0, v___y_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = 0;
v___x_841_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*1, v___x_840_);
v___x_842_ = l_Repr_addAppParen(v___x_841_, v_prec_709_);
return v___x_842_;
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_845_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__39));
lean_inc(v___y_844_);
v___x_846_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_846_, 0, v___y_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = 0;
v___x_848_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*1, v___x_847_);
v___x_849_ = l_Repr_addAppParen(v___x_848_, v_prec_709_);
return v___x_849_;
}
v___jp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_852_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__41));
lean_inc(v___y_851_);
v___x_853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_853_, 0, v___y_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = 0;
v___x_855_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*1, v___x_854_);
v___x_856_ = l_Repr_addAppParen(v___x_855_, v_prec_709_);
return v___x_856_;
}
v___jp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_859_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__43));
lean_inc(v___y_858_);
v___x_860_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = 0;
v___x_862_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*1, v___x_861_);
v___x_863_ = l_Repr_addAppParen(v___x_862_, v_prec_709_);
return v___x_863_;
}
v___jp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_866_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__45));
lean_inc(v___y_865_);
v___x_867_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_867_, 0, v___y_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = 0;
v___x_869_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*1, v___x_868_);
v___x_870_ = l_Repr_addAppParen(v___x_869_, v_prec_709_);
return v___x_870_;
}
v___jp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_873_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__47));
lean_inc(v___y_872_);
v___x_874_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_874_, 0, v___y_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = 0;
v___x_876_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1, v___x_875_);
v___x_877_ = l_Repr_addAppParen(v___x_876_, v_prec_709_);
return v___x_877_;
}
v___jp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_880_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__49));
lean_inc(v___y_879_);
v___x_881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_881_, 0, v___y_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = 0;
v___x_883_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1, v___x_882_);
v___x_884_ = l_Repr_addAppParen(v___x_883_, v_prec_709_);
return v___x_884_;
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__51));
lean_inc(v___y_886_);
v___x_888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_888_, 0, v___y_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = 0;
v___x_890_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*1, v___x_889_);
v___x_891_ = l_Repr_addAppParen(v___x_890_, v_prec_709_);
return v___x_891_;
}
v___jp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_894_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__53));
lean_inc(v___y_893_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___y_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = 0;
v___x_897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_896_);
v___x_898_ = l_Repr_addAppParen(v___x_897_, v_prec_709_);
return v___x_898_;
}
v___jp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_901_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__55));
lean_inc(v___y_900_);
v___x_902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_902_, 0, v___y_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = 0;
v___x_904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1, v___x_903_);
v___x_905_ = l_Repr_addAppParen(v___x_904_, v_prec_709_);
return v___x_905_;
}
v___jp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_908_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__57));
lean_inc(v___y_907_);
v___x_909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_909_, 0, v___y_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = 0;
v___x_911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*1, v___x_910_);
v___x_912_ = l_Repr_addAppParen(v___x_911_, v_prec_709_);
return v___x_912_;
}
v___jp_913_:
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__59));
lean_inc(v___y_914_);
v___x_916_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_916_, 0, v___y_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = 0;
v___x_918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*1, v___x_917_);
v___x_919_ = l_Repr_addAppParen(v___x_918_, v_prec_709_);
return v___x_919_;
}
v___jp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_922_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__61));
lean_inc(v___y_921_);
v___x_923_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_923_, 0, v___y_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = 0;
v___x_925_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*1, v___x_924_);
v___x_926_ = l_Repr_addAppParen(v___x_925_, v_prec_709_);
return v___x_926_;
}
v___jp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_929_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__63));
lean_inc(v___y_928_);
v___x_930_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_930_, 0, v___y_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = 0;
v___x_932_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*1, v___x_931_);
v___x_933_ = l_Repr_addAppParen(v___x_932_, v_prec_709_);
return v___x_933_;
}
v___jp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_936_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__65));
lean_inc(v___y_935_);
v___x_937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_937_, 0, v___y_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = 0;
v___x_939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*1, v___x_938_);
v___x_940_ = l_Repr_addAppParen(v___x_939_, v_prec_709_);
return v___x_940_;
}
v___jp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_943_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__67));
lean_inc(v___y_942_);
v___x_944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_944_, 0, v___y_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = 0;
v___x_946_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*1, v___x_945_);
v___x_947_ = l_Repr_addAppParen(v___x_946_, v_prec_709_);
return v___x_947_;
}
v___jp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_950_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__69));
lean_inc(v___y_949_);
v___x_951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_951_, 0, v___y_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = 0;
v___x_953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v___x_952_);
v___x_954_ = l_Repr_addAppParen(v___x_953_, v_prec_709_);
return v___x_954_;
}
v___jp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_957_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__71));
lean_inc(v___y_956_);
v___x_958_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_958_, 0, v___y_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = 0;
v___x_960_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set_uint8(v___x_960_, sizeof(void*)*1, v___x_959_);
v___x_961_ = l_Repr_addAppParen(v___x_960_, v_prec_709_);
return v___x_961_;
}
v___jp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_964_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__73));
lean_inc(v___y_963_);
v___x_965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_965_, 0, v___y_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = 0;
v___x_967_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*1, v___x_966_);
v___x_968_ = l_Repr_addAppParen(v___x_967_, v_prec_709_);
return v___x_968_;
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_971_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__75));
lean_inc(v___y_970_);
v___x_972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_972_, 0, v___y_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = 0;
v___x_974_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*1, v___x_973_);
v___x_975_ = l_Repr_addAppParen(v___x_974_, v_prec_709_);
return v___x_975_;
}
v___jp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_978_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__77));
lean_inc(v___y_977_);
v___x_979_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_979_, 0, v___y_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = 0;
v___x_981_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*1, v___x_980_);
v___x_982_ = l_Repr_addAppParen(v___x_981_, v_prec_709_);
return v___x_982_;
}
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_985_ = ((lean_object*)(l_Std_Http_instReprMethod_repr___closed__79));
lean_inc(v___y_984_);
v___x_986_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_986_, 0, v___y_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = 0;
v___x_988_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*1, v___x_987_);
v___x_989_ = l_Repr_addAppParen(v___x_988_, v_prec_709_);
return v___x_989_;
}
}
}
LEAN_EXPORT void l_Std_Http_instReprMethod_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_708_ = stack[0].m_num;
lean_object* v_prec_709_ = stack[1].m_obj;
lean_object* v_res_1150_;
v_res_1150_ = l_Std_Http_instReprMethod_repr(v_x_708_, v_prec_709_);
stack->m_obj
 = v_res_1150_;
}
LEAN_EXPORT lean_object* l_Std_Http_instReprMethod_repr___boxed(lean_object* v_x_1151_, lean_object* v_prec_1152_){
_start:
{
uint8_t v_x_2169__boxed_1153_; lean_object* v_res_1154_; 
v_x_2169__boxed_1153_ = lean_unbox(v_x_1151_);
v_res_1154_ = l_Std_Http_instReprMethod_repr(v_x_2169__boxed_1153_, v_prec_1152_);
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
uint8_t l_Std_Http_instBEqMethod_beq(uint8_t v_x_1159_, uint8_t v_y_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1161_ = lean_box(v_x_1159_);
v___x_1162_ = lean_obj_tag_nat(v___x_1161_);
lean_dec(v___x_1161_);
v___x_1163_ = lean_box(v_y_1160_);
v___x_1164_ = lean_obj_tag_nat(v___x_1163_);
lean_dec(v___x_1163_);
v___x_1165_ = lean_nat_dec_eq(v___x_1162_, v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT void l_Std_Http_instBEqMethod_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1159_ = stack[0].m_num;
uint8_t v_y_1160_ = stack[1].m_num;
uint8_t v_res_1166_;
v_res_1166_ = l_Std_Http_instBEqMethod_beq(v_x_1159_, v_y_1160_);
stack->m_num = v_res_1166_;
}
LEAN_EXPORT lean_object* l_Std_Http_instBEqMethod_beq___boxed(lean_object* v_x_1167_, lean_object* v_y_1168_){
_start:
{
uint8_t v_x_24__boxed_1169_; uint8_t v_y_25__boxed_1170_; uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_x_24__boxed_1169_ = lean_unbox(v_x_1167_);
v_y_25__boxed_1170_ = lean_unbox(v_y_1168_);
v_res_1171_ = l_Std_Http_instBEqMethod_beq(v_x_24__boxed_1169_, v_y_25__boxed_1170_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
uint8_t l_Std_Http_Method_ofNat(lean_object* v_n_1175_){
_start:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_unsigned_to_nat(19u);
v___x_1177_ = lean_nat_dec_le(v_n_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_unsigned_to_nat(29u);
v___x_1179_ = lean_nat_dec_le(v_n_1175_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_unsigned_to_nat(34u);
v___x_1181_ = lean_nat_dec_le(v_n_1175_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = lean_unsigned_to_nat(36u);
v___x_1183_ = lean_nat_dec_le(v_n_1175_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = lean_unsigned_to_nat(37u);
v___x_1185_ = lean_nat_dec_le(v_n_1175_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_unsigned_to_nat(38u);
v___x_1187_ = lean_nat_dec_le(v_n_1175_, v___x_1186_);
if (v___x_1187_ == 0)
{
uint8_t v___x_1188_; 
v___x_1188_ = 39;
return v___x_1188_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = 38;
return v___x_1189_;
}
}
else
{
uint8_t v___x_1190_; 
v___x_1190_ = 37;
return v___x_1190_;
}
}
else
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(35u);
v___x_1192_ = lean_nat_dec_le(v_n_1175_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = 36;
return v___x_1193_;
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = 35;
return v___x_1194_;
}
}
}
else
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_unsigned_to_nat(31u);
v___x_1196_ = lean_nat_dec_le(v_n_1175_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_unsigned_to_nat(32u);
v___x_1198_ = lean_nat_dec_le(v_n_1175_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(33u);
v___x_1200_ = lean_nat_dec_le(v_n_1175_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint8_t v___x_1201_; 
v___x_1201_ = 34;
return v___x_1201_;
}
else
{
uint8_t v___x_1202_; 
v___x_1202_ = 33;
return v___x_1202_;
}
}
else
{
uint8_t v___x_1203_; 
v___x_1203_ = 32;
return v___x_1203_;
}
}
else
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(30u);
v___x_1205_ = lean_nat_dec_le(v_n_1175_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint8_t v___x_1206_; 
v___x_1206_ = 31;
return v___x_1206_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = 30;
return v___x_1207_;
}
}
}
}
else
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_unsigned_to_nat(24u);
v___x_1209_ = lean_nat_dec_le(v_n_1175_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_unsigned_to_nat(26u);
v___x_1211_ = lean_nat_dec_le(v_n_1175_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(27u);
v___x_1213_ = lean_nat_dec_le(v_n_1175_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_unsigned_to_nat(28u);
v___x_1215_ = lean_nat_dec_le(v_n_1175_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint8_t v___x_1216_; 
v___x_1216_ = 29;
return v___x_1216_;
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = 28;
return v___x_1217_;
}
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = 27;
return v___x_1218_;
}
}
else
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = lean_unsigned_to_nat(25u);
v___x_1220_ = lean_nat_dec_le(v_n_1175_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; 
v___x_1221_ = 26;
return v___x_1221_;
}
else
{
uint8_t v___x_1222_; 
v___x_1222_ = 25;
return v___x_1222_;
}
}
}
else
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(21u);
v___x_1224_ = lean_nat_dec_le(v_n_1175_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_unsigned_to_nat(22u);
v___x_1226_ = lean_nat_dec_le(v_n_1175_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = lean_unsigned_to_nat(23u);
v___x_1228_ = lean_nat_dec_le(v_n_1175_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; 
v___x_1229_ = 24;
return v___x_1229_;
}
else
{
uint8_t v___x_1230_; 
v___x_1230_ = 23;
return v___x_1230_;
}
}
else
{
uint8_t v___x_1231_; 
v___x_1231_ = 22;
return v___x_1231_;
}
}
else
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = lean_unsigned_to_nat(20u);
v___x_1233_ = lean_nat_dec_le(v_n_1175_, v___x_1232_);
if (v___x_1233_ == 0)
{
uint8_t v___x_1234_; 
v___x_1234_ = 21;
return v___x_1234_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = 20;
return v___x_1235_;
}
}
}
}
}
else
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_unsigned_to_nat(9u);
v___x_1237_ = lean_nat_dec_le(v_n_1175_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_unsigned_to_nat(14u);
v___x_1239_ = lean_nat_dec_le(v_n_1175_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = lean_unsigned_to_nat(16u);
v___x_1241_ = lean_nat_dec_le(v_n_1175_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_unsigned_to_nat(17u);
v___x_1243_ = lean_nat_dec_le(v_n_1175_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(18u);
v___x_1245_ = lean_nat_dec_le(v_n_1175_, v___x_1244_);
if (v___x_1245_ == 0)
{
uint8_t v___x_1246_; 
v___x_1246_ = 19;
return v___x_1246_;
}
else
{
uint8_t v___x_1247_; 
v___x_1247_ = 18;
return v___x_1247_;
}
}
else
{
uint8_t v___x_1248_; 
v___x_1248_ = 17;
return v___x_1248_;
}
}
else
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = lean_unsigned_to_nat(15u);
v___x_1250_ = lean_nat_dec_le(v_n_1175_, v___x_1249_);
if (v___x_1250_ == 0)
{
uint8_t v___x_1251_; 
v___x_1251_ = 16;
return v___x_1251_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = 15;
return v___x_1252_;
}
}
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_unsigned_to_nat(11u);
v___x_1254_ = lean_nat_dec_le(v_n_1175_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_unsigned_to_nat(12u);
v___x_1256_ = lean_nat_dec_le(v_n_1175_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = lean_unsigned_to_nat(13u);
v___x_1258_ = lean_nat_dec_le(v_n_1175_, v___x_1257_);
if (v___x_1258_ == 0)
{
uint8_t v___x_1259_; 
v___x_1259_ = 14;
return v___x_1259_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = 13;
return v___x_1260_;
}
}
else
{
uint8_t v___x_1261_; 
v___x_1261_ = 12;
return v___x_1261_;
}
}
else
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = lean_unsigned_to_nat(10u);
v___x_1263_ = lean_nat_dec_le(v_n_1175_, v___x_1262_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = 11;
return v___x_1264_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = 10;
return v___x_1265_;
}
}
}
}
else
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = lean_unsigned_to_nat(4u);
v___x_1267_ = lean_nat_dec_le(v_n_1175_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = lean_unsigned_to_nat(6u);
v___x_1269_ = lean_nat_dec_le(v_n_1175_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = lean_unsigned_to_nat(7u);
v___x_1271_ = lean_nat_dec_le(v_n_1175_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = lean_unsigned_to_nat(8u);
v___x_1273_ = lean_nat_dec_le(v_n_1175_, v___x_1272_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1274_; 
v___x_1274_ = 9;
return v___x_1274_;
}
else
{
uint8_t v___x_1275_; 
v___x_1275_ = 8;
return v___x_1275_;
}
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = 7;
return v___x_1276_;
}
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(5u);
v___x_1278_ = lean_nat_dec_le(v_n_1175_, v___x_1277_);
if (v___x_1278_ == 0)
{
uint8_t v___x_1279_; 
v___x_1279_ = 6;
return v___x_1279_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = 5;
return v___x_1280_;
}
}
}
else
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_dec_le(v_n_1175_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = lean_unsigned_to_nat(2u);
v___x_1284_ = lean_nat_dec_le(v_n_1175_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = lean_unsigned_to_nat(3u);
v___x_1286_ = lean_nat_dec_le(v_n_1175_, v___x_1285_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = 4;
return v___x_1287_;
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = 3;
return v___x_1288_;
}
}
else
{
uint8_t v___x_1289_; 
v___x_1289_ = 2;
return v___x_1289_;
}
}
else
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_nat_dec_le(v_n_1175_, v___x_1290_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = 1;
return v___x_1292_;
}
else
{
uint8_t v___x_1293_; 
v___x_1293_ = 0;
return v___x_1293_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Method_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1175_ = stack[0].m_obj;
uint8_t v_res_1294_;
v_res_1294_ = l_Std_Http_Method_ofNat(v_n_1175_);
stack->m_num = v_res_1294_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofNat___boxed(lean_object* v_n_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_Std_Http_Method_ofNat(v_n_1295_);
lean_dec(v_n_1295_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
uint8_t l_Std_Http_instDecidableEqMethod(uint8_t v_x_1298_, uint8_t v_y_1299_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1300_ = lean_box(v_x_1298_);
v___x_1301_ = lean_obj_tag_nat(v___x_1300_);
lean_dec(v___x_1300_);
v___x_1302_ = lean_box(v_y_1299_);
v___x_1303_ = lean_obj_tag_nat(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1304_ = lean_nat_dec_eq(v___x_1301_, v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT void l_Std_Http_instDecidableEqMethod_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1298_ = stack[0].m_num;
uint8_t v_y_1299_ = stack[1].m_num;
uint8_t v_res_1305_;
v_res_1305_ = l_Std_Http_instDecidableEqMethod(v_x_1298_, v_y_1299_);
stack->m_num = v_res_1305_;
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableEqMethod___boxed(lean_object* v_x_1306_, lean_object* v_y_1307_){
_start:
{
uint8_t v_x_23__boxed_1308_; uint8_t v_y_24__boxed_1309_; uint8_t v_res_1310_; lean_object* v_r_1311_; 
v_x_23__boxed_1308_ = lean_unbox(v_x_1306_);
v_y_24__boxed_1309_ = lean_unbox(v_y_1307_);
v_res_1310_ = l_Std_Http_instDecidableEqMethod(v_x_23__boxed_1308_, v_y_24__boxed_1309_);
v_r_1311_ = lean_box(v_res_1310_);
return v_r_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f(lean_object* v_x_1472_){
_start:
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
v___x_1474_ = lean_string_dec_eq(v_x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
v___x_1476_ = lean_string_dec_eq(v_x_1472_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
v___x_1478_ = lean_string_dec_eq(v_x_1472_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
v___x_1480_ = lean_string_dec_eq(v_x_1472_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
v___x_1482_ = lean_string_dec_eq(v_x_1472_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
v___x_1484_ = lean_string_dec_eq(v_x_1472_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
v___x_1486_ = lean_string_dec_eq(v_x_1472_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
v___x_1488_ = lean_string_dec_eq(v_x_1472_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
v___x_1490_ = lean_string_dec_eq(v_x_1472_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
v___x_1492_ = lean_string_dec_eq(v_x_1472_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
v___x_1494_ = lean_string_dec_eq(v_x_1472_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
v___x_1496_ = lean_string_dec_eq(v_x_1472_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
v___x_1498_ = lean_string_dec_eq(v_x_1472_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
v___x_1500_ = lean_string_dec_eq(v_x_1472_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
v___x_1502_ = lean_string_dec_eq(v_x_1472_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
v___x_1504_ = lean_string_dec_eq(v_x_1472_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
v___x_1506_ = lean_string_dec_eq(v_x_1472_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
v___x_1508_ = lean_string_dec_eq(v_x_1472_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
v___x_1510_ = lean_string_dec_eq(v_x_1472_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
v___x_1512_ = lean_string_dec_eq(v_x_1472_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
v___x_1514_ = lean_string_dec_eq(v_x_1472_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
v___x_1516_ = lean_string_dec_eq(v_x_1472_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
v___x_1518_ = lean_string_dec_eq(v_x_1472_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
v___x_1520_ = lean_string_dec_eq(v_x_1472_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
v___x_1522_ = lean_string_dec_eq(v_x_1472_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
v___x_1524_ = lean_string_dec_eq(v_x_1472_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
v___x_1526_ = lean_string_dec_eq(v_x_1472_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
v___x_1528_ = lean_string_dec_eq(v_x_1472_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
v___x_1530_ = lean_string_dec_eq(v_x_1472_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
v___x_1532_ = lean_string_dec_eq(v_x_1472_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
v___x_1534_ = lean_string_dec_eq(v_x_1472_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
v___x_1536_ = lean_string_dec_eq(v_x_1472_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
v___x_1538_ = lean_string_dec_eq(v_x_1472_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
v___x_1540_ = lean_string_dec_eq(v_x_1472_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
v___x_1542_ = lean_string_dec_eq(v_x_1472_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
v___x_1544_ = lean_string_dec_eq(v_x_1472_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
v___x_1546_ = lean_string_dec_eq(v_x_1472_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
v___x_1548_ = lean_string_dec_eq(v_x_1472_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
v___x_1550_ = lean_string_dec_eq(v_x_1472_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
v___x_1552_ = lean_string_dec_eq(v_x_1472_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_box(0);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; 
v___x_1554_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__40));
return v___x_1554_;
}
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__41));
return v___x_1555_;
}
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__42));
return v___x_1556_;
}
}
else
{
lean_object* v___x_1557_; 
v___x_1557_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__43));
return v___x_1557_;
}
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__44));
return v___x_1558_;
}
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__45));
return v___x_1559_;
}
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__46));
return v___x_1560_;
}
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__47));
return v___x_1561_;
}
}
else
{
lean_object* v___x_1562_; 
v___x_1562_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__48));
return v___x_1562_;
}
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__49));
return v___x_1563_;
}
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__50));
return v___x_1564_;
}
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__51));
return v___x_1565_;
}
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__52));
return v___x_1566_;
}
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__53));
return v___x_1567_;
}
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__54));
return v___x_1568_;
}
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__55));
return v___x_1569_;
}
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__56));
return v___x_1570_;
}
}
else
{
lean_object* v___x_1571_; 
v___x_1571_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__57));
return v___x_1571_;
}
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__58));
return v___x_1572_;
}
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__59));
return v___x_1573_;
}
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__60));
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__61));
return v___x_1575_;
}
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__62));
return v___x_1576_;
}
}
else
{
lean_object* v___x_1577_; 
v___x_1577_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__63));
return v___x_1577_;
}
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__64));
return v___x_1578_;
}
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__65));
return v___x_1579_;
}
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__66));
return v___x_1580_;
}
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__67));
return v___x_1581_;
}
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__68));
return v___x_1582_;
}
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__69));
return v___x_1583_;
}
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__70));
return v___x_1584_;
}
}
else
{
lean_object* v___x_1585_; 
v___x_1585_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__71));
return v___x_1585_;
}
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__72));
return v___x_1586_;
}
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__73));
return v___x_1587_;
}
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__74));
return v___x_1588_;
}
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__75));
return v___x_1589_;
}
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__76));
return v___x_1590_;
}
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__77));
return v___x_1591_;
}
}
else
{
lean_object* v___x_1592_; 
v___x_1592_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__78));
return v___x_1592_;
}
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__79));
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x3f___boxed(lean_object* v_x_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Std_Http_Method_ofString_x3f(v_x_1594_);
lean_dec_ref(v_x_1594_);
return v_res_1595_;
}
}
uint8_t l_panic___at___00Std_Http_Method_ofString_x21_spec__0(lean_object* v_msg_1596_){
_start:
{
uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1597_ = 0;
v___x_1598_ = lean_box(v___x_1597_);
v___x_1599_ = lean_panic_fn_borrowed(v___x_1598_, v_msg_1596_);
lean_dec(v___x_1598_);
v___x_1600_ = lean_unbox(v___x_1599_);
lean_dec(v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT void l_panic___at___00Std_Http_Method_ofString_x21_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1596_ = stack[0].m_obj;
uint8_t v_res_1601_;
v_res_1601_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v_msg_1596_);
stack->m_num = v_res_1601_;
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Method_ofString_x21_spec__0___boxed(lean_object* v_msg_1602_){
_start:
{
uint8_t v_res_1603_; lean_object* v_r_1604_; 
v_res_1603_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v_msg_1602_);
v_r_1604_ = lean_box(v_res_1603_);
return v_r_1604_;
}
}
uint8_t l_Std_Http_Method_ofString_x21(lean_object* v_s_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Std_Http_Method_ofString_x3f(v_s_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1610_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__0));
v___x_1611_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__1));
v___x_1612_ = lean_unsigned_to_nat(337u);
v___x_1613_ = lean_unsigned_to_nat(12u);
v___x_1614_ = ((lean_object*)(l_Std_Http_Method_ofString_x21___closed__2));
v___x_1615_ = l_String_quote(v_s_1608_);
v___x_1616_ = lean_string_append(v___x_1614_, v___x_1615_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = l_mkPanicMessageWithDecl(v___x_1610_, v___x_1611_, v___x_1612_, v___x_1613_, v___x_1616_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = l_panic___at___00Std_Http_Method_ofString_x21_spec__0(v___x_1617_);
return v___x_1618_;
}
else
{
lean_object* v_val_1619_; uint8_t v___x_1620_; 
lean_dec_ref(v_s_1608_);
v_val_1619_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1620_ = lean_unbox(v_val_1619_);
lean_dec(v_val_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT void l_Std_Http_Method_ofString_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1608_ = stack[0].m_obj;
uint8_t v_res_1621_;
v_res_1621_ = l_Std_Http_Method_ofString_x21(v_s_1608_);
stack->m_num = v_res_1621_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_ofString_x21___boxed(lean_object* v_s_1622_){
_start:
{
uint8_t v_res_1623_; lean_object* v_r_1624_; 
v_res_1623_ = l_Std_Http_Method_ofString_x21(v_s_1622_);
v_r_1624_ = lean_box(v_res_1623_);
return v_r_1624_;
}
}
uint8_t l_Std_Http_Method_isIdempotent(uint8_t v_m_1625_){
_start:
{
uint8_t v___y_1627_; uint8_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = 8;
v___x_1637_ = l_Std_Http_instBEqMethod_beq(v_m_1625_, v___x_1636_);
if (v___x_1637_ == 0)
{
uint8_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = 9;
v___x_1639_ = l_Std_Http_instBEqMethod_beq(v_m_1625_, v___x_1638_);
v___y_1627_ = v___x_1639_;
goto v___jp_1626_;
}
else
{
v___y_1627_ = v___x_1637_;
goto v___jp_1626_;
}
v___jp_1626_:
{
if (v___y_1627_ == 0)
{
uint8_t v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = 27;
v___x_1629_ = l_Std_Http_instBEqMethod_beq(v_m_1625_, v___x_1628_);
if (v___x_1629_ == 0)
{
uint8_t v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = 7;
v___x_1631_ = l_Std_Http_instBEqMethod_beq(v_m_1625_, v___x_1630_);
if (v___x_1631_ == 0)
{
uint8_t v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = 20;
v___x_1633_ = l_Std_Http_instBEqMethod_beq(v_m_1625_, v___x_1632_);
if (v___x_1633_ == 0)
{
uint8_t v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = 32;
v___x_1635_ = l_Std_Http_instBEqMethod_beq(v_m_1625_, v___x_1634_);
return v___x_1635_;
}
else
{
return v___x_1633_;
}
}
else
{
return v___x_1631_;
}
}
else
{
return v___x_1629_;
}
}
else
{
return v___y_1627_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Method_isIdempotent_0interp(lean_interpreter_value* stack)
{
uint8_t v_m_1625_ = stack[0].m_num;
uint8_t v_res_1640_;
v_res_1640_ = l_Std_Http_Method_isIdempotent(v_m_1625_);
stack->m_num = v_res_1640_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_isIdempotent___boxed(lean_object* v_m_1641_){
_start:
{
uint8_t v_m_boxed_1642_; uint8_t v_res_1643_; lean_object* v_r_1644_; 
v_m_boxed_1642_ = lean_unbox(v_m_1641_);
v_res_1643_ = l_Std_Http_Method_isIdempotent(v_m_boxed_1642_);
v_r_1644_ = lean_box(v_res_1643_);
return v_r_1644_;
}
}
uint8_t l_Std_Http_Method_isSafe(uint8_t v_m_1645_){
_start:
{
uint8_t v___y_1647_; uint8_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = 8;
v___x_1653_ = l_Std_Http_instBEqMethod_beq(v_m_1645_, v___x_1652_);
if (v___x_1653_ == 0)
{
uint8_t v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = 9;
v___x_1655_ = l_Std_Http_instBEqMethod_beq(v_m_1645_, v___x_1654_);
v___y_1647_ = v___x_1655_;
goto v___jp_1646_;
}
else
{
v___y_1647_ = v___x_1653_;
goto v___jp_1646_;
}
v___jp_1646_:
{
if (v___y_1647_ == 0)
{
uint8_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = 20;
v___x_1649_ = l_Std_Http_instBEqMethod_beq(v_m_1645_, v___x_1648_);
if (v___x_1649_ == 0)
{
uint8_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = 32;
v___x_1651_ = l_Std_Http_instBEqMethod_beq(v_m_1645_, v___x_1650_);
return v___x_1651_;
}
else
{
return v___x_1649_;
}
}
else
{
return v___y_1647_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Method_isSafe_0interp(lean_interpreter_value* stack)
{
uint8_t v_m_1645_ = stack[0].m_num;
uint8_t v_res_1656_;
v_res_1656_ = l_Std_Http_Method_isSafe(v_m_1645_);
stack->m_num = v_res_1656_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_isSafe___boxed(lean_object* v_m_1657_){
_start:
{
uint8_t v_m_boxed_1658_; uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_m_boxed_1658_ = lean_unbox(v_m_1657_);
v_res_1659_ = l_Std_Http_Method_isSafe(v_m_boxed_1658_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
lean_object* l_Std_Http_Method_instToString___lam__0(uint8_t v_x_1661_){
_start:
{
switch(v_x_1661_)
{
case 0:
{
lean_object* v___x_1662_; 
v___x_1662_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
return v___x_1662_;
}
case 1:
{
lean_object* v___x_1663_; 
v___x_1663_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
return v___x_1663_;
}
case 2:
{
lean_object* v___x_1664_; 
v___x_1664_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
return v___x_1664_;
}
case 3:
{
lean_object* v___x_1665_; 
v___x_1665_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
return v___x_1665_;
}
case 4:
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
return v___x_1666_;
}
case 5:
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
return v___x_1667_;
}
case 6:
{
lean_object* v___x_1668_; 
v___x_1668_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
return v___x_1668_;
}
case 7:
{
lean_object* v___x_1669_; 
v___x_1669_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
return v___x_1669_;
}
case 8:
{
lean_object* v___x_1670_; 
v___x_1670_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
return v___x_1670_;
}
case 9:
{
lean_object* v___x_1671_; 
v___x_1671_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
return v___x_1671_;
}
case 10:
{
lean_object* v___x_1672_; 
v___x_1672_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
return v___x_1672_;
}
case 11:
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
return v___x_1673_;
}
case 12:
{
lean_object* v___x_1674_; 
v___x_1674_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
return v___x_1674_;
}
case 13:
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
return v___x_1675_;
}
case 14:
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
return v___x_1676_;
}
case 15:
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
return v___x_1677_;
}
case 16:
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
return v___x_1678_;
}
case 17:
{
lean_object* v___x_1679_; 
v___x_1679_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
return v___x_1679_;
}
case 18:
{
lean_object* v___x_1680_; 
v___x_1680_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
return v___x_1680_;
}
case 19:
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
return v___x_1681_;
}
case 20:
{
lean_object* v___x_1682_; 
v___x_1682_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
return v___x_1682_;
}
case 21:
{
lean_object* v___x_1683_; 
v___x_1683_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
return v___x_1683_;
}
case 22:
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
return v___x_1684_;
}
case 23:
{
lean_object* v___x_1685_; 
v___x_1685_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
return v___x_1685_;
}
case 24:
{
lean_object* v___x_1686_; 
v___x_1686_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
return v___x_1686_;
}
case 25:
{
lean_object* v___x_1687_; 
v___x_1687_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
return v___x_1687_;
}
case 26:
{
lean_object* v___x_1688_; 
v___x_1688_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
return v___x_1688_;
}
case 27:
{
lean_object* v___x_1689_; 
v___x_1689_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
return v___x_1689_;
}
case 28:
{
lean_object* v___x_1690_; 
v___x_1690_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
return v___x_1690_;
}
case 29:
{
lean_object* v___x_1691_; 
v___x_1691_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
return v___x_1691_;
}
case 30:
{
lean_object* v___x_1692_; 
v___x_1692_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
return v___x_1692_;
}
case 31:
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
return v___x_1693_;
}
case 32:
{
lean_object* v___x_1694_; 
v___x_1694_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
return v___x_1694_;
}
case 33:
{
lean_object* v___x_1695_; 
v___x_1695_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
return v___x_1695_;
}
case 34:
{
lean_object* v___x_1696_; 
v___x_1696_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
return v___x_1696_;
}
case 35:
{
lean_object* v___x_1697_; 
v___x_1697_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
return v___x_1697_;
}
case 36:
{
lean_object* v___x_1698_; 
v___x_1698_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
return v___x_1698_;
}
case 37:
{
lean_object* v___x_1699_; 
v___x_1699_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
return v___x_1699_;
}
case 38:
{
lean_object* v___x_1700_; 
v___x_1700_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
return v___x_1700_;
}
default: 
{
lean_object* v___x_1701_; 
v___x_1701_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
return v___x_1701_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Method_instToString___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1661_ = stack[0].m_num;
lean_object* v_res_1702_;
v_res_1702_ = l_Std_Http_Method_instToString___lam__0(v_x_1661_);
stack->m_obj
 = v_res_1702_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instToString___lam__0___boxed(lean_object* v_x_1703_){
_start:
{
uint8_t v_x_366__boxed_1704_; lean_object* v_res_1705_; 
v_x_366__boxed_1704_ = lean_unbox(v_x_1703_);
v_res_1705_ = l_Std_Http_Method_instToString___lam__0(v_x_366__boxed_1704_);
return v_res_1705_;
}
}
lean_object* l_Std_Http_Method_instEncodeV11___lam__0(lean_object* v_buffer_1708_, uint8_t v___y_1709_){
_start:
{
lean_object* v___y_1711_; 
switch(v___y_1709_)
{
case 0:
{
lean_object* v___x_1725_; 
v___x_1725_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__0));
v___y_1711_ = v___x_1725_;
goto v___jp_1710_;
}
case 1:
{
lean_object* v___x_1726_; 
v___x_1726_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__1));
v___y_1711_ = v___x_1726_;
goto v___jp_1710_;
}
case 2:
{
lean_object* v___x_1727_; 
v___x_1727_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__2));
v___y_1711_ = v___x_1727_;
goto v___jp_1710_;
}
case 3:
{
lean_object* v___x_1728_; 
v___x_1728_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__3));
v___y_1711_ = v___x_1728_;
goto v___jp_1710_;
}
case 4:
{
lean_object* v___x_1729_; 
v___x_1729_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__4));
v___y_1711_ = v___x_1729_;
goto v___jp_1710_;
}
case 5:
{
lean_object* v___x_1730_; 
v___x_1730_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__5));
v___y_1711_ = v___x_1730_;
goto v___jp_1710_;
}
case 6:
{
lean_object* v___x_1731_; 
v___x_1731_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__6));
v___y_1711_ = v___x_1731_;
goto v___jp_1710_;
}
case 7:
{
lean_object* v___x_1732_; 
v___x_1732_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__7));
v___y_1711_ = v___x_1732_;
goto v___jp_1710_;
}
case 8:
{
lean_object* v___x_1733_; 
v___x_1733_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__8));
v___y_1711_ = v___x_1733_;
goto v___jp_1710_;
}
case 9:
{
lean_object* v___x_1734_; 
v___x_1734_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__9));
v___y_1711_ = v___x_1734_;
goto v___jp_1710_;
}
case 10:
{
lean_object* v___x_1735_; 
v___x_1735_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__10));
v___y_1711_ = v___x_1735_;
goto v___jp_1710_;
}
case 11:
{
lean_object* v___x_1736_; 
v___x_1736_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__11));
v___y_1711_ = v___x_1736_;
goto v___jp_1710_;
}
case 12:
{
lean_object* v___x_1737_; 
v___x_1737_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__12));
v___y_1711_ = v___x_1737_;
goto v___jp_1710_;
}
case 13:
{
lean_object* v___x_1738_; 
v___x_1738_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__13));
v___y_1711_ = v___x_1738_;
goto v___jp_1710_;
}
case 14:
{
lean_object* v___x_1739_; 
v___x_1739_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__14));
v___y_1711_ = v___x_1739_;
goto v___jp_1710_;
}
case 15:
{
lean_object* v___x_1740_; 
v___x_1740_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__15));
v___y_1711_ = v___x_1740_;
goto v___jp_1710_;
}
case 16:
{
lean_object* v___x_1741_; 
v___x_1741_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__16));
v___y_1711_ = v___x_1741_;
goto v___jp_1710_;
}
case 17:
{
lean_object* v___x_1742_; 
v___x_1742_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__17));
v___y_1711_ = v___x_1742_;
goto v___jp_1710_;
}
case 18:
{
lean_object* v___x_1743_; 
v___x_1743_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__18));
v___y_1711_ = v___x_1743_;
goto v___jp_1710_;
}
case 19:
{
lean_object* v___x_1744_; 
v___x_1744_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__19));
v___y_1711_ = v___x_1744_;
goto v___jp_1710_;
}
case 20:
{
lean_object* v___x_1745_; 
v___x_1745_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__20));
v___y_1711_ = v___x_1745_;
goto v___jp_1710_;
}
case 21:
{
lean_object* v___x_1746_; 
v___x_1746_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__21));
v___y_1711_ = v___x_1746_;
goto v___jp_1710_;
}
case 22:
{
lean_object* v___x_1747_; 
v___x_1747_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__22));
v___y_1711_ = v___x_1747_;
goto v___jp_1710_;
}
case 23:
{
lean_object* v___x_1748_; 
v___x_1748_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__23));
v___y_1711_ = v___x_1748_;
goto v___jp_1710_;
}
case 24:
{
lean_object* v___x_1749_; 
v___x_1749_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__24));
v___y_1711_ = v___x_1749_;
goto v___jp_1710_;
}
case 25:
{
lean_object* v___x_1750_; 
v___x_1750_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__25));
v___y_1711_ = v___x_1750_;
goto v___jp_1710_;
}
case 26:
{
lean_object* v___x_1751_; 
v___x_1751_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__26));
v___y_1711_ = v___x_1751_;
goto v___jp_1710_;
}
case 27:
{
lean_object* v___x_1752_; 
v___x_1752_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__27));
v___y_1711_ = v___x_1752_;
goto v___jp_1710_;
}
case 28:
{
lean_object* v___x_1753_; 
v___x_1753_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__28));
v___y_1711_ = v___x_1753_;
goto v___jp_1710_;
}
case 29:
{
lean_object* v___x_1754_; 
v___x_1754_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__29));
v___y_1711_ = v___x_1754_;
goto v___jp_1710_;
}
case 30:
{
lean_object* v___x_1755_; 
v___x_1755_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__30));
v___y_1711_ = v___x_1755_;
goto v___jp_1710_;
}
case 31:
{
lean_object* v___x_1756_; 
v___x_1756_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__31));
v___y_1711_ = v___x_1756_;
goto v___jp_1710_;
}
case 32:
{
lean_object* v___x_1757_; 
v___x_1757_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__32));
v___y_1711_ = v___x_1757_;
goto v___jp_1710_;
}
case 33:
{
lean_object* v___x_1758_; 
v___x_1758_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__33));
v___y_1711_ = v___x_1758_;
goto v___jp_1710_;
}
case 34:
{
lean_object* v___x_1759_; 
v___x_1759_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__34));
v___y_1711_ = v___x_1759_;
goto v___jp_1710_;
}
case 35:
{
lean_object* v___x_1760_; 
v___x_1760_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__35));
v___y_1711_ = v___x_1760_;
goto v___jp_1710_;
}
case 36:
{
lean_object* v___x_1761_; 
v___x_1761_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__36));
v___y_1711_ = v___x_1761_;
goto v___jp_1710_;
}
case 37:
{
lean_object* v___x_1762_; 
v___x_1762_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__37));
v___y_1711_ = v___x_1762_;
goto v___jp_1710_;
}
case 38:
{
lean_object* v___x_1763_; 
v___x_1763_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__38));
v___y_1711_ = v___x_1763_;
goto v___jp_1710_;
}
default: 
{
lean_object* v___x_1764_; 
v___x_1764_ = ((lean_object*)(l_Std_Http_Method_ofString_x3f___closed__39));
v___y_1711_ = v___x_1764_;
goto v___jp_1710_;
}
}
v___jp_1710_:
{
lean_object* v_data_1712_; lean_object* v_size_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1724_; 
v_data_1712_ = lean_ctor_get(v_buffer_1708_, 0);
v_size_1713_ = lean_ctor_get(v_buffer_1708_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_buffer_1708_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1715_ = v_buffer_1708_;
v_isShared_1716_ = v_isSharedCheck_1724_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_size_1713_);
lean_inc(v_data_1712_);
lean_dec(v_buffer_1708_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1724_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1717_ = lean_string_to_utf8(v___y_1711_);
lean_inc_ref(v___x_1717_);
v___x_1718_ = lean_array_push(v_data_1712_, v___x_1717_);
v___x_1719_ = lean_byte_array_size(v___x_1717_);
lean_dec_ref(v___x_1717_);
v___x_1720_ = lean_nat_add(v_size_1713_, v___x_1719_);
lean_dec(v_size_1713_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1720_);
lean_ctor_set(v___x_1715_, 0, v___x_1718_);
v___x_1722_ = v___x_1715_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Method_instEncodeV11___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_buffer_1708_ = stack[0].m_obj;
uint8_t v___y_1709_ = stack[1].m_num;
lean_object* v_res_1765_;
v_res_1765_ = l_Std_Http_Method_instEncodeV11___lam__0(v_buffer_1708_, v___y_1709_);
stack->m_obj
 = v_res_1765_;
}
LEAN_EXPORT lean_object* l_Std_Http_Method_instEncodeV11___lam__0___boxed(lean_object* v_buffer_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v___y_192__boxed_1768_; lean_object* v_res_1769_; 
v___y_192__boxed_1768_ = lean_unbox(v___y_1767_);
v_res_1769_ = l_Std_Http_Method_instEncodeV11___lam__0(v_buffer_1766_, v___y_192__boxed_1768_);
return v_res_1769_;
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
