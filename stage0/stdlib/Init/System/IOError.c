// Lean compiler output
// Module: Init.System.IOError
// Imports: public import Init.Data.ToString.Basic import Init.Data.String.Modify
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_alreadyExists_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_alreadyExists_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_otherError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_otherError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_resourceBusy_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_resourceBusy_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_resourceVanished_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_resourceVanished_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_unsupportedOperation_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_unsupportedOperation_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_hardwareFault_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_hardwareFault_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_unsatisfiedConstraints_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_unsatisfiedConstraints_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_illegalOperation_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_illegalOperation_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_protocolError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_protocolError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_timeExpired_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_timeExpired_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_interrupted_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_interrupted_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_noFileOrDirectory_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_noFileOrDirectory_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_invalidArgument_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_invalidArgument_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_permissionDenied_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_permissionDenied_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_resourceExhausted_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_resourceExhausted_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_inappropriateType_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_inappropriateType_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_noSuchThing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_noSuchThing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_unexpectedEof_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_unexpectedEof_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_userError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_userError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instInhabitedError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_instInhabitedError___closed__0 = (const lean_object*)&l_instInhabitedError___closed__0_value;
static const lean_ctor_object l_instInhabitedError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_instInhabitedError___closed__0_value)}};
static const lean_object* l_instInhabitedError___closed__1 = (const lean_object*)&l_instInhabitedError___closed__1_value;
LEAN_EXPORT const lean_object* l_instInhabitedError = (const lean_object*)&l_instInhabitedError___closed__1_value;
LEAN_EXPORT lean_object* lean_mk_io_user_error(lean_object*);
static const lean_closure_object l_instCoeStringError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lean_mk_io_user_error, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instCoeStringError___closed__0 = (const lean_object*)&l_instCoeStringError___closed__0_value;
LEAN_EXPORT const lean_object* l_instCoeStringError = (const lean_object*)&l_instCoeStringError___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists_file(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExistsFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkEofError___redArg();
LEAN_EXPORT lean_object* l_IO_Error_mkEofError___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_eof(lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type_file(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_interrupted(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkInterrupted___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument_file(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_no_file_or_directory(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing_file(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied_file(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted_file(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_unsupported_operation(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThing___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_resource_vanished(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_resource_busy(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_other_error(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkOtherError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_hardware_fault(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_illegal_operation(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_protocol_error(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkProtocolError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_io_error_time_expired(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object*);
static const lean_string_object l_IO_Error_fopenErrorToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " (error code: "};
static const lean_object* l_IO_Error_fopenErrorToString___closed__0 = (const lean_object*)&l_IO_Error_fopenErrorToString___closed__0_value;
static const lean_string_object l_IO_Error_fopenErrorToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ")\n  file: "};
static const lean_object* l_IO_Error_fopenErrorToString___closed__1 = (const lean_object*)&l_IO_Error_fopenErrorToString___closed__1_value;
static const lean_string_object l_IO_Error_fopenErrorToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_IO_Error_fopenErrorToString___closed__2 = (const lean_object*)&l_IO_Error_fopenErrorToString___closed__2_value;
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_Error_otherErrorToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_IO_Error_otherErrorToString___closed__0 = (const lean_object*)&l_IO_Error_otherErrorToString___closed__0_value;
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_Error_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "already exists"};
static const lean_object* l_IO_Error_toString___closed__0 = (const lean_object*)&l_IO_Error_toString___closed__0_value;
static const lean_string_object l_IO_Error_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "resource busy"};
static const lean_object* l_IO_Error_toString___closed__1 = (const lean_object*)&l_IO_Error_toString___closed__1_value;
static const lean_string_object l_IO_Error_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "resource vanished"};
static const lean_object* l_IO_Error_toString___closed__2 = (const lean_object*)&l_IO_Error_toString___closed__2_value;
static const lean_string_object l_IO_Error_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unsupported operation"};
static const lean_object* l_IO_Error_toString___closed__3 = (const lean_object*)&l_IO_Error_toString___closed__3_value;
static const lean_string_object l_IO_Error_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hardware fault"};
static const lean_object* l_IO_Error_toString___closed__4 = (const lean_object*)&l_IO_Error_toString___closed__4_value;
static const lean_string_object l_IO_Error_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "directory not empty"};
static const lean_object* l_IO_Error_toString___closed__5 = (const lean_object*)&l_IO_Error_toString___closed__5_value;
static const lean_string_object l_IO_Error_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "illegal operation"};
static const lean_object* l_IO_Error_toString___closed__6 = (const lean_object*)&l_IO_Error_toString___closed__6_value;
static const lean_string_object l_IO_Error_toString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "protocol error"};
static const lean_object* l_IO_Error_toString___closed__7 = (const lean_object*)&l_IO_Error_toString___closed__7_value;
static const lean_string_object l_IO_Error_toString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "time expired"};
static const lean_object* l_IO_Error_toString___closed__8 = (const lean_object*)&l_IO_Error_toString___closed__8_value;
static const lean_string_object l_IO_Error_toString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "interrupted system call"};
static const lean_object* l_IO_Error_toString___closed__9 = (const lean_object*)&l_IO_Error_toString___closed__9_value;
static const lean_string_object l_IO_Error_toString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "no such file or directory"};
static const lean_object* l_IO_Error_toString___closed__10 = (const lean_object*)&l_IO_Error_toString___closed__10_value;
static const lean_string_object l_IO_Error_toString___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invalid argument"};
static const lean_object* l_IO_Error_toString___closed__11 = (const lean_object*)&l_IO_Error_toString___closed__11_value;
static const lean_string_object l_IO_Error_toString___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "resource exhausted"};
static const lean_object* l_IO_Error_toString___closed__12 = (const lean_object*)&l_IO_Error_toString___closed__12_value;
static const lean_string_object l_IO_Error_toString___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "inappropriate type"};
static const lean_object* l_IO_Error_toString___closed__13 = (const lean_object*)&l_IO_Error_toString___closed__13_value;
static const lean_string_object l_IO_Error_toString___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "no such thing"};
static const lean_object* l_IO_Error_toString___closed__14 = (const lean_object*)&l_IO_Error_toString___closed__14_value;
static const lean_string_object l_IO_Error_toString___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "end of file"};
static const lean_object* l_IO_Error_toString___closed__15 = (const lean_object*)&l_IO_Error_toString___closed__15_value;
LEAN_EXPORT lean_object* lean_io_error_to_string(lean_object*);
static const lean_closure_object l_IO_Error_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lean_io_error_to_string, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_Error_instToString___closed__0 = (const lean_object*)&l_IO_Error_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_Error_instToString = (const lean_object*)&l_IO_Error_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_IO_Error_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_filename_7_; uint32_t v_osCode_8_; lean_object* v_details_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_filename_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_filename_7_);
v_osCode_8_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*2);
v_details_9_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_details_9_);
lean_dec_ref_known(v_t_5_, 2);
v___x_10_ = lean_box_uint32(v_osCode_8_);
v___x_11_ = lean_apply_3(v_k_6_, v_filename_7_, v___x_10_, v_details_9_);
return v___x_11_;
}
case 10:
{
lean_object* v_filename_12_; uint32_t v_osCode_13_; lean_object* v_details_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_filename_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_filename_12_);
v_osCode_13_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*2);
v_details_14_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_details_14_);
lean_dec_ref_known(v_t_5_, 2);
v___x_15_ = lean_box_uint32(v_osCode_13_);
v___x_16_ = lean_apply_3(v_k_6_, v_filename_12_, v___x_15_, v_details_14_);
return v___x_16_;
}
case 11:
{
lean_object* v_filename_17_; uint32_t v_osCode_18_; lean_object* v_details_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_filename_17_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_filename_17_);
v_osCode_18_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*2);
v_details_19_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_details_19_);
lean_dec_ref_known(v_t_5_, 2);
v___x_20_ = lean_box_uint32(v_osCode_18_);
v___x_21_ = lean_apply_3(v_k_6_, v_filename_17_, v___x_20_, v_details_19_);
return v___x_21_;
}
case 12:
{
lean_object* v_filename_22_; uint32_t v_osCode_23_; lean_object* v_details_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_filename_22_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_filename_22_);
v_osCode_23_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*2);
v_details_24_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_details_24_);
lean_dec_ref_known(v_t_5_, 2);
v___x_25_ = lean_box_uint32(v_osCode_23_);
v___x_26_ = lean_apply_3(v_k_6_, v_filename_22_, v___x_25_, v_details_24_);
return v___x_26_;
}
case 13:
{
lean_object* v_filename_27_; uint32_t v_osCode_28_; lean_object* v_details_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_filename_27_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_filename_27_);
v_osCode_28_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*2);
v_details_29_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_details_29_);
lean_dec_ref_known(v_t_5_, 2);
v___x_30_ = lean_box_uint32(v_osCode_28_);
v___x_31_ = lean_apply_3(v_k_6_, v_filename_27_, v___x_30_, v_details_29_);
return v___x_31_;
}
case 14:
{
lean_object* v_filename_32_; uint32_t v_osCode_33_; lean_object* v_details_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_filename_32_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_filename_32_);
v_osCode_33_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*2);
v_details_34_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_details_34_);
lean_dec_ref_known(v_t_5_, 2);
v___x_35_ = lean_box_uint32(v_osCode_33_);
v___x_36_ = lean_apply_3(v_k_6_, v_filename_32_, v___x_35_, v_details_34_);
return v___x_36_;
}
case 15:
{
lean_object* v_filename_37_; uint32_t v_osCode_38_; lean_object* v_details_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_filename_37_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_filename_37_);
v_osCode_38_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*2);
v_details_39_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_details_39_);
lean_dec_ref_known(v_t_5_, 2);
v___x_40_ = lean_box_uint32(v_osCode_38_);
v___x_41_ = lean_apply_3(v_k_6_, v_filename_37_, v___x_40_, v_details_39_);
return v___x_41_;
}
case 16:
{
lean_object* v_filename_42_; uint32_t v_osCode_43_; lean_object* v_details_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_filename_42_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_filename_42_);
v_osCode_43_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*2);
v_details_44_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_details_44_);
lean_dec_ref_known(v_t_5_, 2);
v___x_45_ = lean_box_uint32(v_osCode_43_);
v___x_46_ = lean_apply_3(v_k_6_, v_filename_42_, v___x_45_, v_details_44_);
return v___x_46_;
}
case 17:
{
return v_k_6_;
}
case 18:
{
lean_object* v_msg_47_; lean_object* v___x_48_; 
v_msg_47_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_msg_47_);
lean_dec_ref_known(v_t_5_, 1);
v___x_48_ = lean_apply_1(v_k_6_, v_msg_47_);
return v___x_48_;
}
default: 
{
uint32_t v_osCode_49_; lean_object* v_details_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_osCode_49_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*1);
v_details_50_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_details_50_);
lean_dec(v_t_5_);
v___x_51_ = lean_box_uint32(v_osCode_49_);
v___x_52_ = lean_apply_2(v_k_6_, v___x_51_, v_details_50_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim(lean_object* v_motive_53_, lean_object* v_ctorIdx_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_k_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_IO_Error_ctorElim___redArg(v_t_55_, v_k_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim___boxed(lean_object* v_motive_59_, lean_object* v_ctorIdx_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_k_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_IO_Error_ctorElim(v_motive_59_, v_ctorIdx_60_, v_t_61_, v_h_62_, v_k_63_);
lean_dec(v_ctorIdx_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_alreadyExists_elim___redArg(lean_object* v_t_65_, lean_object* v_alreadyExists_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_IO_Error_ctorElim___redArg(v_t_65_, v_alreadyExists_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_alreadyExists_elim(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_alreadyExists_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_IO_Error_ctorElim___redArg(v_t_69_, v_alreadyExists_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherError_elim___redArg(lean_object* v_t_73_, lean_object* v_otherError_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_IO_Error_ctorElim___redArg(v_t_73_, v_otherError_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherError_elim(lean_object* v_motive_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_otherError_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_IO_Error_ctorElim___redArg(v_t_77_, v_otherError_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceBusy_elim___redArg(lean_object* v_t_81_, lean_object* v_resourceBusy_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_IO_Error_ctorElim___redArg(v_t_81_, v_resourceBusy_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceBusy_elim(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_resourceBusy_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_IO_Error_ctorElim___redArg(v_t_85_, v_resourceBusy_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceVanished_elim___redArg(lean_object* v_t_89_, lean_object* v_resourceVanished_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_IO_Error_ctorElim___redArg(v_t_89_, v_resourceVanished_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceVanished_elim(lean_object* v_motive_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_resourceVanished_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_IO_Error_ctorElim___redArg(v_t_93_, v_resourceVanished_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsupportedOperation_elim___redArg(lean_object* v_t_97_, lean_object* v_unsupportedOperation_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_IO_Error_ctorElim___redArg(v_t_97_, v_unsupportedOperation_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsupportedOperation_elim(lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_unsupportedOperation_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_IO_Error_ctorElim___redArg(v_t_101_, v_unsupportedOperation_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_hardwareFault_elim___redArg(lean_object* v_t_105_, lean_object* v_hardwareFault_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_IO_Error_ctorElim___redArg(v_t_105_, v_hardwareFault_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_hardwareFault_elim(lean_object* v_motive_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_hardwareFault_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_IO_Error_ctorElim___redArg(v_t_109_, v_hardwareFault_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsatisfiedConstraints_elim___redArg(lean_object* v_t_113_, lean_object* v_unsatisfiedConstraints_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_IO_Error_ctorElim___redArg(v_t_113_, v_unsatisfiedConstraints_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsatisfiedConstraints_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_unsatisfiedConstraints_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_IO_Error_ctorElim___redArg(v_t_117_, v_unsatisfiedConstraints_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_illegalOperation_elim___redArg(lean_object* v_t_121_, lean_object* v_illegalOperation_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_IO_Error_ctorElim___redArg(v_t_121_, v_illegalOperation_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_illegalOperation_elim(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_illegalOperation_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_IO_Error_ctorElim___redArg(v_t_125_, v_illegalOperation_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_protocolError_elim___redArg(lean_object* v_t_129_, lean_object* v_protocolError_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_IO_Error_ctorElim___redArg(v_t_129_, v_protocolError_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_protocolError_elim(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_protocolError_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_IO_Error_ctorElim___redArg(v_t_133_, v_protocolError_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_timeExpired_elim___redArg(lean_object* v_t_137_, lean_object* v_timeExpired_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_IO_Error_ctorElim___redArg(v_t_137_, v_timeExpired_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_timeExpired_elim(lean_object* v_motive_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_timeExpired_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_IO_Error_ctorElim___redArg(v_t_141_, v_timeExpired_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_interrupted_elim___redArg(lean_object* v_t_145_, lean_object* v_interrupted_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_IO_Error_ctorElim___redArg(v_t_145_, v_interrupted_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_interrupted_elim(lean_object* v_motive_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_interrupted_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_IO_Error_ctorElim___redArg(v_t_149_, v_interrupted_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noFileOrDirectory_elim___redArg(lean_object* v_t_153_, lean_object* v_noFileOrDirectory_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_IO_Error_ctorElim___redArg(v_t_153_, v_noFileOrDirectory_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noFileOrDirectory_elim(lean_object* v_motive_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_noFileOrDirectory_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_IO_Error_ctorElim___redArg(v_t_157_, v_noFileOrDirectory_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_invalidArgument_elim___redArg(lean_object* v_t_161_, lean_object* v_invalidArgument_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_IO_Error_ctorElim___redArg(v_t_161_, v_invalidArgument_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_invalidArgument_elim(lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_invalidArgument_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_IO_Error_ctorElim___redArg(v_t_165_, v_invalidArgument_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_permissionDenied_elim___redArg(lean_object* v_t_169_, lean_object* v_permissionDenied_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_IO_Error_ctorElim___redArg(v_t_169_, v_permissionDenied_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_permissionDenied_elim(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_permissionDenied_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_IO_Error_ctorElim___redArg(v_t_173_, v_permissionDenied_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceExhausted_elim___redArg(lean_object* v_t_177_, lean_object* v_resourceExhausted_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_IO_Error_ctorElim___redArg(v_t_177_, v_resourceExhausted_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceExhausted_elim(lean_object* v_motive_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_resourceExhausted_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_IO_Error_ctorElim___redArg(v_t_181_, v_resourceExhausted_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_inappropriateType_elim___redArg(lean_object* v_t_185_, lean_object* v_inappropriateType_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_IO_Error_ctorElim___redArg(v_t_185_, v_inappropriateType_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_inappropriateType_elim(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_inappropriateType_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_IO_Error_ctorElim___redArg(v_t_189_, v_inappropriateType_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noSuchThing_elim___redArg(lean_object* v_t_193_, lean_object* v_noSuchThing_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_IO_Error_ctorElim___redArg(v_t_193_, v_noSuchThing_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noSuchThing_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_noSuchThing_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_IO_Error_ctorElim___redArg(v_t_197_, v_noSuchThing_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unexpectedEof_elim___redArg(lean_object* v_t_201_, lean_object* v_unexpectedEof_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_IO_Error_ctorElim___redArg(v_t_201_, v_unexpectedEof_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unexpectedEof_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_unexpectedEof_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_IO_Error_ctorElim___redArg(v_t_205_, v_unexpectedEof_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_userError_elim___redArg(lean_object* v_t_209_, lean_object* v_userError_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_IO_Error_ctorElim___redArg(v_t_209_, v_userError_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_userError_elim(lean_object* v_motive_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_userError_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_IO_Error_ctorElim___redArg(v_t_213_, v_userError_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_user_error(lean_object* v_s_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_222_, 0, v_s_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists_file(lean_object* v_a_225_, uint32_t v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_a_225_);
v___x_229_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_a_227_);
lean_ctor_set_uint32(v___x_229_, sizeof(void*)*2, v_a_226_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExistsFile___boxed(lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
uint32_t v_a_20__boxed_233_; lean_object* v_res_234_; 
v_a_20__boxed_233_ = lean_unbox_uint32(v_a_231_);
lean_dec(v_a_231_);
v_res_234_ = lean_mk_io_error_already_exists_file(v_a_230_, v_a_20__boxed_233_, v_a_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkEofError___redArg(){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(17);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkEofError___redArg___boxed(lean_object* v___dummy_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_IO_Error_mkEofError___redArg();
return v_res_238_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_eof(lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(17);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type_file(lean_object* v_a_241_, uint32_t v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_a_241_);
v___x_245_ = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_a_243_);
lean_ctor_set_uint32(v___x_245_, sizeof(void*)*2, v_a_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
uint32_t v_a_20__boxed_249_; lean_object* v_res_250_; 
v_a_20__boxed_249_ = lean_unbox_uint32(v_a_247_);
lean_dec(v_a_247_);
v_res_250_ = lean_mk_io_error_inappropriate_type_file(v_a_246_, v_a_20__boxed_249_, v_a_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_interrupted(lean_object* v_filename_251_, uint32_t v_osCode_252_, lean_object* v_details_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(10, 2, 4);
lean_ctor_set(v___x_254_, 0, v_filename_251_);
lean_ctor_set(v___x_254_, 1, v_details_253_);
lean_ctor_set_uint32(v___x_254_, sizeof(void*)*2, v_osCode_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInterrupted___boxed(lean_object* v_filename_255_, lean_object* v_osCode_256_, lean_object* v_details_257_){
_start:
{
uint32_t v_osCode_boxed_258_; lean_object* v_res_259_; 
v_osCode_boxed_258_ = lean_unbox_uint32(v_osCode_256_);
lean_dec(v_osCode_256_);
v_res_259_ = lean_mk_io_error_interrupted(v_filename_255_, v_osCode_boxed_258_, v_details_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument_file(lean_object* v_a_260_, uint32_t v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_a_260_);
v___x_264_ = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_a_262_);
lean_ctor_set_uint32(v___x_264_, sizeof(void*)*2, v_a_261_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
uint32_t v_a_20__boxed_268_; lean_object* v_res_269_; 
v_a_20__boxed_268_ = lean_unbox_uint32(v_a_266_);
lean_dec(v_a_266_);
v_res_269_ = lean_mk_io_error_invalid_argument_file(v_a_265_, v_a_20__boxed_268_, v_a_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_file_or_directory(lean_object* v_filename_270_, uint32_t v_osCode_271_, lean_object* v_details_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_273_, 0, v_filename_270_);
lean_ctor_set(v___x_273_, 1, v_details_272_);
lean_ctor_set_uint32(v___x_273_, sizeof(void*)*2, v_osCode_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object* v_filename_274_, lean_object* v_osCode_275_, lean_object* v_details_276_){
_start:
{
uint32_t v_osCode_boxed_277_; lean_object* v_res_278_; 
v_osCode_boxed_277_ = lean_unbox_uint32(v_osCode_275_);
lean_dec(v_osCode_275_);
v_res_278_ = lean_mk_io_error_no_file_or_directory(v_filename_274_, v_osCode_boxed_277_, v_details_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing_file(lean_object* v_a_279_, uint32_t v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v_a_279_);
v___x_283_ = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_a_281_);
lean_ctor_set_uint32(v___x_283_, sizeof(void*)*2, v_a_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
uint32_t v_a_20__boxed_287_; lean_object* v_res_288_; 
v_a_20__boxed_287_ = lean_unbox_uint32(v_a_285_);
lean_dec(v_a_285_);
v_res_288_ = lean_mk_io_error_no_such_thing_file(v_a_284_, v_a_20__boxed_287_, v_a_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied_file(lean_object* v_a_289_, uint32_t v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v_a_289_);
v___x_293_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_a_291_);
lean_ctor_set_uint32(v___x_293_, sizeof(void*)*2, v_a_290_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
uint32_t v_a_20__boxed_297_; lean_object* v_res_298_; 
v_a_20__boxed_297_ = lean_unbox_uint32(v_a_295_);
lean_dec(v_a_295_);
v_res_298_ = lean_mk_io_error_permission_denied_file(v_a_294_, v_a_20__boxed_297_, v_a_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted_file(lean_object* v_a_299_, uint32_t v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v_a_299_);
v___x_303_ = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_a_301_);
lean_ctor_set_uint32(v___x_303_, sizeof(void*)*2, v_a_300_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
uint32_t v_a_20__boxed_307_; lean_object* v_res_308_; 
v_a_20__boxed_307_ = lean_unbox_uint32(v_a_305_);
lean_dec(v_a_305_);
v_res_308_ = lean_mk_io_error_resource_exhausted_file(v_a_304_, v_a_20__boxed_307_, v_a_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_unsupported_operation(uint32_t v_osCode_309_, lean_object* v_details_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = lean_alloc_ctor(4, 1, 4);
lean_ctor_set(v___x_311_, 0, v_details_310_);
lean_ctor_set_uint32(v___x_311_, sizeof(void*)*1, v_osCode_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object* v_osCode_312_, lean_object* v_details_313_){
_start:
{
uint32_t v_osCode_boxed_314_; lean_object* v_res_315_; 
v_osCode_boxed_314_ = lean_unbox_uint32(v_osCode_312_);
lean_dec(v_osCode_312_);
v_res_315_ = lean_mk_io_error_unsupported_operation(v_osCode_boxed_314_, v_details_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted(uint32_t v_osCode_316_, lean_object* v_details_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_box(0);
v___x_319_ = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_details_317_);
lean_ctor_set_uint32(v___x_319_, sizeof(void*)*2, v_osCode_316_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object* v_osCode_320_, lean_object* v_details_321_){
_start:
{
uint32_t v_osCode_boxed_322_; lean_object* v_res_323_; 
v_osCode_boxed_322_ = lean_unbox_uint32(v_osCode_320_);
lean_dec(v_osCode_320_);
v_res_323_ = lean_mk_io_error_resource_exhausted(v_osCode_boxed_322_, v_details_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists(uint32_t v_osCode_324_, lean_object* v_details_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_box(0);
v___x_327_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_details_325_);
lean_ctor_set_uint32(v___x_327_, sizeof(void*)*2, v_osCode_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object* v_osCode_328_, lean_object* v_details_329_){
_start:
{
uint32_t v_osCode_boxed_330_; lean_object* v_res_331_; 
v_osCode_boxed_330_ = lean_unbox_uint32(v_osCode_328_);
lean_dec(v_osCode_328_);
v_res_331_ = lean_mk_io_error_already_exists(v_osCode_boxed_330_, v_details_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type(uint32_t v_osCode_332_, lean_object* v_details_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_details_333_);
lean_ctor_set_uint32(v___x_335_, sizeof(void*)*2, v_osCode_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object* v_osCode_336_, lean_object* v_details_337_){
_start:
{
uint32_t v_osCode_boxed_338_; lean_object* v_res_339_; 
v_osCode_boxed_338_ = lean_unbox_uint32(v_osCode_336_);
lean_dec(v_osCode_336_);
v_res_339_ = lean_mk_io_error_inappropriate_type(v_osCode_boxed_338_, v_details_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing(uint32_t v_osCode_340_, lean_object* v_details_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_box(0);
v___x_343_ = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_details_341_);
lean_ctor_set_uint32(v___x_343_, sizeof(void*)*2, v_osCode_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThing___boxed(lean_object* v_osCode_344_, lean_object* v_details_345_){
_start:
{
uint32_t v_osCode_boxed_346_; lean_object* v_res_347_; 
v_osCode_boxed_346_ = lean_unbox_uint32(v_osCode_344_);
lean_dec(v_osCode_344_);
v_res_347_ = lean_mk_io_error_no_such_thing(v_osCode_boxed_346_, v_details_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_vanished(uint32_t v_osCode_348_, lean_object* v_details_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_ctor(3, 1, 4);
lean_ctor_set(v___x_350_, 0, v_details_349_);
lean_ctor_set_uint32(v___x_350_, sizeof(void*)*1, v_osCode_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object* v_osCode_351_, lean_object* v_details_352_){
_start:
{
uint32_t v_osCode_boxed_353_; lean_object* v_res_354_; 
v_osCode_boxed_353_ = lean_unbox_uint32(v_osCode_351_);
lean_dec(v_osCode_351_);
v_res_354_ = lean_mk_io_error_resource_vanished(v_osCode_boxed_353_, v_details_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_busy(uint32_t v_osCode_355_, lean_object* v_details_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(2, 1, 4);
lean_ctor_set(v___x_357_, 0, v_details_356_);
lean_ctor_set_uint32(v___x_357_, sizeof(void*)*1, v_osCode_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object* v_osCode_358_, lean_object* v_details_359_){
_start:
{
uint32_t v_osCode_boxed_360_; lean_object* v_res_361_; 
v_osCode_boxed_360_ = lean_unbox_uint32(v_osCode_358_);
lean_dec(v_osCode_358_);
v_res_361_ = lean_mk_io_error_resource_busy(v_osCode_boxed_360_, v_details_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument(uint32_t v_osCode_362_, lean_object* v_details_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_details_363_);
lean_ctor_set_uint32(v___x_365_, sizeof(void*)*2, v_osCode_362_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object* v_osCode_366_, lean_object* v_details_367_){
_start:
{
uint32_t v_osCode_boxed_368_; lean_object* v_res_369_; 
v_osCode_boxed_368_ = lean_unbox_uint32(v_osCode_366_);
lean_dec(v_osCode_366_);
v_res_369_ = lean_mk_io_error_invalid_argument(v_osCode_boxed_368_, v_details_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_other_error(uint32_t v_osCode_370_, lean_object* v_details_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(1, 1, 4);
lean_ctor_set(v___x_372_, 0, v_details_371_);
lean_ctor_set_uint32(v___x_372_, sizeof(void*)*1, v_osCode_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkOtherError___boxed(lean_object* v_osCode_373_, lean_object* v_details_374_){
_start:
{
uint32_t v_osCode_boxed_375_; lean_object* v_res_376_; 
v_osCode_boxed_375_ = lean_unbox_uint32(v_osCode_373_);
lean_dec(v_osCode_373_);
v_res_376_ = lean_mk_io_error_other_error(v_osCode_boxed_375_, v_details_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied(uint32_t v_osCode_377_, lean_object* v_details_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_details_378_);
lean_ctor_set_uint32(v___x_380_, sizeof(void*)*2, v_osCode_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object* v_osCode_381_, lean_object* v_details_382_){
_start:
{
uint32_t v_osCode_boxed_383_; lean_object* v_res_384_; 
v_osCode_boxed_383_ = lean_unbox_uint32(v_osCode_381_);
lean_dec(v_osCode_381_);
v_res_384_ = lean_mk_io_error_permission_denied(v_osCode_boxed_383_, v_details_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_hardware_fault(uint32_t v_osCode_385_, lean_object* v_details_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(5, 1, 4);
lean_ctor_set(v___x_387_, 0, v_details_386_);
lean_ctor_set_uint32(v___x_387_, sizeof(void*)*1, v_osCode_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object* v_osCode_388_, lean_object* v_details_389_){
_start:
{
uint32_t v_osCode_boxed_390_; lean_object* v_res_391_; 
v_osCode_boxed_390_ = lean_unbox_uint32(v_osCode_388_);
lean_dec(v_osCode_388_);
v_res_391_ = lean_mk_io_error_hardware_fault(v_osCode_boxed_390_, v_details_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t v_osCode_392_, lean_object* v_details_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(6, 1, 4);
lean_ctor_set(v___x_394_, 0, v_details_393_);
lean_ctor_set_uint32(v___x_394_, sizeof(void*)*1, v_osCode_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object* v_osCode_395_, lean_object* v_details_396_){
_start:
{
uint32_t v_osCode_boxed_397_; lean_object* v_res_398_; 
v_osCode_boxed_397_ = lean_unbox_uint32(v_osCode_395_);
lean_dec(v_osCode_395_);
v_res_398_ = lean_mk_io_error_unsatisfied_constraints(v_osCode_boxed_397_, v_details_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_illegal_operation(uint32_t v_osCode_399_, lean_object* v_details_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_alloc_ctor(7, 1, 4);
lean_ctor_set(v___x_401_, 0, v_details_400_);
lean_ctor_set_uint32(v___x_401_, sizeof(void*)*1, v_osCode_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object* v_osCode_402_, lean_object* v_details_403_){
_start:
{
uint32_t v_osCode_boxed_404_; lean_object* v_res_405_; 
v_osCode_boxed_404_ = lean_unbox_uint32(v_osCode_402_);
lean_dec(v_osCode_402_);
v_res_405_ = lean_mk_io_error_illegal_operation(v_osCode_boxed_404_, v_details_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_protocol_error(uint32_t v_osCode_406_, lean_object* v_details_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(8, 1, 4);
lean_ctor_set(v___x_408_, 0, v_details_407_);
lean_ctor_set_uint32(v___x_408_, sizeof(void*)*1, v_osCode_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkProtocolError___boxed(lean_object* v_osCode_409_, lean_object* v_details_410_){
_start:
{
uint32_t v_osCode_boxed_411_; lean_object* v_res_412_; 
v_osCode_boxed_411_ = lean_unbox_uint32(v_osCode_409_);
lean_dec(v_osCode_409_);
v_res_412_ = lean_mk_io_error_protocol_error(v_osCode_boxed_411_, v_details_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_time_expired(uint32_t v_osCode_413_, lean_object* v_details_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_alloc_ctor(9, 1, 4);
lean_ctor_set(v___x_415_, 0, v_details_414_);
lean_ctor_set_uint32(v___x_415_, sizeof(void*)*1, v_osCode_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object* v_osCode_416_, lean_object* v_details_417_){
_start:
{
uint32_t v_osCode_boxed_418_; lean_object* v_res_419_; 
v_osCode_boxed_418_ = lean_unbox_uint32(v_osCode_416_);
lean_dec(v_osCode_416_);
v_res_419_ = lean_mk_io_error_time_expired(v_osCode_boxed_418_, v_details_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object* v_s_420_){
_start:
{
lean_object* v___x_421_; uint32_t v___x_422_; uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_string_utf8_get(v_s_420_, v___x_421_);
v___x_423_ = 65;
v___x_424_ = lean_uint32_dec_le(v___x_423_, v___x_422_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_string_utf8_set(v_s_420_, v___x_421_, v___x_422_);
return v___x_425_;
}
else
{
uint32_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 90;
v___x_427_ = lean_uint32_dec_le(v___x_422_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
v___x_428_ = lean_string_utf8_set(v_s_420_, v___x_421_, v___x_422_);
return v___x_428_;
}
else
{
uint32_t v___x_429_; uint32_t v___x_430_; lean_object* v___x_431_; 
v___x_429_ = 32;
v___x_430_ = lean_uint32_add(v___x_422_, v___x_429_);
v___x_431_ = lean_string_utf8_set(v_s_420_, v___x_421_, v___x_430_);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString(lean_object* v_gist_435_, lean_object* v_fn_436_, uint32_t v_code_437_, lean_object* v_x_438_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_439_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_435_);
v___x_440_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_441_ = lean_string_append(v___x_439_, v___x_440_);
v___x_442_ = lean_uint32_to_nat(v_code_437_);
v___x_443_ = l_Nat_reprFast(v___x_442_);
v___x_444_ = lean_string_append(v___x_441_, v___x_443_);
lean_dec_ref(v___x_443_);
v___x_445_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
v___x_446_ = lean_string_append(v___x_444_, v___x_445_);
v___x_447_ = lean_string_append(v___x_446_, v_fn_436_);
return v___x_447_;
}
else
{
lean_object* v_val_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_val_448_ = lean_ctor_get(v_x_438_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v_x_438_, 1);
v___x_449_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_435_);
v___x_450_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_451_ = lean_string_append(v___x_449_, v___x_450_);
v___x_452_ = lean_uint32_to_nat(v_code_437_);
v___x_453_ = l_Nat_reprFast(v___x_452_);
v___x_454_ = lean_string_append(v___x_451_, v___x_453_);
lean_dec_ref(v___x_453_);
v___x_455_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
v___x_456_ = lean_string_append(v___x_454_, v___x_455_);
v___x_457_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_448_);
v___x_458_ = lean_string_append(v___x_456_, v___x_457_);
lean_dec_ref(v___x_457_);
v___x_459_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
v___x_460_ = lean_string_append(v___x_458_, v___x_459_);
v___x_461_ = lean_string_append(v___x_460_, v_fn_436_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object* v_gist_462_, lean_object* v_fn_463_, lean_object* v_code_464_, lean_object* v_x_465_){
_start:
{
uint32_t v_code_boxed_466_; lean_object* v_res_467_; 
v_code_boxed_466_ = lean_unbox_uint32(v_code_464_);
lean_dec(v_code_464_);
v_res_467_ = l_IO_Error_fopenErrorToString(v_gist_462_, v_fn_463_, v_code_boxed_466_, v_x_465_);
lean_dec_ref(v_fn_463_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString(lean_object* v_gist_469_, uint32_t v_code_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_472_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_469_);
v___x_473_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
v___x_475_ = lean_uint32_to_nat(v_code_470_);
v___x_476_ = l_Nat_reprFast(v___x_475_);
v___x_477_ = lean_string_append(v___x_474_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_val_480_ = lean_ctor_get(v_x_471_, 0);
lean_inc(v_val_480_);
lean_dec_ref_known(v_x_471_, 1);
v___x_481_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_469_);
v___x_482_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v___x_484_ = lean_uint32_to_nat(v_code_470_);
v___x_485_ = l_Nat_reprFast(v___x_484_);
v___x_486_ = lean_string_append(v___x_483_, v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
v___x_489_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_480_);
v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_491_ = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString___boxed(lean_object* v_gist_493_, lean_object* v_code_494_, lean_object* v_x_495_){
_start:
{
uint32_t v_code_boxed_496_; lean_object* v_res_497_; 
v_code_boxed_496_ = lean_unbox_uint32(v_code_494_);
lean_dec(v_code_494_);
v_res_497_ = l_IO_Error_otherErrorToString(v_gist_493_, v_code_boxed_496_, v_x_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* lean_io_error_to_string(lean_object* v_x_514_){
_start:
{
uint32_t v_code_516_; lean_object* v_details_517_; 
switch(lean_obj_tag(v_x_514_))
{
case 0:
{
lean_object* v_filename_520_; 
v_filename_520_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_filename_520_);
if (lean_obj_tag(v_filename_520_) == 0)
{
uint32_t v_osCode_521_; lean_object* v_details_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_osCode_521_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_522_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_522_);
lean_dec_ref_known(v_x_514_, 2);
v___x_523_ = ((lean_object*)(l_IO_Error_toString___closed__0));
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v_details_522_);
v___x_525_ = l_IO_Error_otherErrorToString(v___x_523_, v_osCode_521_, v___x_524_);
return v___x_525_;
}
else
{
uint32_t v_osCode_526_; lean_object* v_details_527_; lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_537_; 
v_osCode_526_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_527_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_527_);
lean_dec_ref_known(v_x_514_, 2);
v_val_528_ = lean_ctor_get(v_filename_520_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_filename_520_);
if (v_isSharedCheck_537_ == 0)
{
v___x_530_ = v_filename_520_;
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v_filename_520_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = ((lean_object*)(l_IO_Error_toString___closed__0));
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v_details_527_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_details_527_);
v___x_534_ = v_reuseFailAlloc_536_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; 
v___x_535_ = l_IO_Error_fopenErrorToString(v___x_532_, v_val_528_, v_osCode_526_, v___x_534_);
lean_dec(v_val_528_);
return v___x_535_;
}
}
}
}
case 1:
{
uint32_t v_osCode_538_; lean_object* v_details_539_; 
v_osCode_538_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
v_details_539_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_details_539_);
lean_dec_ref_known(v_x_514_, 1);
v_code_516_ = v_osCode_538_;
v_details_517_ = v_details_539_;
goto v___jp_515_;
}
case 2:
{
uint32_t v_osCode_540_; lean_object* v_details_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_osCode_540_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
v_details_541_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_details_541_);
lean_dec_ref_known(v_x_514_, 1);
v___x_542_ = ((lean_object*)(l_IO_Error_toString___closed__1));
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_details_541_);
v___x_544_ = l_IO_Error_otherErrorToString(v___x_542_, v_osCode_540_, v___x_543_);
return v___x_544_;
}
case 3:
{
uint32_t v_osCode_545_; lean_object* v_details_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_osCode_545_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
v_details_546_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_details_546_);
lean_dec_ref_known(v_x_514_, 1);
v___x_547_ = ((lean_object*)(l_IO_Error_toString___closed__2));
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_details_546_);
v___x_549_ = l_IO_Error_otherErrorToString(v___x_547_, v_osCode_545_, v___x_548_);
return v___x_549_;
}
case 4:
{
uint32_t v_osCode_550_; lean_object* v_details_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_osCode_550_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
v_details_551_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_details_551_);
lean_dec_ref_known(v_x_514_, 1);
v___x_552_ = ((lean_object*)(l_IO_Error_toString___closed__3));
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_details_551_);
v___x_554_ = l_IO_Error_otherErrorToString(v___x_552_, v_osCode_550_, v___x_553_);
return v___x_554_;
}
case 5:
{
uint32_t v_osCode_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_osCode_555_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
lean_dec_ref_known(v_x_514_, 1);
v___x_556_ = ((lean_object*)(l_IO_Error_toString___closed__4));
v___x_557_ = lean_box(0);
v___x_558_ = l_IO_Error_otherErrorToString(v___x_556_, v_osCode_555_, v___x_557_);
return v___x_558_;
}
case 6:
{
uint32_t v_osCode_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_osCode_559_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
lean_dec_ref_known(v_x_514_, 1);
v___x_560_ = ((lean_object*)(l_IO_Error_toString___closed__5));
v___x_561_ = lean_box(0);
v___x_562_ = l_IO_Error_otherErrorToString(v___x_560_, v_osCode_559_, v___x_561_);
return v___x_562_;
}
case 7:
{
uint32_t v_osCode_563_; lean_object* v_details_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_osCode_563_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
v_details_564_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_details_564_);
lean_dec_ref_known(v_x_514_, 1);
v___x_565_ = ((lean_object*)(l_IO_Error_toString___closed__6));
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_details_564_);
v___x_567_ = l_IO_Error_otherErrorToString(v___x_565_, v_osCode_563_, v___x_566_);
return v___x_567_;
}
case 8:
{
uint32_t v_osCode_568_; lean_object* v_details_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_osCode_568_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
v_details_569_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_details_569_);
lean_dec_ref_known(v_x_514_, 1);
v___x_570_ = ((lean_object*)(l_IO_Error_toString___closed__7));
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v_details_569_);
v___x_572_ = l_IO_Error_otherErrorToString(v___x_570_, v_osCode_568_, v___x_571_);
return v___x_572_;
}
case 9:
{
uint32_t v_osCode_573_; lean_object* v_details_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_osCode_573_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*1);
v_details_574_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_details_574_);
lean_dec_ref_known(v_x_514_, 1);
v___x_575_ = ((lean_object*)(l_IO_Error_toString___closed__8));
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v_details_574_);
v___x_577_ = l_IO_Error_otherErrorToString(v___x_575_, v_osCode_573_, v___x_576_);
return v___x_577_;
}
case 10:
{
lean_object* v_filename_578_; uint32_t v_osCode_579_; lean_object* v_details_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_filename_578_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_filename_578_);
v_osCode_579_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_580_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_580_);
lean_dec_ref_known(v_x_514_, 2);
v___x_581_ = ((lean_object*)(l_IO_Error_toString___closed__9));
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_details_580_);
v___x_583_ = l_IO_Error_fopenErrorToString(v___x_581_, v_filename_578_, v_osCode_579_, v___x_582_);
lean_dec_ref(v_filename_578_);
return v___x_583_;
}
case 11:
{
lean_object* v_filename_584_; uint32_t v_osCode_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_filename_584_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_filename_584_);
v_osCode_585_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
lean_dec_ref_known(v_x_514_, 2);
v___x_586_ = ((lean_object*)(l_IO_Error_toString___closed__10));
v___x_587_ = lean_box(0);
v___x_588_ = l_IO_Error_fopenErrorToString(v___x_586_, v_filename_584_, v_osCode_585_, v___x_587_);
lean_dec_ref(v_filename_584_);
return v___x_588_;
}
case 12:
{
lean_object* v_filename_589_; 
v_filename_589_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_filename_589_);
if (lean_obj_tag(v_filename_589_) == 0)
{
uint32_t v_osCode_590_; lean_object* v_details_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_osCode_590_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_591_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_591_);
lean_dec_ref_known(v_x_514_, 2);
v___x_592_ = ((lean_object*)(l_IO_Error_toString___closed__11));
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v_details_591_);
v___x_594_ = l_IO_Error_otherErrorToString(v___x_592_, v_osCode_590_, v___x_593_);
return v___x_594_;
}
else
{
uint32_t v_osCode_595_; lean_object* v_details_596_; lean_object* v_val_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_606_; 
v_osCode_595_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_596_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_596_);
lean_dec_ref_known(v_x_514_, 2);
v_val_597_ = lean_ctor_get(v_filename_589_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_filename_589_);
if (v_isSharedCheck_606_ == 0)
{
v___x_599_ = v_filename_589_;
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_val_597_);
lean_dec(v_filename_589_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = ((lean_object*)(l_IO_Error_toString___closed__11));
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_details_596_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_details_596_);
v___x_603_ = v_reuseFailAlloc_605_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = l_IO_Error_fopenErrorToString(v___x_601_, v_val_597_, v_osCode_595_, v___x_603_);
lean_dec(v_val_597_);
return v___x_604_;
}
}
}
}
case 13:
{
lean_object* v_filename_607_; 
v_filename_607_ = lean_ctor_get(v_x_514_, 0);
if (lean_obj_tag(v_filename_607_) == 0)
{
uint32_t v_osCode_608_; lean_object* v_details_609_; 
v_osCode_608_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_609_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_609_);
lean_dec_ref_known(v_x_514_, 2);
v_code_516_ = v_osCode_608_;
v_details_517_ = v_details_609_;
goto v___jp_515_;
}
else
{
uint32_t v_osCode_610_; lean_object* v_details_611_; lean_object* v_val_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_inc_ref(v_filename_607_);
v_osCode_610_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_611_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_611_);
lean_dec_ref_known(v_x_514_, 2);
v_val_612_ = lean_ctor_get(v_filename_607_, 0);
lean_inc(v_val_612_);
lean_dec_ref_known(v_filename_607_, 1);
v___x_613_ = lean_box(0);
v___x_614_ = l_IO_Error_fopenErrorToString(v_details_611_, v_val_612_, v_osCode_610_, v___x_613_);
lean_dec(v_val_612_);
return v___x_614_;
}
}
case 14:
{
lean_object* v_filename_615_; 
v_filename_615_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_filename_615_);
if (lean_obj_tag(v_filename_615_) == 0)
{
uint32_t v_osCode_616_; lean_object* v_details_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_osCode_616_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_617_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_617_);
lean_dec_ref_known(v_x_514_, 2);
v___x_618_ = ((lean_object*)(l_IO_Error_toString___closed__12));
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v_details_617_);
v___x_620_ = l_IO_Error_otherErrorToString(v___x_618_, v_osCode_616_, v___x_619_);
return v___x_620_;
}
else
{
uint32_t v_osCode_621_; lean_object* v_details_622_; lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_632_; 
v_osCode_621_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_622_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_622_);
lean_dec_ref_known(v_x_514_, 2);
v_val_623_ = lean_ctor_get(v_filename_615_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_filename_615_);
if (v_isSharedCheck_632_ == 0)
{
v___x_625_ = v_filename_615_;
v_isShared_626_ = v_isSharedCheck_632_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v_filename_615_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_632_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = ((lean_object*)(l_IO_Error_toString___closed__12));
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_details_622_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_details_622_);
v___x_629_ = v_reuseFailAlloc_631_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; 
v___x_630_ = l_IO_Error_fopenErrorToString(v___x_627_, v_val_623_, v_osCode_621_, v___x_629_);
lean_dec(v_val_623_);
return v___x_630_;
}
}
}
}
case 15:
{
lean_object* v_filename_633_; 
v_filename_633_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_filename_633_);
if (lean_obj_tag(v_filename_633_) == 0)
{
uint32_t v_osCode_634_; lean_object* v_details_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_osCode_634_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_635_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_635_);
lean_dec_ref_known(v_x_514_, 2);
v___x_636_ = ((lean_object*)(l_IO_Error_toString___closed__13));
v___x_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_637_, 0, v_details_635_);
v___x_638_ = l_IO_Error_otherErrorToString(v___x_636_, v_osCode_634_, v___x_637_);
return v___x_638_;
}
else
{
uint32_t v_osCode_639_; lean_object* v_details_640_; lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_650_; 
v_osCode_639_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_640_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_640_);
lean_dec_ref_known(v_x_514_, 2);
v_val_641_ = lean_ctor_get(v_filename_633_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_filename_633_);
if (v_isSharedCheck_650_ == 0)
{
v___x_643_ = v_filename_633_;
v_isShared_644_ = v_isSharedCheck_650_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v_filename_633_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_650_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = ((lean_object*)(l_IO_Error_toString___closed__13));
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_details_640_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_details_640_);
v___x_647_ = v_reuseFailAlloc_649_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; 
v___x_648_ = l_IO_Error_fopenErrorToString(v___x_645_, v_val_641_, v_osCode_639_, v___x_647_);
lean_dec(v_val_641_);
return v___x_648_;
}
}
}
}
case 16:
{
lean_object* v_filename_651_; 
v_filename_651_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_filename_651_);
if (lean_obj_tag(v_filename_651_) == 0)
{
uint32_t v_osCode_652_; lean_object* v_details_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_osCode_652_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_653_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_653_);
lean_dec_ref_known(v_x_514_, 2);
v___x_654_ = ((lean_object*)(l_IO_Error_toString___closed__14));
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_details_653_);
v___x_656_ = l_IO_Error_otherErrorToString(v___x_654_, v_osCode_652_, v___x_655_);
return v___x_656_;
}
else
{
uint32_t v_osCode_657_; lean_object* v_details_658_; lean_object* v_val_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_668_; 
v_osCode_657_ = lean_ctor_get_uint32(v_x_514_, sizeof(void*)*2);
v_details_658_ = lean_ctor_get(v_x_514_, 1);
lean_inc_ref(v_details_658_);
lean_dec_ref_known(v_x_514_, 2);
v_val_659_ = lean_ctor_get(v_filename_651_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_filename_651_);
if (v_isSharedCheck_668_ == 0)
{
v___x_661_ = v_filename_651_;
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_val_659_);
lean_dec(v_filename_651_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = ((lean_object*)(l_IO_Error_toString___closed__14));
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_details_658_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_details_658_);
v___x_665_ = v_reuseFailAlloc_667_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; 
v___x_666_ = l_IO_Error_fopenErrorToString(v___x_663_, v_val_659_, v_osCode_657_, v___x_665_);
lean_dec(v_val_659_);
return v___x_666_;
}
}
}
}
case 17:
{
lean_object* v___x_669_; 
v___x_669_ = ((lean_object*)(l_IO_Error_toString___closed__15));
return v___x_669_;
}
default: 
{
lean_object* v_msg_670_; 
v_msg_670_ = lean_ctor_get(v_x_514_, 0);
lean_inc_ref(v_msg_670_);
lean_dec_ref_known(v_x_514_, 1);
return v_msg_670_;
}
}
v___jp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_box(0);
v___x_519_ = l_IO_Error_otherErrorToString(v_details_517_, v_code_516_, v___x_518_);
return v___x_519_;
}
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_IOError(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_IOError(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_IOError(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IOError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_IOError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_IOError(builtin);
}
#ifdef __cplusplus
}
#endif
