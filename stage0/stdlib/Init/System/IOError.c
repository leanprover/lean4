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
lean_object* lean_mk_io_error_already_exists_file(lean_object* v_a_225_, uint32_t v_a_226_, lean_object* v_a_227_){
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
LEAN_EXPORT void lean_mk_io_error_already_exists_file_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_225_ = stack[0].m_obj;
uint32_t v_a_226_ = stack[1].m_num;
lean_object* v_a_227_ = stack[2].m_obj;
lean_object* v_res_230_;
v_res_230_ = lean_mk_io_error_already_exists_file(v_a_225_, v_a_226_, v_a_227_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExistsFile___boxed(lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
uint32_t v_a_20__boxed_234_; lean_object* v_res_235_; 
v_a_20__boxed_234_ = lean_unbox_uint32(v_a_232_);
lean_dec(v_a_232_);
v_res_235_ = lean_mk_io_error_already_exists_file(v_a_231_, v_a_20__boxed_234_, v_a_233_);
return v_res_235_;
}
}
lean_object* l_IO_Error_mkEofError___redArg(){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_box(17);
return v___x_237_;
}
}
LEAN_EXPORT void l_IO_Error_mkEofError___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_238_;
v_res_238_ = l_IO_Error_mkEofError___redArg();
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkEofError___redArg___boxed(lean_object* v___dummy_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_IO_Error_mkEofError___redArg();
return v_res_240_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_eof(lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_box(17);
return v___x_242_;
}
}
lean_object* lean_mk_io_error_inappropriate_type_file(lean_object* v_a_243_, uint32_t v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_a_243_);
v___x_247_ = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_245_);
lean_ctor_set_uint32(v___x_247_, sizeof(void*)*2, v_a_244_);
return v___x_247_;
}
}
LEAN_EXPORT void lean_mk_io_error_inappropriate_type_file_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_243_ = stack[0].m_obj;
uint32_t v_a_244_ = stack[1].m_num;
lean_object* v_a_245_ = stack[2].m_obj;
lean_object* v_res_248_;
v_res_248_ = lean_mk_io_error_inappropriate_type_file(v_a_243_, v_a_244_, v_a_245_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
uint32_t v_a_20__boxed_252_; lean_object* v_res_253_; 
v_a_20__boxed_252_ = lean_unbox_uint32(v_a_250_);
lean_dec(v_a_250_);
v_res_253_ = lean_mk_io_error_inappropriate_type_file(v_a_249_, v_a_20__boxed_252_, v_a_251_);
return v_res_253_;
}
}
lean_object* lean_mk_io_error_interrupted(lean_object* v_filename_254_, uint32_t v_osCode_255_, lean_object* v_details_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(10, 2, 4);
lean_ctor_set(v___x_257_, 0, v_filename_254_);
lean_ctor_set(v___x_257_, 1, v_details_256_);
lean_ctor_set_uint32(v___x_257_, sizeof(void*)*2, v_osCode_255_);
return v___x_257_;
}
}
LEAN_EXPORT void lean_mk_io_error_interrupted_0interp(lean_interpreter_value* stack)
{
lean_object* v_filename_254_ = stack[0].m_obj;
uint32_t v_osCode_255_ = stack[1].m_num;
lean_object* v_details_256_ = stack[2].m_obj;
lean_object* v_res_258_;
v_res_258_ = lean_mk_io_error_interrupted(v_filename_254_, v_osCode_255_, v_details_256_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkInterrupted___boxed(lean_object* v_filename_259_, lean_object* v_osCode_260_, lean_object* v_details_261_){
_start:
{
uint32_t v_osCode_boxed_262_; lean_object* v_res_263_; 
v_osCode_boxed_262_ = lean_unbox_uint32(v_osCode_260_);
lean_dec(v_osCode_260_);
v_res_263_ = lean_mk_io_error_interrupted(v_filename_259_, v_osCode_boxed_262_, v_details_261_);
return v_res_263_;
}
}
lean_object* lean_mk_io_error_invalid_argument_file(lean_object* v_a_264_, uint32_t v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_a_264_);
v___x_268_ = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_266_);
lean_ctor_set_uint32(v___x_268_, sizeof(void*)*2, v_a_265_);
return v___x_268_;
}
}
LEAN_EXPORT void lean_mk_io_error_invalid_argument_file_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_264_ = stack[0].m_obj;
uint32_t v_a_265_ = stack[1].m_num;
lean_object* v_a_266_ = stack[2].m_obj;
lean_object* v_res_269_;
v_res_269_ = lean_mk_io_error_invalid_argument_file(v_a_264_, v_a_265_, v_a_266_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
uint32_t v_a_20__boxed_273_; lean_object* v_res_274_; 
v_a_20__boxed_273_ = lean_unbox_uint32(v_a_271_);
lean_dec(v_a_271_);
v_res_274_ = lean_mk_io_error_invalid_argument_file(v_a_270_, v_a_20__boxed_273_, v_a_272_);
return v_res_274_;
}
}
lean_object* lean_mk_io_error_no_file_or_directory(lean_object* v_filename_275_, uint32_t v_osCode_276_, lean_object* v_details_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_278_, 0, v_filename_275_);
lean_ctor_set(v___x_278_, 1, v_details_277_);
lean_ctor_set_uint32(v___x_278_, sizeof(void*)*2, v_osCode_276_);
return v___x_278_;
}
}
LEAN_EXPORT void lean_mk_io_error_no_file_or_directory_0interp(lean_interpreter_value* stack)
{
lean_object* v_filename_275_ = stack[0].m_obj;
uint32_t v_osCode_276_ = stack[1].m_num;
lean_object* v_details_277_ = stack[2].m_obj;
lean_object* v_res_279_;
v_res_279_ = lean_mk_io_error_no_file_or_directory(v_filename_275_, v_osCode_276_, v_details_277_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object* v_filename_280_, lean_object* v_osCode_281_, lean_object* v_details_282_){
_start:
{
uint32_t v_osCode_boxed_283_; lean_object* v_res_284_; 
v_osCode_boxed_283_ = lean_unbox_uint32(v_osCode_281_);
lean_dec(v_osCode_281_);
v_res_284_ = lean_mk_io_error_no_file_or_directory(v_filename_280_, v_osCode_boxed_283_, v_details_282_);
return v_res_284_;
}
}
lean_object* lean_mk_io_error_no_such_thing_file(lean_object* v_a_285_, uint32_t v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v_a_285_);
v___x_289_ = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_a_287_);
lean_ctor_set_uint32(v___x_289_, sizeof(void*)*2, v_a_286_);
return v___x_289_;
}
}
LEAN_EXPORT void lean_mk_io_error_no_such_thing_file_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_285_ = stack[0].m_obj;
uint32_t v_a_286_ = stack[1].m_num;
lean_object* v_a_287_ = stack[2].m_obj;
lean_object* v_res_290_;
v_res_290_ = lean_mk_io_error_no_such_thing_file(v_a_285_, v_a_286_, v_a_287_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
uint32_t v_a_20__boxed_294_; lean_object* v_res_295_; 
v_a_20__boxed_294_ = lean_unbox_uint32(v_a_292_);
lean_dec(v_a_292_);
v_res_295_ = lean_mk_io_error_no_such_thing_file(v_a_291_, v_a_20__boxed_294_, v_a_293_);
return v_res_295_;
}
}
lean_object* lean_mk_io_error_permission_denied_file(lean_object* v_a_296_, uint32_t v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v_a_296_);
v___x_300_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v_a_298_);
lean_ctor_set_uint32(v___x_300_, sizeof(void*)*2, v_a_297_);
return v___x_300_;
}
}
LEAN_EXPORT void lean_mk_io_error_permission_denied_file_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_296_ = stack[0].m_obj;
uint32_t v_a_297_ = stack[1].m_num;
lean_object* v_a_298_ = stack[2].m_obj;
lean_object* v_res_301_;
v_res_301_ = lean_mk_io_error_permission_denied_file(v_a_296_, v_a_297_, v_a_298_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
uint32_t v_a_20__boxed_305_; lean_object* v_res_306_; 
v_a_20__boxed_305_ = lean_unbox_uint32(v_a_303_);
lean_dec(v_a_303_);
v_res_306_ = lean_mk_io_error_permission_denied_file(v_a_302_, v_a_20__boxed_305_, v_a_304_);
return v_res_306_;
}
}
lean_object* lean_mk_io_error_resource_exhausted_file(lean_object* v_a_307_, uint32_t v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_a_307_);
v___x_311_ = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_309_);
lean_ctor_set_uint32(v___x_311_, sizeof(void*)*2, v_a_308_);
return v___x_311_;
}
}
LEAN_EXPORT void lean_mk_io_error_resource_exhausted_file_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_307_ = stack[0].m_obj;
uint32_t v_a_308_ = stack[1].m_num;
lean_object* v_a_309_ = stack[2].m_obj;
lean_object* v_res_312_;
v_res_312_ = lean_mk_io_error_resource_exhausted_file(v_a_307_, v_a_308_, v_a_309_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
uint32_t v_a_20__boxed_316_; lean_object* v_res_317_; 
v_a_20__boxed_316_ = lean_unbox_uint32(v_a_314_);
lean_dec(v_a_314_);
v_res_317_ = lean_mk_io_error_resource_exhausted_file(v_a_313_, v_a_20__boxed_316_, v_a_315_);
return v_res_317_;
}
}
lean_object* lean_mk_io_error_unsupported_operation(uint32_t v_osCode_318_, lean_object* v_details_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(4, 1, 4);
lean_ctor_set(v___x_320_, 0, v_details_319_);
lean_ctor_set_uint32(v___x_320_, sizeof(void*)*1, v_osCode_318_);
return v___x_320_;
}
}
LEAN_EXPORT void lean_mk_io_error_unsupported_operation_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_318_ = stack[0].m_num;
lean_object* v_details_319_ = stack[1].m_obj;
lean_object* v_res_321_;
v_res_321_ = lean_mk_io_error_unsupported_operation(v_osCode_318_, v_details_319_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object* v_osCode_322_, lean_object* v_details_323_){
_start:
{
uint32_t v_osCode_boxed_324_; lean_object* v_res_325_; 
v_osCode_boxed_324_ = lean_unbox_uint32(v_osCode_322_);
lean_dec(v_osCode_322_);
v_res_325_ = lean_mk_io_error_unsupported_operation(v_osCode_boxed_324_, v_details_323_);
return v_res_325_;
}
}
lean_object* lean_mk_io_error_resource_exhausted(uint32_t v_osCode_326_, lean_object* v_details_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_box(0);
v___x_329_ = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_details_327_);
lean_ctor_set_uint32(v___x_329_, sizeof(void*)*2, v_osCode_326_);
return v___x_329_;
}
}
LEAN_EXPORT void lean_mk_io_error_resource_exhausted_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_326_ = stack[0].m_num;
lean_object* v_details_327_ = stack[1].m_obj;
lean_object* v_res_330_;
v_res_330_ = lean_mk_io_error_resource_exhausted(v_osCode_326_, v_details_327_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object* v_osCode_331_, lean_object* v_details_332_){
_start:
{
uint32_t v_osCode_boxed_333_; lean_object* v_res_334_; 
v_osCode_boxed_333_ = lean_unbox_uint32(v_osCode_331_);
lean_dec(v_osCode_331_);
v_res_334_ = lean_mk_io_error_resource_exhausted(v_osCode_boxed_333_, v_details_332_);
return v_res_334_;
}
}
lean_object* lean_mk_io_error_already_exists(uint32_t v_osCode_335_, lean_object* v_details_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_details_336_);
lean_ctor_set_uint32(v___x_338_, sizeof(void*)*2, v_osCode_335_);
return v___x_338_;
}
}
LEAN_EXPORT void lean_mk_io_error_already_exists_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_335_ = stack[0].m_num;
lean_object* v_details_336_ = stack[1].m_obj;
lean_object* v_res_339_;
v_res_339_ = lean_mk_io_error_already_exists(v_osCode_335_, v_details_336_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object* v_osCode_340_, lean_object* v_details_341_){
_start:
{
uint32_t v_osCode_boxed_342_; lean_object* v_res_343_; 
v_osCode_boxed_342_ = lean_unbox_uint32(v_osCode_340_);
lean_dec(v_osCode_340_);
v_res_343_ = lean_mk_io_error_already_exists(v_osCode_boxed_342_, v_details_341_);
return v_res_343_;
}
}
lean_object* lean_mk_io_error_inappropriate_type(uint32_t v_osCode_344_, lean_object* v_details_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_box(0);
v___x_347_ = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v_details_345_);
lean_ctor_set_uint32(v___x_347_, sizeof(void*)*2, v_osCode_344_);
return v___x_347_;
}
}
LEAN_EXPORT void lean_mk_io_error_inappropriate_type_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_344_ = stack[0].m_num;
lean_object* v_details_345_ = stack[1].m_obj;
lean_object* v_res_348_;
v_res_348_ = lean_mk_io_error_inappropriate_type(v_osCode_344_, v_details_345_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object* v_osCode_349_, lean_object* v_details_350_){
_start:
{
uint32_t v_osCode_boxed_351_; lean_object* v_res_352_; 
v_osCode_boxed_351_ = lean_unbox_uint32(v_osCode_349_);
lean_dec(v_osCode_349_);
v_res_352_ = lean_mk_io_error_inappropriate_type(v_osCode_boxed_351_, v_details_350_);
return v_res_352_;
}
}
lean_object* lean_mk_io_error_no_such_thing(uint32_t v_osCode_353_, lean_object* v_details_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_details_354_);
lean_ctor_set_uint32(v___x_356_, sizeof(void*)*2, v_osCode_353_);
return v___x_356_;
}
}
LEAN_EXPORT void lean_mk_io_error_no_such_thing_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_353_ = stack[0].m_num;
lean_object* v_details_354_ = stack[1].m_obj;
lean_object* v_res_357_;
v_res_357_ = lean_mk_io_error_no_such_thing(v_osCode_353_, v_details_354_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThing___boxed(lean_object* v_osCode_358_, lean_object* v_details_359_){
_start:
{
uint32_t v_osCode_boxed_360_; lean_object* v_res_361_; 
v_osCode_boxed_360_ = lean_unbox_uint32(v_osCode_358_);
lean_dec(v_osCode_358_);
v_res_361_ = lean_mk_io_error_no_such_thing(v_osCode_boxed_360_, v_details_359_);
return v_res_361_;
}
}
lean_object* lean_mk_io_error_resource_vanished(uint32_t v_osCode_362_, lean_object* v_details_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(3, 1, 4);
lean_ctor_set(v___x_364_, 0, v_details_363_);
lean_ctor_set_uint32(v___x_364_, sizeof(void*)*1, v_osCode_362_);
return v___x_364_;
}
}
LEAN_EXPORT void lean_mk_io_error_resource_vanished_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_362_ = stack[0].m_num;
lean_object* v_details_363_ = stack[1].m_obj;
lean_object* v_res_365_;
v_res_365_ = lean_mk_io_error_resource_vanished(v_osCode_362_, v_details_363_);
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object* v_osCode_366_, lean_object* v_details_367_){
_start:
{
uint32_t v_osCode_boxed_368_; lean_object* v_res_369_; 
v_osCode_boxed_368_ = lean_unbox_uint32(v_osCode_366_);
lean_dec(v_osCode_366_);
v_res_369_ = lean_mk_io_error_resource_vanished(v_osCode_boxed_368_, v_details_367_);
return v_res_369_;
}
}
lean_object* lean_mk_io_error_resource_busy(uint32_t v_osCode_370_, lean_object* v_details_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(2, 1, 4);
lean_ctor_set(v___x_372_, 0, v_details_371_);
lean_ctor_set_uint32(v___x_372_, sizeof(void*)*1, v_osCode_370_);
return v___x_372_;
}
}
LEAN_EXPORT void lean_mk_io_error_resource_busy_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_370_ = stack[0].m_num;
lean_object* v_details_371_ = stack[1].m_obj;
lean_object* v_res_373_;
v_res_373_ = lean_mk_io_error_resource_busy(v_osCode_370_, v_details_371_);
stack->m_obj
 = v_res_373_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object* v_osCode_374_, lean_object* v_details_375_){
_start:
{
uint32_t v_osCode_boxed_376_; lean_object* v_res_377_; 
v_osCode_boxed_376_ = lean_unbox_uint32(v_osCode_374_);
lean_dec(v_osCode_374_);
v_res_377_ = lean_mk_io_error_resource_busy(v_osCode_boxed_376_, v_details_375_);
return v_res_377_;
}
}
lean_object* lean_mk_io_error_invalid_argument(uint32_t v_osCode_378_, lean_object* v_details_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_details_379_);
lean_ctor_set_uint32(v___x_381_, sizeof(void*)*2, v_osCode_378_);
return v___x_381_;
}
}
LEAN_EXPORT void lean_mk_io_error_invalid_argument_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_378_ = stack[0].m_num;
lean_object* v_details_379_ = stack[1].m_obj;
lean_object* v_res_382_;
v_res_382_ = lean_mk_io_error_invalid_argument(v_osCode_378_, v_details_379_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object* v_osCode_383_, lean_object* v_details_384_){
_start:
{
uint32_t v_osCode_boxed_385_; lean_object* v_res_386_; 
v_osCode_boxed_385_ = lean_unbox_uint32(v_osCode_383_);
lean_dec(v_osCode_383_);
v_res_386_ = lean_mk_io_error_invalid_argument(v_osCode_boxed_385_, v_details_384_);
return v_res_386_;
}
}
lean_object* lean_mk_io_error_other_error(uint32_t v_osCode_387_, lean_object* v_details_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(1, 1, 4);
lean_ctor_set(v___x_389_, 0, v_details_388_);
lean_ctor_set_uint32(v___x_389_, sizeof(void*)*1, v_osCode_387_);
return v___x_389_;
}
}
LEAN_EXPORT void lean_mk_io_error_other_error_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_387_ = stack[0].m_num;
lean_object* v_details_388_ = stack[1].m_obj;
lean_object* v_res_390_;
v_res_390_ = lean_mk_io_error_other_error(v_osCode_387_, v_details_388_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkOtherError___boxed(lean_object* v_osCode_391_, lean_object* v_details_392_){
_start:
{
uint32_t v_osCode_boxed_393_; lean_object* v_res_394_; 
v_osCode_boxed_393_ = lean_unbox_uint32(v_osCode_391_);
lean_dec(v_osCode_391_);
v_res_394_ = lean_mk_io_error_other_error(v_osCode_boxed_393_, v_details_392_);
return v_res_394_;
}
}
lean_object* lean_mk_io_error_permission_denied(uint32_t v_osCode_395_, lean_object* v_details_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_details_396_);
lean_ctor_set_uint32(v___x_398_, sizeof(void*)*2, v_osCode_395_);
return v___x_398_;
}
}
LEAN_EXPORT void lean_mk_io_error_permission_denied_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_395_ = stack[0].m_num;
lean_object* v_details_396_ = stack[1].m_obj;
lean_object* v_res_399_;
v_res_399_ = lean_mk_io_error_permission_denied(v_osCode_395_, v_details_396_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object* v_osCode_400_, lean_object* v_details_401_){
_start:
{
uint32_t v_osCode_boxed_402_; lean_object* v_res_403_; 
v_osCode_boxed_402_ = lean_unbox_uint32(v_osCode_400_);
lean_dec(v_osCode_400_);
v_res_403_ = lean_mk_io_error_permission_denied(v_osCode_boxed_402_, v_details_401_);
return v_res_403_;
}
}
lean_object* lean_mk_io_error_hardware_fault(uint32_t v_osCode_404_, lean_object* v_details_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_ctor(5, 1, 4);
lean_ctor_set(v___x_406_, 0, v_details_405_);
lean_ctor_set_uint32(v___x_406_, sizeof(void*)*1, v_osCode_404_);
return v___x_406_;
}
}
LEAN_EXPORT void lean_mk_io_error_hardware_fault_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_404_ = stack[0].m_num;
lean_object* v_details_405_ = stack[1].m_obj;
lean_object* v_res_407_;
v_res_407_ = lean_mk_io_error_hardware_fault(v_osCode_404_, v_details_405_);
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object* v_osCode_408_, lean_object* v_details_409_){
_start:
{
uint32_t v_osCode_boxed_410_; lean_object* v_res_411_; 
v_osCode_boxed_410_ = lean_unbox_uint32(v_osCode_408_);
lean_dec(v_osCode_408_);
v_res_411_ = lean_mk_io_error_hardware_fault(v_osCode_boxed_410_, v_details_409_);
return v_res_411_;
}
}
lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t v_osCode_412_, lean_object* v_details_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_alloc_ctor(6, 1, 4);
lean_ctor_set(v___x_414_, 0, v_details_413_);
lean_ctor_set_uint32(v___x_414_, sizeof(void*)*1, v_osCode_412_);
return v___x_414_;
}
}
LEAN_EXPORT void lean_mk_io_error_unsatisfied_constraints_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_412_ = stack[0].m_num;
lean_object* v_details_413_ = stack[1].m_obj;
lean_object* v_res_415_;
v_res_415_ = lean_mk_io_error_unsatisfied_constraints(v_osCode_412_, v_details_413_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object* v_osCode_416_, lean_object* v_details_417_){
_start:
{
uint32_t v_osCode_boxed_418_; lean_object* v_res_419_; 
v_osCode_boxed_418_ = lean_unbox_uint32(v_osCode_416_);
lean_dec(v_osCode_416_);
v_res_419_ = lean_mk_io_error_unsatisfied_constraints(v_osCode_boxed_418_, v_details_417_);
return v_res_419_;
}
}
lean_object* lean_mk_io_error_illegal_operation(uint32_t v_osCode_420_, lean_object* v_details_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(7, 1, 4);
lean_ctor_set(v___x_422_, 0, v_details_421_);
lean_ctor_set_uint32(v___x_422_, sizeof(void*)*1, v_osCode_420_);
return v___x_422_;
}
}
LEAN_EXPORT void lean_mk_io_error_illegal_operation_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_420_ = stack[0].m_num;
lean_object* v_details_421_ = stack[1].m_obj;
lean_object* v_res_423_;
v_res_423_ = lean_mk_io_error_illegal_operation(v_osCode_420_, v_details_421_);
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object* v_osCode_424_, lean_object* v_details_425_){
_start:
{
uint32_t v_osCode_boxed_426_; lean_object* v_res_427_; 
v_osCode_boxed_426_ = lean_unbox_uint32(v_osCode_424_);
lean_dec(v_osCode_424_);
v_res_427_ = lean_mk_io_error_illegal_operation(v_osCode_boxed_426_, v_details_425_);
return v_res_427_;
}
}
lean_object* lean_mk_io_error_protocol_error(uint32_t v_osCode_428_, lean_object* v_details_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(8, 1, 4);
lean_ctor_set(v___x_430_, 0, v_details_429_);
lean_ctor_set_uint32(v___x_430_, sizeof(void*)*1, v_osCode_428_);
return v___x_430_;
}
}
LEAN_EXPORT void lean_mk_io_error_protocol_error_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_428_ = stack[0].m_num;
lean_object* v_details_429_ = stack[1].m_obj;
lean_object* v_res_431_;
v_res_431_ = lean_mk_io_error_protocol_error(v_osCode_428_, v_details_429_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkProtocolError___boxed(lean_object* v_osCode_432_, lean_object* v_details_433_){
_start:
{
uint32_t v_osCode_boxed_434_; lean_object* v_res_435_; 
v_osCode_boxed_434_ = lean_unbox_uint32(v_osCode_432_);
lean_dec(v_osCode_432_);
v_res_435_ = lean_mk_io_error_protocol_error(v_osCode_boxed_434_, v_details_433_);
return v_res_435_;
}
}
lean_object* lean_mk_io_error_time_expired(uint32_t v_osCode_436_, lean_object* v_details_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = lean_alloc_ctor(9, 1, 4);
lean_ctor_set(v___x_438_, 0, v_details_437_);
lean_ctor_set_uint32(v___x_438_, sizeof(void*)*1, v_osCode_436_);
return v___x_438_;
}
}
LEAN_EXPORT void lean_mk_io_error_time_expired_0interp(lean_interpreter_value* stack)
{
uint32_t v_osCode_436_ = stack[0].m_num;
lean_object* v_details_437_ = stack[1].m_obj;
lean_object* v_res_439_;
v_res_439_ = lean_mk_io_error_time_expired(v_osCode_436_, v_details_437_);
stack->m_obj
 = v_res_439_;
}
LEAN_EXPORT lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object* v_osCode_440_, lean_object* v_details_441_){
_start:
{
uint32_t v_osCode_boxed_442_; lean_object* v_res_443_; 
v_osCode_boxed_442_ = lean_unbox_uint32(v_osCode_440_);
lean_dec(v_osCode_440_);
v_res_443_ = lean_mk_io_error_time_expired(v_osCode_boxed_442_, v_details_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object* v_s_444_){
_start:
{
lean_object* v___x_445_; uint32_t v___x_446_; uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_string_utf8_get(v_s_444_, v___x_445_);
v___x_447_ = 65;
v___x_448_ = lean_uint32_dec_le(v___x_447_, v___x_446_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
v___x_449_ = lean_string_utf8_set(v_s_444_, v___x_445_, v___x_446_);
return v___x_449_;
}
else
{
uint32_t v___x_450_; uint8_t v___x_451_; 
v___x_450_ = 90;
v___x_451_ = lean_uint32_dec_le(v___x_446_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_string_utf8_set(v_s_444_, v___x_445_, v___x_446_);
return v___x_452_;
}
else
{
uint32_t v___x_453_; uint32_t v___x_454_; lean_object* v___x_455_; 
v___x_453_ = 32;
v___x_454_ = lean_uint32_add(v___x_446_, v___x_453_);
v___x_455_ = lean_string_utf8_set(v_s_444_, v___x_445_, v___x_454_);
return v___x_455_;
}
}
}
}
lean_object* l_IO_Error_fopenErrorToString(lean_object* v_gist_459_, lean_object* v_fn_460_, uint32_t v_code_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_463_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_459_);
v___x_464_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_465_ = lean_string_append(v___x_463_, v___x_464_);
v___x_466_ = lean_uint32_to_nat(v_code_461_);
v___x_467_ = l_Nat_reprFast(v___x_466_);
v___x_468_ = lean_string_append(v___x_465_, v___x_467_);
lean_dec_ref(v___x_467_);
v___x_469_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
v___x_470_ = lean_string_append(v___x_468_, v___x_469_);
v___x_471_ = lean_string_append(v___x_470_, v_fn_460_);
return v___x_471_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_val_472_ = lean_ctor_get(v_x_462_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v_x_462_, 1);
v___x_473_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_459_);
v___x_474_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
v___x_476_ = lean_uint32_to_nat(v_code_461_);
v___x_477_ = l_Nat_reprFast(v___x_476_);
v___x_478_ = lean_string_append(v___x_475_, v___x_477_);
lean_dec_ref(v___x_477_);
v___x_479_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
v___x_481_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_472_);
v___x_482_ = lean_string_append(v___x_480_, v___x_481_);
lean_dec_ref(v___x_481_);
v___x_483_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
v___x_485_ = lean_string_append(v___x_484_, v_fn_460_);
return v___x_485_;
}
}
}
LEAN_EXPORT void l_IO_Error_fopenErrorToString_0interp(lean_interpreter_value* stack)
{
lean_object* v_gist_459_ = stack[0].m_obj;
lean_object* v_fn_460_ = stack[1].m_obj;
uint32_t v_code_461_ = stack[2].m_num;
lean_object* v_x_462_ = stack[3].m_obj;
lean_object* v_res_486_;
v_res_486_ = l_IO_Error_fopenErrorToString(v_gist_459_, v_fn_460_, v_code_461_, v_x_462_);
stack->m_obj
 = v_res_486_;
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object* v_gist_487_, lean_object* v_fn_488_, lean_object* v_code_489_, lean_object* v_x_490_){
_start:
{
uint32_t v_code_boxed_491_; lean_object* v_res_492_; 
v_code_boxed_491_ = lean_unbox_uint32(v_code_489_);
lean_dec(v_code_489_);
v_res_492_ = l_IO_Error_fopenErrorToString(v_gist_487_, v_fn_488_, v_code_boxed_491_, v_x_490_);
lean_dec_ref(v_fn_488_);
return v_res_492_;
}
}
lean_object* l_IO_Error_otherErrorToString(lean_object* v_gist_494_, uint32_t v_code_495_, lean_object* v_x_496_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_497_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_494_);
v___x_498_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_499_ = lean_string_append(v___x_497_, v___x_498_);
v___x_500_ = lean_uint32_to_nat(v_code_495_);
v___x_501_ = l_Nat_reprFast(v___x_500_);
v___x_502_ = lean_string_append(v___x_499_, v___x_501_);
lean_dec_ref(v___x_501_);
v___x_503_ = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
v___x_504_ = lean_string_append(v___x_502_, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_val_505_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_x_496_, 1);
v___x_506_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_494_);
v___x_507_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_508_ = lean_string_append(v___x_506_, v___x_507_);
v___x_509_ = lean_uint32_to_nat(v_code_495_);
v___x_510_ = l_Nat_reprFast(v___x_509_);
v___x_511_ = lean_string_append(v___x_508_, v___x_510_);
lean_dec_ref(v___x_510_);
v___x_512_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
v___x_514_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_505_);
v___x_515_ = lean_string_append(v___x_513_, v___x_514_);
lean_dec_ref(v___x_514_);
v___x_516_ = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
v___x_517_ = lean_string_append(v___x_515_, v___x_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT void l_IO_Error_otherErrorToString_0interp(lean_interpreter_value* stack)
{
lean_object* v_gist_494_ = stack[0].m_obj;
uint32_t v_code_495_ = stack[1].m_num;
lean_object* v_x_496_ = stack[2].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_IO_Error_otherErrorToString(v_gist_494_, v_code_495_, v_x_496_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString___boxed(lean_object* v_gist_519_, lean_object* v_code_520_, lean_object* v_x_521_){
_start:
{
uint32_t v_code_boxed_522_; lean_object* v_res_523_; 
v_code_boxed_522_ = lean_unbox_uint32(v_code_520_);
lean_dec(v_code_520_);
v_res_523_ = l_IO_Error_otherErrorToString(v_gist_519_, v_code_boxed_522_, v_x_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* lean_io_error_to_string(lean_object* v_x_540_){
_start:
{
uint32_t v_code_542_; lean_object* v_details_543_; 
switch(lean_obj_tag(v_x_540_))
{
case 0:
{
lean_object* v_filename_546_; 
v_filename_546_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_filename_546_);
if (lean_obj_tag(v_filename_546_) == 0)
{
uint32_t v_osCode_547_; lean_object* v_details_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_osCode_547_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_548_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_548_);
lean_dec_ref_known(v_x_540_, 2);
v___x_549_ = ((lean_object*)(l_IO_Error_toString___closed__0));
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v_details_548_);
v___x_551_ = l_IO_Error_otherErrorToString(v___x_549_, v_osCode_547_, v___x_550_);
return v___x_551_;
}
else
{
uint32_t v_osCode_552_; lean_object* v_details_553_; lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_563_; 
v_osCode_552_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_553_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_553_);
lean_dec_ref_known(v_x_540_, 2);
v_val_554_ = lean_ctor_get(v_filename_546_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_filename_546_);
if (v_isSharedCheck_563_ == 0)
{
v___x_556_ = v_filename_546_;
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v_filename_546_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = ((lean_object*)(l_IO_Error_toString___closed__0));
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_details_553_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_details_553_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = l_IO_Error_fopenErrorToString(v___x_558_, v_val_554_, v_osCode_552_, v___x_560_);
lean_dec(v_val_554_);
return v___x_561_;
}
}
}
}
case 1:
{
uint32_t v_osCode_564_; lean_object* v_details_565_; 
v_osCode_564_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
v_details_565_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_details_565_);
lean_dec_ref_known(v_x_540_, 1);
v_code_542_ = v_osCode_564_;
v_details_543_ = v_details_565_;
goto v___jp_541_;
}
case 2:
{
uint32_t v_osCode_566_; lean_object* v_details_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_osCode_566_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
v_details_567_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_details_567_);
lean_dec_ref_known(v_x_540_, 1);
v___x_568_ = ((lean_object*)(l_IO_Error_toString___closed__1));
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v_details_567_);
v___x_570_ = l_IO_Error_otherErrorToString(v___x_568_, v_osCode_566_, v___x_569_);
return v___x_570_;
}
case 3:
{
uint32_t v_osCode_571_; lean_object* v_details_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_osCode_571_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
v_details_572_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_details_572_);
lean_dec_ref_known(v_x_540_, 1);
v___x_573_ = ((lean_object*)(l_IO_Error_toString___closed__2));
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v_details_572_);
v___x_575_ = l_IO_Error_otherErrorToString(v___x_573_, v_osCode_571_, v___x_574_);
return v___x_575_;
}
case 4:
{
uint32_t v_osCode_576_; lean_object* v_details_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_osCode_576_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
v_details_577_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_details_577_);
lean_dec_ref_known(v_x_540_, 1);
v___x_578_ = ((lean_object*)(l_IO_Error_toString___closed__3));
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v_details_577_);
v___x_580_ = l_IO_Error_otherErrorToString(v___x_578_, v_osCode_576_, v___x_579_);
return v___x_580_;
}
case 5:
{
uint32_t v_osCode_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_osCode_581_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
lean_dec_ref_known(v_x_540_, 1);
v___x_582_ = ((lean_object*)(l_IO_Error_toString___closed__4));
v___x_583_ = lean_box(0);
v___x_584_ = l_IO_Error_otherErrorToString(v___x_582_, v_osCode_581_, v___x_583_);
return v___x_584_;
}
case 6:
{
uint32_t v_osCode_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_osCode_585_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
lean_dec_ref_known(v_x_540_, 1);
v___x_586_ = ((lean_object*)(l_IO_Error_toString___closed__5));
v___x_587_ = lean_box(0);
v___x_588_ = l_IO_Error_otherErrorToString(v___x_586_, v_osCode_585_, v___x_587_);
return v___x_588_;
}
case 7:
{
uint32_t v_osCode_589_; lean_object* v_details_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_osCode_589_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
v_details_590_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_details_590_);
lean_dec_ref_known(v_x_540_, 1);
v___x_591_ = ((lean_object*)(l_IO_Error_toString___closed__6));
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_details_590_);
v___x_593_ = l_IO_Error_otherErrorToString(v___x_591_, v_osCode_589_, v___x_592_);
return v___x_593_;
}
case 8:
{
uint32_t v_osCode_594_; lean_object* v_details_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_osCode_594_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
v_details_595_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_details_595_);
lean_dec_ref_known(v_x_540_, 1);
v___x_596_ = ((lean_object*)(l_IO_Error_toString___closed__7));
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_details_595_);
v___x_598_ = l_IO_Error_otherErrorToString(v___x_596_, v_osCode_594_, v___x_597_);
return v___x_598_;
}
case 9:
{
uint32_t v_osCode_599_; lean_object* v_details_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_osCode_599_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*1);
v_details_600_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_details_600_);
lean_dec_ref_known(v_x_540_, 1);
v___x_601_ = ((lean_object*)(l_IO_Error_toString___closed__8));
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_details_600_);
v___x_603_ = l_IO_Error_otherErrorToString(v___x_601_, v_osCode_599_, v___x_602_);
return v___x_603_;
}
case 10:
{
lean_object* v_filename_604_; uint32_t v_osCode_605_; lean_object* v_details_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_filename_604_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_filename_604_);
v_osCode_605_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_606_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_606_);
lean_dec_ref_known(v_x_540_, 2);
v___x_607_ = ((lean_object*)(l_IO_Error_toString___closed__9));
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v_details_606_);
v___x_609_ = l_IO_Error_fopenErrorToString(v___x_607_, v_filename_604_, v_osCode_605_, v___x_608_);
lean_dec_ref(v_filename_604_);
return v___x_609_;
}
case 11:
{
lean_object* v_filename_610_; uint32_t v_osCode_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_filename_610_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_filename_610_);
v_osCode_611_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
lean_dec_ref_known(v_x_540_, 2);
v___x_612_ = ((lean_object*)(l_IO_Error_toString___closed__10));
v___x_613_ = lean_box(0);
v___x_614_ = l_IO_Error_fopenErrorToString(v___x_612_, v_filename_610_, v_osCode_611_, v___x_613_);
lean_dec_ref(v_filename_610_);
return v___x_614_;
}
case 12:
{
lean_object* v_filename_615_; 
v_filename_615_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_filename_615_);
if (lean_obj_tag(v_filename_615_) == 0)
{
uint32_t v_osCode_616_; lean_object* v_details_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_osCode_616_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_617_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_617_);
lean_dec_ref_known(v_x_540_, 2);
v___x_618_ = ((lean_object*)(l_IO_Error_toString___closed__11));
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v_details_617_);
v___x_620_ = l_IO_Error_otherErrorToString(v___x_618_, v_osCode_616_, v___x_619_);
return v___x_620_;
}
else
{
uint32_t v_osCode_621_; lean_object* v_details_622_; lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_632_; 
v_osCode_621_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_622_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_622_);
lean_dec_ref_known(v_x_540_, 2);
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
v___x_627_ = ((lean_object*)(l_IO_Error_toString___closed__11));
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
case 13:
{
lean_object* v_filename_633_; 
v_filename_633_ = lean_ctor_get(v_x_540_, 0);
if (lean_obj_tag(v_filename_633_) == 0)
{
uint32_t v_osCode_634_; lean_object* v_details_635_; 
v_osCode_634_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_635_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_635_);
lean_dec_ref_known(v_x_540_, 2);
v_code_542_ = v_osCode_634_;
v_details_543_ = v_details_635_;
goto v___jp_541_;
}
else
{
uint32_t v_osCode_636_; lean_object* v_details_637_; lean_object* v_val_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_inc_ref(v_filename_633_);
v_osCode_636_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_637_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_637_);
lean_dec_ref_known(v_x_540_, 2);
v_val_638_ = lean_ctor_get(v_filename_633_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v_filename_633_, 1);
v___x_639_ = lean_box(0);
v___x_640_ = l_IO_Error_fopenErrorToString(v_details_637_, v_val_638_, v_osCode_636_, v___x_639_);
lean_dec(v_val_638_);
return v___x_640_;
}
}
case 14:
{
lean_object* v_filename_641_; 
v_filename_641_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_filename_641_);
if (lean_obj_tag(v_filename_641_) == 0)
{
uint32_t v_osCode_642_; lean_object* v_details_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_osCode_642_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_643_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_643_);
lean_dec_ref_known(v_x_540_, 2);
v___x_644_ = ((lean_object*)(l_IO_Error_toString___closed__12));
v___x_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_645_, 0, v_details_643_);
v___x_646_ = l_IO_Error_otherErrorToString(v___x_644_, v_osCode_642_, v___x_645_);
return v___x_646_;
}
else
{
uint32_t v_osCode_647_; lean_object* v_details_648_; lean_object* v_val_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_658_; 
v_osCode_647_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_648_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_648_);
lean_dec_ref_known(v_x_540_, 2);
v_val_649_ = lean_ctor_get(v_filename_641_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_filename_641_);
if (v_isSharedCheck_658_ == 0)
{
v___x_651_ = v_filename_641_;
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_val_649_);
lean_dec(v_filename_641_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = ((lean_object*)(l_IO_Error_toString___closed__12));
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v_details_648_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_details_648_);
v___x_655_ = v_reuseFailAlloc_657_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; 
v___x_656_ = l_IO_Error_fopenErrorToString(v___x_653_, v_val_649_, v_osCode_647_, v___x_655_);
lean_dec(v_val_649_);
return v___x_656_;
}
}
}
}
case 15:
{
lean_object* v_filename_659_; 
v_filename_659_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_filename_659_);
if (lean_obj_tag(v_filename_659_) == 0)
{
uint32_t v_osCode_660_; lean_object* v_details_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_osCode_660_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_661_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_661_);
lean_dec_ref_known(v_x_540_, 2);
v___x_662_ = ((lean_object*)(l_IO_Error_toString___closed__13));
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v_details_661_);
v___x_664_ = l_IO_Error_otherErrorToString(v___x_662_, v_osCode_660_, v___x_663_);
return v___x_664_;
}
else
{
uint32_t v_osCode_665_; lean_object* v_details_666_; lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_676_; 
v_osCode_665_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_666_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_666_);
lean_dec_ref_known(v_x_540_, 2);
v_val_667_ = lean_ctor_get(v_filename_659_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_filename_659_);
if (v_isSharedCheck_676_ == 0)
{
v___x_669_ = v_filename_659_;
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v_filename_659_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l_IO_Error_toString___closed__13));
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v_details_666_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_details_666_);
v___x_673_ = v_reuseFailAlloc_675_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; 
v___x_674_ = l_IO_Error_fopenErrorToString(v___x_671_, v_val_667_, v_osCode_665_, v___x_673_);
lean_dec(v_val_667_);
return v___x_674_;
}
}
}
}
case 16:
{
lean_object* v_filename_677_; 
v_filename_677_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_filename_677_);
if (lean_obj_tag(v_filename_677_) == 0)
{
uint32_t v_osCode_678_; lean_object* v_details_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_osCode_678_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_679_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_679_);
lean_dec_ref_known(v_x_540_, 2);
v___x_680_ = ((lean_object*)(l_IO_Error_toString___closed__14));
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v_details_679_);
v___x_682_ = l_IO_Error_otherErrorToString(v___x_680_, v_osCode_678_, v___x_681_);
return v___x_682_;
}
else
{
uint32_t v_osCode_683_; lean_object* v_details_684_; lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_694_; 
v_osCode_683_ = lean_ctor_get_uint32(v_x_540_, sizeof(void*)*2);
v_details_684_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_details_684_);
lean_dec_ref_known(v_x_540_, 2);
v_val_685_ = lean_ctor_get(v_filename_677_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_filename_677_);
if (v_isSharedCheck_694_ == 0)
{
v___x_687_ = v_filename_677_;
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_dec(v_filename_677_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = ((lean_object*)(l_IO_Error_toString___closed__14));
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v_details_684_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_details_684_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = l_IO_Error_fopenErrorToString(v___x_689_, v_val_685_, v_osCode_683_, v___x_691_);
lean_dec(v_val_685_);
return v___x_692_;
}
}
}
}
case 17:
{
lean_object* v___x_695_; 
v___x_695_ = ((lean_object*)(l_IO_Error_toString___closed__15));
return v___x_695_;
}
default: 
{
lean_object* v_msg_696_; 
v_msg_696_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_msg_696_);
lean_dec_ref_known(v_x_540_, 1);
return v_msg_696_;
}
}
v___jp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_box(0);
v___x_545_ = l_IO_Error_otherErrorToString(v_details_543_, v_code_542_, v___x_544_);
return v___x_545_;
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
