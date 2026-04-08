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
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
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
default: 
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(18u);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx___boxed(lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_IO_Error_ctorIdx(v_x_21_);
lean_dec(v_x_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim___redArg(lean_object* v_t_23_, lean_object* v_k_24_){
_start:
{
switch(lean_obj_tag(v_t_23_))
{
case 0:
{
lean_object* v_filename_25_; uint32_t v_osCode_26_; lean_object* v_details_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_filename_25_ = lean_ctor_get(v_t_23_, 0);
lean_inc(v_filename_25_);
v_osCode_26_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*2);
v_details_27_ = lean_ctor_get(v_t_23_, 1);
lean_inc_ref(v_details_27_);
lean_dec_ref(v_t_23_);
v___x_28_ = lean_box_uint32(v_osCode_26_);
v___x_29_ = lean_apply_3(v_k_24_, v_filename_25_, v___x_28_, v_details_27_);
return v___x_29_;
}
case 10:
{
lean_object* v_filename_30_; uint32_t v_osCode_31_; lean_object* v_details_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_filename_30_ = lean_ctor_get(v_t_23_, 0);
lean_inc_ref(v_filename_30_);
v_osCode_31_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*2);
v_details_32_ = lean_ctor_get(v_t_23_, 1);
lean_inc_ref(v_details_32_);
lean_dec_ref(v_t_23_);
v___x_33_ = lean_box_uint32(v_osCode_31_);
v___x_34_ = lean_apply_3(v_k_24_, v_filename_30_, v___x_33_, v_details_32_);
return v___x_34_;
}
case 11:
{
lean_object* v_filename_35_; uint32_t v_osCode_36_; lean_object* v_details_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_filename_35_ = lean_ctor_get(v_t_23_, 0);
lean_inc_ref(v_filename_35_);
v_osCode_36_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*2);
v_details_37_ = lean_ctor_get(v_t_23_, 1);
lean_inc_ref(v_details_37_);
lean_dec_ref(v_t_23_);
v___x_38_ = lean_box_uint32(v_osCode_36_);
v___x_39_ = lean_apply_3(v_k_24_, v_filename_35_, v___x_38_, v_details_37_);
return v___x_39_;
}
case 12:
{
lean_object* v_filename_40_; uint32_t v_osCode_41_; lean_object* v_details_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_filename_40_ = lean_ctor_get(v_t_23_, 0);
lean_inc(v_filename_40_);
v_osCode_41_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*2);
v_details_42_ = lean_ctor_get(v_t_23_, 1);
lean_inc_ref(v_details_42_);
lean_dec_ref(v_t_23_);
v___x_43_ = lean_box_uint32(v_osCode_41_);
v___x_44_ = lean_apply_3(v_k_24_, v_filename_40_, v___x_43_, v_details_42_);
return v___x_44_;
}
case 13:
{
lean_object* v_filename_45_; uint32_t v_osCode_46_; lean_object* v_details_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_filename_45_ = lean_ctor_get(v_t_23_, 0);
lean_inc(v_filename_45_);
v_osCode_46_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*2);
v_details_47_ = lean_ctor_get(v_t_23_, 1);
lean_inc_ref(v_details_47_);
lean_dec_ref(v_t_23_);
v___x_48_ = lean_box_uint32(v_osCode_46_);
v___x_49_ = lean_apply_3(v_k_24_, v_filename_45_, v___x_48_, v_details_47_);
return v___x_49_;
}
case 14:
{
lean_object* v_filename_50_; uint32_t v_osCode_51_; lean_object* v_details_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_filename_50_ = lean_ctor_get(v_t_23_, 0);
lean_inc(v_filename_50_);
v_osCode_51_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*2);
v_details_52_ = lean_ctor_get(v_t_23_, 1);
lean_inc_ref(v_details_52_);
lean_dec_ref(v_t_23_);
v___x_53_ = lean_box_uint32(v_osCode_51_);
v___x_54_ = lean_apply_3(v_k_24_, v_filename_50_, v___x_53_, v_details_52_);
return v___x_54_;
}
case 15:
{
lean_object* v_filename_55_; uint32_t v_osCode_56_; lean_object* v_details_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_filename_55_ = lean_ctor_get(v_t_23_, 0);
lean_inc(v_filename_55_);
v_osCode_56_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*2);
v_details_57_ = lean_ctor_get(v_t_23_, 1);
lean_inc_ref(v_details_57_);
lean_dec_ref(v_t_23_);
v___x_58_ = lean_box_uint32(v_osCode_56_);
v___x_59_ = lean_apply_3(v_k_24_, v_filename_55_, v___x_58_, v_details_57_);
return v___x_59_;
}
case 16:
{
lean_object* v_filename_60_; uint32_t v_osCode_61_; lean_object* v_details_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_filename_60_ = lean_ctor_get(v_t_23_, 0);
lean_inc(v_filename_60_);
v_osCode_61_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*2);
v_details_62_ = lean_ctor_get(v_t_23_, 1);
lean_inc_ref(v_details_62_);
lean_dec_ref(v_t_23_);
v___x_63_ = lean_box_uint32(v_osCode_61_);
v___x_64_ = lean_apply_3(v_k_24_, v_filename_60_, v___x_63_, v_details_62_);
return v___x_64_;
}
case 17:
{
return v_k_24_;
}
case 18:
{
lean_object* v_msg_65_; lean_object* v___x_66_; 
v_msg_65_ = lean_ctor_get(v_t_23_, 0);
lean_inc_ref(v_msg_65_);
lean_dec_ref(v_t_23_);
v___x_66_ = lean_apply_1(v_k_24_, v_msg_65_);
return v___x_66_;
}
default: 
{
uint32_t v_osCode_67_; lean_object* v_details_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_osCode_67_ = lean_ctor_get_uint32(v_t_23_, sizeof(void*)*1);
v_details_68_ = lean_ctor_get(v_t_23_, 0);
lean_inc_ref(v_details_68_);
lean_dec(v_t_23_);
v___x_69_ = lean_box_uint32(v_osCode_67_);
v___x_70_ = lean_apply_2(v_k_24_, v___x_69_, v_details_68_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim(lean_object* v_motive_71_, lean_object* v_ctorIdx_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_IO_Error_ctorElim___redArg(v_t_73_, v_k_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim___boxed(lean_object* v_motive_77_, lean_object* v_ctorIdx_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_k_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_IO_Error_ctorElim(v_motive_77_, v_ctorIdx_78_, v_t_79_, v_h_80_, v_k_81_);
lean_dec(v_ctorIdx_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_alreadyExists_elim___redArg(lean_object* v_t_83_, lean_object* v_alreadyExists_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_IO_Error_ctorElim___redArg(v_t_83_, v_alreadyExists_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_alreadyExists_elim(lean_object* v_motive_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_alreadyExists_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_IO_Error_ctorElim___redArg(v_t_87_, v_alreadyExists_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherError_elim___redArg(lean_object* v_t_91_, lean_object* v_otherError_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_IO_Error_ctorElim___redArg(v_t_91_, v_otherError_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherError_elim(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_otherError_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_IO_Error_ctorElim___redArg(v_t_95_, v_otherError_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceBusy_elim___redArg(lean_object* v_t_99_, lean_object* v_resourceBusy_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_IO_Error_ctorElim___redArg(v_t_99_, v_resourceBusy_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceBusy_elim(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_resourceBusy_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_IO_Error_ctorElim___redArg(v_t_103_, v_resourceBusy_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceVanished_elim___redArg(lean_object* v_t_107_, lean_object* v_resourceVanished_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_IO_Error_ctorElim___redArg(v_t_107_, v_resourceVanished_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceVanished_elim(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_resourceVanished_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_IO_Error_ctorElim___redArg(v_t_111_, v_resourceVanished_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsupportedOperation_elim___redArg(lean_object* v_t_115_, lean_object* v_unsupportedOperation_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_IO_Error_ctorElim___redArg(v_t_115_, v_unsupportedOperation_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsupportedOperation_elim(lean_object* v_motive_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_unsupportedOperation_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_IO_Error_ctorElim___redArg(v_t_119_, v_unsupportedOperation_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_hardwareFault_elim___redArg(lean_object* v_t_123_, lean_object* v_hardwareFault_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_IO_Error_ctorElim___redArg(v_t_123_, v_hardwareFault_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_hardwareFault_elim(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_hardwareFault_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_IO_Error_ctorElim___redArg(v_t_127_, v_hardwareFault_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsatisfiedConstraints_elim___redArg(lean_object* v_t_131_, lean_object* v_unsatisfiedConstraints_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_IO_Error_ctorElim___redArg(v_t_131_, v_unsatisfiedConstraints_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsatisfiedConstraints_elim(lean_object* v_motive_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_unsatisfiedConstraints_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_IO_Error_ctorElim___redArg(v_t_135_, v_unsatisfiedConstraints_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_illegalOperation_elim___redArg(lean_object* v_t_139_, lean_object* v_illegalOperation_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_IO_Error_ctorElim___redArg(v_t_139_, v_illegalOperation_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_illegalOperation_elim(lean_object* v_motive_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_illegalOperation_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_IO_Error_ctorElim___redArg(v_t_143_, v_illegalOperation_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_protocolError_elim___redArg(lean_object* v_t_147_, lean_object* v_protocolError_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_IO_Error_ctorElim___redArg(v_t_147_, v_protocolError_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_protocolError_elim(lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_protocolError_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_IO_Error_ctorElim___redArg(v_t_151_, v_protocolError_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_timeExpired_elim___redArg(lean_object* v_t_155_, lean_object* v_timeExpired_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_IO_Error_ctorElim___redArg(v_t_155_, v_timeExpired_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_timeExpired_elim(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_timeExpired_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_IO_Error_ctorElim___redArg(v_t_159_, v_timeExpired_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_interrupted_elim___redArg(lean_object* v_t_163_, lean_object* v_interrupted_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_IO_Error_ctorElim___redArg(v_t_163_, v_interrupted_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_interrupted_elim(lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_interrupted_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_IO_Error_ctorElim___redArg(v_t_167_, v_interrupted_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noFileOrDirectory_elim___redArg(lean_object* v_t_171_, lean_object* v_noFileOrDirectory_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_IO_Error_ctorElim___redArg(v_t_171_, v_noFileOrDirectory_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noFileOrDirectory_elim(lean_object* v_motive_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_noFileOrDirectory_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_IO_Error_ctorElim___redArg(v_t_175_, v_noFileOrDirectory_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_invalidArgument_elim___redArg(lean_object* v_t_179_, lean_object* v_invalidArgument_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_IO_Error_ctorElim___redArg(v_t_179_, v_invalidArgument_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_invalidArgument_elim(lean_object* v_motive_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_invalidArgument_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_IO_Error_ctorElim___redArg(v_t_183_, v_invalidArgument_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_permissionDenied_elim___redArg(lean_object* v_t_187_, lean_object* v_permissionDenied_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_IO_Error_ctorElim___redArg(v_t_187_, v_permissionDenied_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_permissionDenied_elim(lean_object* v_motive_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_permissionDenied_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_IO_Error_ctorElim___redArg(v_t_191_, v_permissionDenied_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceExhausted_elim___redArg(lean_object* v_t_195_, lean_object* v_resourceExhausted_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_IO_Error_ctorElim___redArg(v_t_195_, v_resourceExhausted_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceExhausted_elim(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_resourceExhausted_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_IO_Error_ctorElim___redArg(v_t_199_, v_resourceExhausted_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_inappropriateType_elim___redArg(lean_object* v_t_203_, lean_object* v_inappropriateType_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_IO_Error_ctorElim___redArg(v_t_203_, v_inappropriateType_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_inappropriateType_elim(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_inappropriateType_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_IO_Error_ctorElim___redArg(v_t_207_, v_inappropriateType_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noSuchThing_elim___redArg(lean_object* v_t_211_, lean_object* v_noSuchThing_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_IO_Error_ctorElim___redArg(v_t_211_, v_noSuchThing_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noSuchThing_elim(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_noSuchThing_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_IO_Error_ctorElim___redArg(v_t_215_, v_noSuchThing_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unexpectedEof_elim___redArg(lean_object* v_t_219_, lean_object* v_unexpectedEof_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_IO_Error_ctorElim___redArg(v_t_219_, v_unexpectedEof_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unexpectedEof_elim(lean_object* v_motive_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_unexpectedEof_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_IO_Error_ctorElim___redArg(v_t_223_, v_unexpectedEof_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_userError_elim___redArg(lean_object* v_t_227_, lean_object* v_userError_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_IO_Error_ctorElim___redArg(v_t_227_, v_userError_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_userError_elim(lean_object* v_motive_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_userError_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_IO_Error_ctorElim___redArg(v_t_231_, v_userError_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_user_error(lean_object* v_s_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_240_, 0, v_s_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists_file(lean_object* v_a_243_, uint32_t v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_a_243_);
v___x_247_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_245_);
lean_ctor_set_uint32(v___x_247_, sizeof(void*)*2, v_a_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExistsFile___boxed(lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
uint32_t v_a_20__boxed_251_; lean_object* v_res_252_; 
v_a_20__boxed_251_ = lean_unbox_uint32(v_a_249_);
lean_dec(v_a_249_);
v_res_252_ = lean_mk_io_error_already_exists_file(v_a_248_, v_a_20__boxed_251_, v_a_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_eof(lean_object* v_x_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_box(17);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type_file(lean_object* v_a_255_, uint32_t v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_a_255_);
v___x_259_ = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_a_257_);
lean_ctor_set_uint32(v___x_259_, sizeof(void*)*2, v_a_256_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
uint32_t v_a_20__boxed_263_; lean_object* v_res_264_; 
v_a_20__boxed_263_ = lean_unbox_uint32(v_a_261_);
lean_dec(v_a_261_);
v_res_264_ = lean_mk_io_error_inappropriate_type_file(v_a_260_, v_a_20__boxed_263_, v_a_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_interrupted(lean_object* v_filename_265_, uint32_t v_osCode_266_, lean_object* v_details_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(10, 2, 4);
lean_ctor_set(v___x_268_, 0, v_filename_265_);
lean_ctor_set(v___x_268_, 1, v_details_267_);
lean_ctor_set_uint32(v___x_268_, sizeof(void*)*2, v_osCode_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInterrupted___boxed(lean_object* v_filename_269_, lean_object* v_osCode_270_, lean_object* v_details_271_){
_start:
{
uint32_t v_osCode_boxed_272_; lean_object* v_res_273_; 
v_osCode_boxed_272_ = lean_unbox_uint32(v_osCode_270_);
lean_dec(v_osCode_270_);
v_res_273_ = lean_mk_io_error_interrupted(v_filename_269_, v_osCode_boxed_272_, v_details_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument_file(lean_object* v_a_274_, uint32_t v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v_a_274_);
v___x_278_ = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_276_);
lean_ctor_set_uint32(v___x_278_, sizeof(void*)*2, v_a_275_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
uint32_t v_a_20__boxed_282_; lean_object* v_res_283_; 
v_a_20__boxed_282_ = lean_unbox_uint32(v_a_280_);
lean_dec(v_a_280_);
v_res_283_ = lean_mk_io_error_invalid_argument_file(v_a_279_, v_a_20__boxed_282_, v_a_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_file_or_directory(lean_object* v_filename_284_, uint32_t v_osCode_285_, lean_object* v_details_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_287_, 0, v_filename_284_);
lean_ctor_set(v___x_287_, 1, v_details_286_);
lean_ctor_set_uint32(v___x_287_, sizeof(void*)*2, v_osCode_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object* v_filename_288_, lean_object* v_osCode_289_, lean_object* v_details_290_){
_start:
{
uint32_t v_osCode_boxed_291_; lean_object* v_res_292_; 
v_osCode_boxed_291_ = lean_unbox_uint32(v_osCode_289_);
lean_dec(v_osCode_289_);
v_res_292_ = lean_mk_io_error_no_file_or_directory(v_filename_288_, v_osCode_boxed_291_, v_details_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing_file(lean_object* v_a_293_, uint32_t v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v_a_293_);
v___x_297_ = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_295_);
lean_ctor_set_uint32(v___x_297_, sizeof(void*)*2, v_a_294_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
uint32_t v_a_20__boxed_301_; lean_object* v_res_302_; 
v_a_20__boxed_301_ = lean_unbox_uint32(v_a_299_);
lean_dec(v_a_299_);
v_res_302_ = lean_mk_io_error_no_such_thing_file(v_a_298_, v_a_20__boxed_301_, v_a_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied_file(lean_object* v_a_303_, uint32_t v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v_a_303_);
v___x_307_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_a_305_);
lean_ctor_set_uint32(v___x_307_, sizeof(void*)*2, v_a_304_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
uint32_t v_a_20__boxed_311_; lean_object* v_res_312_; 
v_a_20__boxed_311_ = lean_unbox_uint32(v_a_309_);
lean_dec(v_a_309_);
v_res_312_ = lean_mk_io_error_permission_denied_file(v_a_308_, v_a_20__boxed_311_, v_a_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted_file(lean_object* v_a_313_, uint32_t v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v_a_313_);
v___x_317_ = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_a_315_);
lean_ctor_set_uint32(v___x_317_, sizeof(void*)*2, v_a_314_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
uint32_t v_a_20__boxed_321_; lean_object* v_res_322_; 
v_a_20__boxed_321_ = lean_unbox_uint32(v_a_319_);
lean_dec(v_a_319_);
v_res_322_ = lean_mk_io_error_resource_exhausted_file(v_a_318_, v_a_20__boxed_321_, v_a_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_unsupported_operation(uint32_t v_osCode_323_, lean_object* v_details_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(4, 1, 4);
lean_ctor_set(v___x_325_, 0, v_details_324_);
lean_ctor_set_uint32(v___x_325_, sizeof(void*)*1, v_osCode_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object* v_osCode_326_, lean_object* v_details_327_){
_start:
{
uint32_t v_osCode_boxed_328_; lean_object* v_res_329_; 
v_osCode_boxed_328_ = lean_unbox_uint32(v_osCode_326_);
lean_dec(v_osCode_326_);
v_res_329_ = lean_mk_io_error_unsupported_operation(v_osCode_boxed_328_, v_details_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted(uint32_t v_osCode_330_, lean_object* v_details_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_box(0);
v___x_333_ = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_details_331_);
lean_ctor_set_uint32(v___x_333_, sizeof(void*)*2, v_osCode_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object* v_osCode_334_, lean_object* v_details_335_){
_start:
{
uint32_t v_osCode_boxed_336_; lean_object* v_res_337_; 
v_osCode_boxed_336_ = lean_unbox_uint32(v_osCode_334_);
lean_dec(v_osCode_334_);
v_res_337_ = lean_mk_io_error_resource_exhausted(v_osCode_boxed_336_, v_details_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists(uint32_t v_osCode_338_, lean_object* v_details_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
v___x_341_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v_details_339_);
lean_ctor_set_uint32(v___x_341_, sizeof(void*)*2, v_osCode_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object* v_osCode_342_, lean_object* v_details_343_){
_start:
{
uint32_t v_osCode_boxed_344_; lean_object* v_res_345_; 
v_osCode_boxed_344_ = lean_unbox_uint32(v_osCode_342_);
lean_dec(v_osCode_342_);
v_res_345_ = lean_mk_io_error_already_exists(v_osCode_boxed_344_, v_details_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type(uint32_t v_osCode_346_, lean_object* v_details_347_){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_details_347_);
lean_ctor_set_uint32(v___x_349_, sizeof(void*)*2, v_osCode_346_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object* v_osCode_350_, lean_object* v_details_351_){
_start:
{
uint32_t v_osCode_boxed_352_; lean_object* v_res_353_; 
v_osCode_boxed_352_ = lean_unbox_uint32(v_osCode_350_);
lean_dec(v_osCode_350_);
v_res_353_ = lean_mk_io_error_inappropriate_type(v_osCode_boxed_352_, v_details_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing(uint32_t v_osCode_354_, lean_object* v_details_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_box(0);
v___x_357_ = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_details_355_);
lean_ctor_set_uint32(v___x_357_, sizeof(void*)*2, v_osCode_354_);
return v___x_357_;
}
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
LEAN_EXPORT lean_object* lean_mk_io_error_resource_vanished(uint32_t v_osCode_362_, lean_object* v_details_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(3, 1, 4);
lean_ctor_set(v___x_364_, 0, v_details_363_);
lean_ctor_set_uint32(v___x_364_, sizeof(void*)*1, v_osCode_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object* v_osCode_365_, lean_object* v_details_366_){
_start:
{
uint32_t v_osCode_boxed_367_; lean_object* v_res_368_; 
v_osCode_boxed_367_ = lean_unbox_uint32(v_osCode_365_);
lean_dec(v_osCode_365_);
v_res_368_ = lean_mk_io_error_resource_vanished(v_osCode_boxed_367_, v_details_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_busy(uint32_t v_osCode_369_, lean_object* v_details_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_alloc_ctor(2, 1, 4);
lean_ctor_set(v___x_371_, 0, v_details_370_);
lean_ctor_set_uint32(v___x_371_, sizeof(void*)*1, v_osCode_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object* v_osCode_372_, lean_object* v_details_373_){
_start:
{
uint32_t v_osCode_boxed_374_; lean_object* v_res_375_; 
v_osCode_boxed_374_ = lean_unbox_uint32(v_osCode_372_);
lean_dec(v_osCode_372_);
v_res_375_ = lean_mk_io_error_resource_busy(v_osCode_boxed_374_, v_details_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument(uint32_t v_osCode_376_, lean_object* v_details_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v_details_377_);
lean_ctor_set_uint32(v___x_379_, sizeof(void*)*2, v_osCode_376_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object* v_osCode_380_, lean_object* v_details_381_){
_start:
{
uint32_t v_osCode_boxed_382_; lean_object* v_res_383_; 
v_osCode_boxed_382_ = lean_unbox_uint32(v_osCode_380_);
lean_dec(v_osCode_380_);
v_res_383_ = lean_mk_io_error_invalid_argument(v_osCode_boxed_382_, v_details_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_other_error(uint32_t v_osCode_384_, lean_object* v_details_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(1, 1, 4);
lean_ctor_set(v___x_386_, 0, v_details_385_);
lean_ctor_set_uint32(v___x_386_, sizeof(void*)*1, v_osCode_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkOtherError___boxed(lean_object* v_osCode_387_, lean_object* v_details_388_){
_start:
{
uint32_t v_osCode_boxed_389_; lean_object* v_res_390_; 
v_osCode_boxed_389_ = lean_unbox_uint32(v_osCode_387_);
lean_dec(v_osCode_387_);
v_res_390_ = lean_mk_io_error_other_error(v_osCode_boxed_389_, v_details_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied(uint32_t v_osCode_391_, lean_object* v_details_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_box(0);
v___x_394_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v_details_392_);
lean_ctor_set_uint32(v___x_394_, sizeof(void*)*2, v_osCode_391_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object* v_osCode_395_, lean_object* v_details_396_){
_start:
{
uint32_t v_osCode_boxed_397_; lean_object* v_res_398_; 
v_osCode_boxed_397_ = lean_unbox_uint32(v_osCode_395_);
lean_dec(v_osCode_395_);
v_res_398_ = lean_mk_io_error_permission_denied(v_osCode_boxed_397_, v_details_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_hardware_fault(uint32_t v_osCode_399_, lean_object* v_details_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_alloc_ctor(5, 1, 4);
lean_ctor_set(v___x_401_, 0, v_details_400_);
lean_ctor_set_uint32(v___x_401_, sizeof(void*)*1, v_osCode_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object* v_osCode_402_, lean_object* v_details_403_){
_start:
{
uint32_t v_osCode_boxed_404_; lean_object* v_res_405_; 
v_osCode_boxed_404_ = lean_unbox_uint32(v_osCode_402_);
lean_dec(v_osCode_402_);
v_res_405_ = lean_mk_io_error_hardware_fault(v_osCode_boxed_404_, v_details_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t v_osCode_406_, lean_object* v_details_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(6, 1, 4);
lean_ctor_set(v___x_408_, 0, v_details_407_);
lean_ctor_set_uint32(v___x_408_, sizeof(void*)*1, v_osCode_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object* v_osCode_409_, lean_object* v_details_410_){
_start:
{
uint32_t v_osCode_boxed_411_; lean_object* v_res_412_; 
v_osCode_boxed_411_ = lean_unbox_uint32(v_osCode_409_);
lean_dec(v_osCode_409_);
v_res_412_ = lean_mk_io_error_unsatisfied_constraints(v_osCode_boxed_411_, v_details_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_illegal_operation(uint32_t v_osCode_413_, lean_object* v_details_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_alloc_ctor(7, 1, 4);
lean_ctor_set(v___x_415_, 0, v_details_414_);
lean_ctor_set_uint32(v___x_415_, sizeof(void*)*1, v_osCode_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object* v_osCode_416_, lean_object* v_details_417_){
_start:
{
uint32_t v_osCode_boxed_418_; lean_object* v_res_419_; 
v_osCode_boxed_418_ = lean_unbox_uint32(v_osCode_416_);
lean_dec(v_osCode_416_);
v_res_419_ = lean_mk_io_error_illegal_operation(v_osCode_boxed_418_, v_details_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_protocol_error(uint32_t v_osCode_420_, lean_object* v_details_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(8, 1, 4);
lean_ctor_set(v___x_422_, 0, v_details_421_);
lean_ctor_set_uint32(v___x_422_, sizeof(void*)*1, v_osCode_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkProtocolError___boxed(lean_object* v_osCode_423_, lean_object* v_details_424_){
_start:
{
uint32_t v_osCode_boxed_425_; lean_object* v_res_426_; 
v_osCode_boxed_425_ = lean_unbox_uint32(v_osCode_423_);
lean_dec(v_osCode_423_);
v_res_426_ = lean_mk_io_error_protocol_error(v_osCode_boxed_425_, v_details_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_time_expired(uint32_t v_osCode_427_, lean_object* v_details_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(9, 1, 4);
lean_ctor_set(v___x_429_, 0, v_details_428_);
lean_ctor_set_uint32(v___x_429_, sizeof(void*)*1, v_osCode_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object* v_osCode_430_, lean_object* v_details_431_){
_start:
{
uint32_t v_osCode_boxed_432_; lean_object* v_res_433_; 
v_osCode_boxed_432_ = lean_unbox_uint32(v_osCode_430_);
lean_dec(v_osCode_430_);
v_res_433_ = lean_mk_io_error_time_expired(v_osCode_boxed_432_, v_details_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object* v_s_434_){
_start:
{
lean_object* v___x_435_; uint32_t v___x_436_; uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_string_utf8_get(v_s_434_, v___x_435_);
v___x_437_ = 65;
v___x_438_ = lean_uint32_dec_le(v___x_437_, v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
v___x_439_ = lean_string_utf8_set(v_s_434_, v___x_435_, v___x_436_);
return v___x_439_;
}
else
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 90;
v___x_441_ = lean_uint32_dec_le(v___x_436_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_string_utf8_set(v_s_434_, v___x_435_, v___x_436_);
return v___x_442_;
}
else
{
uint32_t v___x_443_; uint32_t v___x_444_; lean_object* v___x_445_; 
v___x_443_ = 32;
v___x_444_ = lean_uint32_add(v___x_436_, v___x_443_);
v___x_445_ = lean_string_utf8_set(v_s_434_, v___x_435_, v___x_444_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString(lean_object* v_gist_449_, lean_object* v_fn_450_, uint32_t v_code_451_, lean_object* v_x_452_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_453_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_449_);
v___x_454_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
v___x_456_ = lean_uint32_to_nat(v_code_451_);
v___x_457_ = l_Nat_reprFast(v___x_456_);
v___x_458_ = lean_string_append(v___x_455_, v___x_457_);
lean_dec_ref(v___x_457_);
v___x_459_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
v___x_460_ = lean_string_append(v___x_458_, v___x_459_);
v___x_461_ = lean_string_append(v___x_460_, v_fn_450_);
return v___x_461_;
}
else
{
lean_object* v_val_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_val_462_ = lean_ctor_get(v_x_452_, 0);
lean_inc(v_val_462_);
lean_dec_ref(v_x_452_);
v___x_463_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_449_);
v___x_464_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_465_ = lean_string_append(v___x_463_, v___x_464_);
v___x_466_ = lean_uint32_to_nat(v_code_451_);
v___x_467_ = l_Nat_reprFast(v___x_466_);
v___x_468_ = lean_string_append(v___x_465_, v___x_467_);
lean_dec_ref(v___x_467_);
v___x_469_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
v___x_470_ = lean_string_append(v___x_468_, v___x_469_);
v___x_471_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_462_);
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
v___x_475_ = lean_string_append(v___x_474_, v_fn_450_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object* v_gist_476_, lean_object* v_fn_477_, lean_object* v_code_478_, lean_object* v_x_479_){
_start:
{
uint32_t v_code_boxed_480_; lean_object* v_res_481_; 
v_code_boxed_480_ = lean_unbox_uint32(v_code_478_);
lean_dec(v_code_478_);
v_res_481_ = l_IO_Error_fopenErrorToString(v_gist_476_, v_fn_477_, v_code_boxed_480_, v_x_479_);
lean_dec_ref(v_fn_477_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString(lean_object* v_gist_483_, uint32_t v_code_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_486_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_483_);
v___x_487_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
v___x_489_ = lean_uint32_to_nat(v_code_484_);
v___x_490_ = l_Nat_reprFast(v___x_489_);
v___x_491_ = lean_string_append(v___x_488_, v___x_490_);
lean_dec_ref(v___x_490_);
v___x_492_ = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
return v___x_493_;
}
else
{
lean_object* v_val_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_val_494_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_val_494_);
lean_dec_ref(v_x_485_);
v___x_495_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_483_);
v___x_496_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_497_ = lean_string_append(v___x_495_, v___x_496_);
v___x_498_ = lean_uint32_to_nat(v_code_484_);
v___x_499_ = l_Nat_reprFast(v___x_498_);
v___x_500_ = lean_string_append(v___x_497_, v___x_499_);
lean_dec_ref(v___x_499_);
v___x_501_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
v___x_502_ = lean_string_append(v___x_500_, v___x_501_);
v___x_503_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_494_);
v___x_504_ = lean_string_append(v___x_502_, v___x_503_);
lean_dec_ref(v___x_503_);
v___x_505_ = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
v___x_506_ = lean_string_append(v___x_504_, v___x_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString___boxed(lean_object* v_gist_507_, lean_object* v_code_508_, lean_object* v_x_509_){
_start:
{
uint32_t v_code_boxed_510_; lean_object* v_res_511_; 
v_code_boxed_510_ = lean_unbox_uint32(v_code_508_);
lean_dec(v_code_508_);
v_res_511_ = l_IO_Error_otherErrorToString(v_gist_507_, v_code_boxed_510_, v_x_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* lean_io_error_to_string(lean_object* v_x_528_){
_start:
{
uint32_t v_code_530_; lean_object* v_details_531_; 
switch(lean_obj_tag(v_x_528_))
{
case 0:
{
lean_object* v_filename_534_; 
v_filename_534_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_filename_534_);
if (lean_obj_tag(v_filename_534_) == 0)
{
uint32_t v_osCode_535_; lean_object* v_details_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_osCode_535_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_536_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_536_);
lean_dec_ref(v_x_528_);
v___x_537_ = ((lean_object*)(l_IO_Error_toString___closed__0));
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v_details_536_);
v___x_539_ = l_IO_Error_otherErrorToString(v___x_537_, v_osCode_535_, v___x_538_);
return v___x_539_;
}
else
{
uint32_t v_osCode_540_; lean_object* v_details_541_; lean_object* v_val_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_551_; 
v_osCode_540_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_541_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_541_);
lean_dec_ref(v_x_528_);
v_val_542_ = lean_ctor_get(v_filename_534_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_filename_534_);
if (v_isSharedCheck_551_ == 0)
{
v___x_544_ = v_filename_534_;
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_val_542_);
lean_dec(v_filename_534_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = ((lean_object*)(l_IO_Error_toString___closed__0));
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v_details_541_);
v___x_548_ = v___x_544_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_details_541_);
v___x_548_ = v_reuseFailAlloc_550_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; 
v___x_549_ = l_IO_Error_fopenErrorToString(v___x_546_, v_val_542_, v_osCode_540_, v___x_548_);
lean_dec(v_val_542_);
return v___x_549_;
}
}
}
}
case 1:
{
uint32_t v_osCode_552_; lean_object* v_details_553_; 
v_osCode_552_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
v_details_553_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_details_553_);
lean_dec_ref(v_x_528_);
v_code_530_ = v_osCode_552_;
v_details_531_ = v_details_553_;
goto v___jp_529_;
}
case 2:
{
uint32_t v_osCode_554_; lean_object* v_details_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_osCode_554_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
v_details_555_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_details_555_);
lean_dec_ref(v_x_528_);
v___x_556_ = ((lean_object*)(l_IO_Error_toString___closed__1));
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_details_555_);
v___x_558_ = l_IO_Error_otherErrorToString(v___x_556_, v_osCode_554_, v___x_557_);
return v___x_558_;
}
case 3:
{
uint32_t v_osCode_559_; lean_object* v_details_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_osCode_559_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
v_details_560_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_details_560_);
lean_dec_ref(v_x_528_);
v___x_561_ = ((lean_object*)(l_IO_Error_toString___closed__2));
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v_details_560_);
v___x_563_ = l_IO_Error_otherErrorToString(v___x_561_, v_osCode_559_, v___x_562_);
return v___x_563_;
}
case 4:
{
uint32_t v_osCode_564_; lean_object* v_details_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_osCode_564_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
v_details_565_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_details_565_);
lean_dec_ref(v_x_528_);
v___x_566_ = ((lean_object*)(l_IO_Error_toString___closed__3));
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v_details_565_);
v___x_568_ = l_IO_Error_otherErrorToString(v___x_566_, v_osCode_564_, v___x_567_);
return v___x_568_;
}
case 5:
{
uint32_t v_osCode_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_osCode_569_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
lean_dec_ref(v_x_528_);
v___x_570_ = ((lean_object*)(l_IO_Error_toString___closed__4));
v___x_571_ = lean_box(0);
v___x_572_ = l_IO_Error_otherErrorToString(v___x_570_, v_osCode_569_, v___x_571_);
return v___x_572_;
}
case 6:
{
uint32_t v_osCode_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_osCode_573_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
lean_dec_ref(v_x_528_);
v___x_574_ = ((lean_object*)(l_IO_Error_toString___closed__5));
v___x_575_ = lean_box(0);
v___x_576_ = l_IO_Error_otherErrorToString(v___x_574_, v_osCode_573_, v___x_575_);
return v___x_576_;
}
case 7:
{
uint32_t v_osCode_577_; lean_object* v_details_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_osCode_577_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
v_details_578_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_details_578_);
lean_dec_ref(v_x_528_);
v___x_579_ = ((lean_object*)(l_IO_Error_toString___closed__6));
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v_details_578_);
v___x_581_ = l_IO_Error_otherErrorToString(v___x_579_, v_osCode_577_, v___x_580_);
return v___x_581_;
}
case 8:
{
uint32_t v_osCode_582_; lean_object* v_details_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_osCode_582_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
v_details_583_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_details_583_);
lean_dec_ref(v_x_528_);
v___x_584_ = ((lean_object*)(l_IO_Error_toString___closed__7));
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_details_583_);
v___x_586_ = l_IO_Error_otherErrorToString(v___x_584_, v_osCode_582_, v___x_585_);
return v___x_586_;
}
case 9:
{
uint32_t v_osCode_587_; lean_object* v_details_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_osCode_587_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*1);
v_details_588_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_details_588_);
lean_dec_ref(v_x_528_);
v___x_589_ = ((lean_object*)(l_IO_Error_toString___closed__8));
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v_details_588_);
v___x_591_ = l_IO_Error_otherErrorToString(v___x_589_, v_osCode_587_, v___x_590_);
return v___x_591_;
}
case 10:
{
lean_object* v_filename_592_; uint32_t v_osCode_593_; lean_object* v_details_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_filename_592_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_filename_592_);
v_osCode_593_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_594_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_594_);
lean_dec_ref(v_x_528_);
v___x_595_ = ((lean_object*)(l_IO_Error_toString___closed__9));
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v_details_594_);
v___x_597_ = l_IO_Error_fopenErrorToString(v___x_595_, v_filename_592_, v_osCode_593_, v___x_596_);
lean_dec_ref(v_filename_592_);
return v___x_597_;
}
case 11:
{
lean_object* v_filename_598_; uint32_t v_osCode_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_filename_598_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_filename_598_);
v_osCode_599_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
lean_dec_ref(v_x_528_);
v___x_600_ = ((lean_object*)(l_IO_Error_toString___closed__10));
v___x_601_ = lean_box(0);
v___x_602_ = l_IO_Error_fopenErrorToString(v___x_600_, v_filename_598_, v_osCode_599_, v___x_601_);
lean_dec_ref(v_filename_598_);
return v___x_602_;
}
case 12:
{
lean_object* v_filename_603_; 
v_filename_603_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_filename_603_);
if (lean_obj_tag(v_filename_603_) == 0)
{
uint32_t v_osCode_604_; lean_object* v_details_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_osCode_604_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_605_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_605_);
lean_dec_ref(v_x_528_);
v___x_606_ = ((lean_object*)(l_IO_Error_toString___closed__11));
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v_details_605_);
v___x_608_ = l_IO_Error_otherErrorToString(v___x_606_, v_osCode_604_, v___x_607_);
return v___x_608_;
}
else
{
uint32_t v_osCode_609_; lean_object* v_details_610_; lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v_osCode_609_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_610_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_610_);
lean_dec_ref(v_x_528_);
v_val_611_ = lean_ctor_get(v_filename_603_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_filename_603_);
if (v_isSharedCheck_620_ == 0)
{
v___x_613_ = v_filename_603_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v_filename_603_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = ((lean_object*)(l_IO_Error_toString___closed__11));
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_details_610_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_details_610_);
v___x_617_ = v_reuseFailAlloc_619_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = l_IO_Error_fopenErrorToString(v___x_615_, v_val_611_, v_osCode_609_, v___x_617_);
lean_dec(v_val_611_);
return v___x_618_;
}
}
}
}
case 13:
{
lean_object* v_filename_621_; 
v_filename_621_ = lean_ctor_get(v_x_528_, 0);
if (lean_obj_tag(v_filename_621_) == 0)
{
uint32_t v_osCode_622_; lean_object* v_details_623_; 
v_osCode_622_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_623_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_623_);
lean_dec_ref(v_x_528_);
v_code_530_ = v_osCode_622_;
v_details_531_ = v_details_623_;
goto v___jp_529_;
}
else
{
uint32_t v_osCode_624_; lean_object* v_details_625_; lean_object* v_val_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_inc_ref(v_filename_621_);
v_osCode_624_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_625_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_625_);
lean_dec_ref(v_x_528_);
v_val_626_ = lean_ctor_get(v_filename_621_, 0);
lean_inc(v_val_626_);
lean_dec_ref(v_filename_621_);
v___x_627_ = lean_box(0);
v___x_628_ = l_IO_Error_fopenErrorToString(v_details_625_, v_val_626_, v_osCode_624_, v___x_627_);
lean_dec(v_val_626_);
return v___x_628_;
}
}
case 14:
{
lean_object* v_filename_629_; 
v_filename_629_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_filename_629_);
if (lean_obj_tag(v_filename_629_) == 0)
{
uint32_t v_osCode_630_; lean_object* v_details_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_osCode_630_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_631_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_631_);
lean_dec_ref(v_x_528_);
v___x_632_ = ((lean_object*)(l_IO_Error_toString___closed__12));
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v_details_631_);
v___x_634_ = l_IO_Error_otherErrorToString(v___x_632_, v_osCode_630_, v___x_633_);
return v___x_634_;
}
else
{
uint32_t v_osCode_635_; lean_object* v_details_636_; lean_object* v_val_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_646_; 
v_osCode_635_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_636_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_636_);
lean_dec_ref(v_x_528_);
v_val_637_ = lean_ctor_get(v_filename_629_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_filename_629_);
if (v_isSharedCheck_646_ == 0)
{
v___x_639_ = v_filename_629_;
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_val_637_);
lean_dec(v_filename_629_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = ((lean_object*)(l_IO_Error_toString___closed__12));
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_details_636_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_details_636_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; 
v___x_644_ = l_IO_Error_fopenErrorToString(v___x_641_, v_val_637_, v_osCode_635_, v___x_643_);
lean_dec(v_val_637_);
return v___x_644_;
}
}
}
}
case 15:
{
lean_object* v_filename_647_; 
v_filename_647_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_filename_647_);
if (lean_obj_tag(v_filename_647_) == 0)
{
uint32_t v_osCode_648_; lean_object* v_details_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_osCode_648_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_649_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_649_);
lean_dec_ref(v_x_528_);
v___x_650_ = ((lean_object*)(l_IO_Error_toString___closed__13));
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v_details_649_);
v___x_652_ = l_IO_Error_otherErrorToString(v___x_650_, v_osCode_648_, v___x_651_);
return v___x_652_;
}
else
{
uint32_t v_osCode_653_; lean_object* v_details_654_; lean_object* v_val_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_664_; 
v_osCode_653_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_654_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_654_);
lean_dec_ref(v_x_528_);
v_val_655_ = lean_ctor_get(v_filename_647_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_filename_647_);
if (v_isSharedCheck_664_ == 0)
{
v___x_657_ = v_filename_647_;
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_val_655_);
lean_dec(v_filename_647_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = ((lean_object*)(l_IO_Error_toString___closed__13));
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_details_654_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_details_654_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; 
v___x_662_ = l_IO_Error_fopenErrorToString(v___x_659_, v_val_655_, v_osCode_653_, v___x_661_);
lean_dec(v_val_655_);
return v___x_662_;
}
}
}
}
case 16:
{
lean_object* v_filename_665_; 
v_filename_665_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_filename_665_);
if (lean_obj_tag(v_filename_665_) == 0)
{
uint32_t v_osCode_666_; lean_object* v_details_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_osCode_666_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_667_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_667_);
lean_dec_ref(v_x_528_);
v___x_668_ = ((lean_object*)(l_IO_Error_toString___closed__14));
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_details_667_);
v___x_670_ = l_IO_Error_otherErrorToString(v___x_668_, v_osCode_666_, v___x_669_);
return v___x_670_;
}
else
{
uint32_t v_osCode_671_; lean_object* v_details_672_; lean_object* v_val_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_682_; 
v_osCode_671_ = lean_ctor_get_uint32(v_x_528_, sizeof(void*)*2);
v_details_672_ = lean_ctor_get(v_x_528_, 1);
lean_inc_ref(v_details_672_);
lean_dec_ref(v_x_528_);
v_val_673_ = lean_ctor_get(v_filename_665_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v_filename_665_);
if (v_isSharedCheck_682_ == 0)
{
v___x_675_ = v_filename_665_;
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_val_673_);
lean_dec(v_filename_665_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = ((lean_object*)(l_IO_Error_toString___closed__14));
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v_details_672_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_details_672_);
v___x_679_ = v_reuseFailAlloc_681_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = l_IO_Error_fopenErrorToString(v___x_677_, v_val_673_, v_osCode_671_, v___x_679_);
lean_dec(v_val_673_);
return v___x_680_;
}
}
}
}
case 17:
{
lean_object* v___x_683_; 
v___x_683_ = ((lean_object*)(l_IO_Error_toString___closed__15));
return v___x_683_;
}
default: 
{
lean_object* v_msg_684_; 
v_msg_684_ = lean_ctor_get(v_x_528_, 0);
lean_inc_ref(v_msg_684_);
lean_dec_ref(v_x_528_);
return v_msg_684_;
}
}
v___jp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_box(0);
v___x_533_ = l_IO_Error_otherErrorToString(v_details_531_, v_code_530_, v___x_532_);
return v___x_533_;
}
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_IOError(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
