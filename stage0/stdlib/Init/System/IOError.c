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
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_dec_ref_known(v_t_23_, 2);
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
lean_dec_ref_known(v_t_23_, 2);
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
lean_dec_ref_known(v_t_23_, 2);
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
lean_dec_ref_known(v_t_23_, 2);
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
lean_dec_ref_known(v_t_23_, 2);
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
lean_dec_ref_known(v_t_23_, 2);
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
lean_dec_ref_known(v_t_23_, 2);
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
lean_dec_ref_known(v_t_23_, 2);
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
lean_dec_ref_known(v_t_23_, 1);
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
LEAN_EXPORT lean_object* l_IO_Error_mkEofError___redArg(){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_box(17);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkEofError___redArg___boxed(lean_object* v___dummy_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_IO_Error_mkEofError___redArg();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_eof(lean_object* v_x_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_box(17);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type_file(lean_object* v_a_259_, uint32_t v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v_a_259_);
v___x_263_ = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_a_261_);
lean_ctor_set_uint32(v___x_263_, sizeof(void*)*2, v_a_260_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
uint32_t v_a_20__boxed_267_; lean_object* v_res_268_; 
v_a_20__boxed_267_ = lean_unbox_uint32(v_a_265_);
lean_dec(v_a_265_);
v_res_268_ = lean_mk_io_error_inappropriate_type_file(v_a_264_, v_a_20__boxed_267_, v_a_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_interrupted(lean_object* v_filename_269_, uint32_t v_osCode_270_, lean_object* v_details_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(10, 2, 4);
lean_ctor_set(v___x_272_, 0, v_filename_269_);
lean_ctor_set(v___x_272_, 1, v_details_271_);
lean_ctor_set_uint32(v___x_272_, sizeof(void*)*2, v_osCode_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInterrupted___boxed(lean_object* v_filename_273_, lean_object* v_osCode_274_, lean_object* v_details_275_){
_start:
{
uint32_t v_osCode_boxed_276_; lean_object* v_res_277_; 
v_osCode_boxed_276_ = lean_unbox_uint32(v_osCode_274_);
lean_dec(v_osCode_274_);
v_res_277_ = lean_mk_io_error_interrupted(v_filename_273_, v_osCode_boxed_276_, v_details_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument_file(lean_object* v_a_278_, uint32_t v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_a_278_);
v___x_282_ = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_a_280_);
lean_ctor_set_uint32(v___x_282_, sizeof(void*)*2, v_a_279_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
uint32_t v_a_20__boxed_286_; lean_object* v_res_287_; 
v_a_20__boxed_286_ = lean_unbox_uint32(v_a_284_);
lean_dec(v_a_284_);
v_res_287_ = lean_mk_io_error_invalid_argument_file(v_a_283_, v_a_20__boxed_286_, v_a_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_file_or_directory(lean_object* v_filename_288_, uint32_t v_osCode_289_, lean_object* v_details_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_291_, 0, v_filename_288_);
lean_ctor_set(v___x_291_, 1, v_details_290_);
lean_ctor_set_uint32(v___x_291_, sizeof(void*)*2, v_osCode_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object* v_filename_292_, lean_object* v_osCode_293_, lean_object* v_details_294_){
_start:
{
uint32_t v_osCode_boxed_295_; lean_object* v_res_296_; 
v_osCode_boxed_295_ = lean_unbox_uint32(v_osCode_293_);
lean_dec(v_osCode_293_);
v_res_296_ = lean_mk_io_error_no_file_or_directory(v_filename_292_, v_osCode_boxed_295_, v_details_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing_file(lean_object* v_a_297_, uint32_t v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v_a_297_);
v___x_301_ = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_a_299_);
lean_ctor_set_uint32(v___x_301_, sizeof(void*)*2, v_a_298_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
uint32_t v_a_20__boxed_305_; lean_object* v_res_306_; 
v_a_20__boxed_305_ = lean_unbox_uint32(v_a_303_);
lean_dec(v_a_303_);
v_res_306_ = lean_mk_io_error_no_such_thing_file(v_a_302_, v_a_20__boxed_305_, v_a_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied_file(lean_object* v_a_307_, uint32_t v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_a_307_);
v___x_311_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_309_);
lean_ctor_set_uint32(v___x_311_, sizeof(void*)*2, v_a_308_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
uint32_t v_a_20__boxed_315_; lean_object* v_res_316_; 
v_a_20__boxed_315_ = lean_unbox_uint32(v_a_313_);
lean_dec(v_a_313_);
v_res_316_ = lean_mk_io_error_permission_denied_file(v_a_312_, v_a_20__boxed_315_, v_a_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted_file(lean_object* v_a_317_, uint32_t v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_a_317_);
v___x_321_ = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_a_319_);
lean_ctor_set_uint32(v___x_321_, sizeof(void*)*2, v_a_318_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
uint32_t v_a_20__boxed_325_; lean_object* v_res_326_; 
v_a_20__boxed_325_ = lean_unbox_uint32(v_a_323_);
lean_dec(v_a_323_);
v_res_326_ = lean_mk_io_error_resource_exhausted_file(v_a_322_, v_a_20__boxed_325_, v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_unsupported_operation(uint32_t v_osCode_327_, lean_object* v_details_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(4, 1, 4);
lean_ctor_set(v___x_329_, 0, v_details_328_);
lean_ctor_set_uint32(v___x_329_, sizeof(void*)*1, v_osCode_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object* v_osCode_330_, lean_object* v_details_331_){
_start:
{
uint32_t v_osCode_boxed_332_; lean_object* v_res_333_; 
v_osCode_boxed_332_ = lean_unbox_uint32(v_osCode_330_);
lean_dec(v_osCode_330_);
v_res_333_ = lean_mk_io_error_unsupported_operation(v_osCode_boxed_332_, v_details_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted(uint32_t v_osCode_334_, lean_object* v_details_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v_details_335_);
lean_ctor_set_uint32(v___x_337_, sizeof(void*)*2, v_osCode_334_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object* v_osCode_338_, lean_object* v_details_339_){
_start:
{
uint32_t v_osCode_boxed_340_; lean_object* v_res_341_; 
v_osCode_boxed_340_ = lean_unbox_uint32(v_osCode_338_);
lean_dec(v_osCode_338_);
v_res_341_ = lean_mk_io_error_resource_exhausted(v_osCode_boxed_340_, v_details_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists(uint32_t v_osCode_342_, lean_object* v_details_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_box(0);
v___x_345_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_details_343_);
lean_ctor_set_uint32(v___x_345_, sizeof(void*)*2, v_osCode_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object* v_osCode_346_, lean_object* v_details_347_){
_start:
{
uint32_t v_osCode_boxed_348_; lean_object* v_res_349_; 
v_osCode_boxed_348_ = lean_unbox_uint32(v_osCode_346_);
lean_dec(v_osCode_346_);
v_res_349_ = lean_mk_io_error_already_exists(v_osCode_boxed_348_, v_details_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type(uint32_t v_osCode_350_, lean_object* v_details_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_details_351_);
lean_ctor_set_uint32(v___x_353_, sizeof(void*)*2, v_osCode_350_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object* v_osCode_354_, lean_object* v_details_355_){
_start:
{
uint32_t v_osCode_boxed_356_; lean_object* v_res_357_; 
v_osCode_boxed_356_ = lean_unbox_uint32(v_osCode_354_);
lean_dec(v_osCode_354_);
v_res_357_ = lean_mk_io_error_inappropriate_type(v_osCode_boxed_356_, v_details_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing(uint32_t v_osCode_358_, lean_object* v_details_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_details_359_);
lean_ctor_set_uint32(v___x_361_, sizeof(void*)*2, v_osCode_358_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThing___boxed(lean_object* v_osCode_362_, lean_object* v_details_363_){
_start:
{
uint32_t v_osCode_boxed_364_; lean_object* v_res_365_; 
v_osCode_boxed_364_ = lean_unbox_uint32(v_osCode_362_);
lean_dec(v_osCode_362_);
v_res_365_ = lean_mk_io_error_no_such_thing(v_osCode_boxed_364_, v_details_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_vanished(uint32_t v_osCode_366_, lean_object* v_details_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(3, 1, 4);
lean_ctor_set(v___x_368_, 0, v_details_367_);
lean_ctor_set_uint32(v___x_368_, sizeof(void*)*1, v_osCode_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object* v_osCode_369_, lean_object* v_details_370_){
_start:
{
uint32_t v_osCode_boxed_371_; lean_object* v_res_372_; 
v_osCode_boxed_371_ = lean_unbox_uint32(v_osCode_369_);
lean_dec(v_osCode_369_);
v_res_372_ = lean_mk_io_error_resource_vanished(v_osCode_boxed_371_, v_details_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_busy(uint32_t v_osCode_373_, lean_object* v_details_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(2, 1, 4);
lean_ctor_set(v___x_375_, 0, v_details_374_);
lean_ctor_set_uint32(v___x_375_, sizeof(void*)*1, v_osCode_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object* v_osCode_376_, lean_object* v_details_377_){
_start:
{
uint32_t v_osCode_boxed_378_; lean_object* v_res_379_; 
v_osCode_boxed_378_ = lean_unbox_uint32(v_osCode_376_);
lean_dec(v_osCode_376_);
v_res_379_ = lean_mk_io_error_resource_busy(v_osCode_boxed_378_, v_details_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument(uint32_t v_osCode_380_, lean_object* v_details_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_box(0);
v___x_383_ = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_details_381_);
lean_ctor_set_uint32(v___x_383_, sizeof(void*)*2, v_osCode_380_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object* v_osCode_384_, lean_object* v_details_385_){
_start:
{
uint32_t v_osCode_boxed_386_; lean_object* v_res_387_; 
v_osCode_boxed_386_ = lean_unbox_uint32(v_osCode_384_);
lean_dec(v_osCode_384_);
v_res_387_ = lean_mk_io_error_invalid_argument(v_osCode_boxed_386_, v_details_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_other_error(uint32_t v_osCode_388_, lean_object* v_details_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(1, 1, 4);
lean_ctor_set(v___x_390_, 0, v_details_389_);
lean_ctor_set_uint32(v___x_390_, sizeof(void*)*1, v_osCode_388_);
return v___x_390_;
}
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
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied(uint32_t v_osCode_395_, lean_object* v_details_396_){
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
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object* v_osCode_399_, lean_object* v_details_400_){
_start:
{
uint32_t v_osCode_boxed_401_; lean_object* v_res_402_; 
v_osCode_boxed_401_ = lean_unbox_uint32(v_osCode_399_);
lean_dec(v_osCode_399_);
v_res_402_ = lean_mk_io_error_permission_denied(v_osCode_boxed_401_, v_details_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_hardware_fault(uint32_t v_osCode_403_, lean_object* v_details_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(5, 1, 4);
lean_ctor_set(v___x_405_, 0, v_details_404_);
lean_ctor_set_uint32(v___x_405_, sizeof(void*)*1, v_osCode_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object* v_osCode_406_, lean_object* v_details_407_){
_start:
{
uint32_t v_osCode_boxed_408_; lean_object* v_res_409_; 
v_osCode_boxed_408_ = lean_unbox_uint32(v_osCode_406_);
lean_dec(v_osCode_406_);
v_res_409_ = lean_mk_io_error_hardware_fault(v_osCode_boxed_408_, v_details_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t v_osCode_410_, lean_object* v_details_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = lean_alloc_ctor(6, 1, 4);
lean_ctor_set(v___x_412_, 0, v_details_411_);
lean_ctor_set_uint32(v___x_412_, sizeof(void*)*1, v_osCode_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object* v_osCode_413_, lean_object* v_details_414_){
_start:
{
uint32_t v_osCode_boxed_415_; lean_object* v_res_416_; 
v_osCode_boxed_415_ = lean_unbox_uint32(v_osCode_413_);
lean_dec(v_osCode_413_);
v_res_416_ = lean_mk_io_error_unsatisfied_constraints(v_osCode_boxed_415_, v_details_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_illegal_operation(uint32_t v_osCode_417_, lean_object* v_details_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = lean_alloc_ctor(7, 1, 4);
lean_ctor_set(v___x_419_, 0, v_details_418_);
lean_ctor_set_uint32(v___x_419_, sizeof(void*)*1, v_osCode_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object* v_osCode_420_, lean_object* v_details_421_){
_start:
{
uint32_t v_osCode_boxed_422_; lean_object* v_res_423_; 
v_osCode_boxed_422_ = lean_unbox_uint32(v_osCode_420_);
lean_dec(v_osCode_420_);
v_res_423_ = lean_mk_io_error_illegal_operation(v_osCode_boxed_422_, v_details_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_protocol_error(uint32_t v_osCode_424_, lean_object* v_details_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(8, 1, 4);
lean_ctor_set(v___x_426_, 0, v_details_425_);
lean_ctor_set_uint32(v___x_426_, sizeof(void*)*1, v_osCode_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkProtocolError___boxed(lean_object* v_osCode_427_, lean_object* v_details_428_){
_start:
{
uint32_t v_osCode_boxed_429_; lean_object* v_res_430_; 
v_osCode_boxed_429_ = lean_unbox_uint32(v_osCode_427_);
lean_dec(v_osCode_427_);
v_res_430_ = lean_mk_io_error_protocol_error(v_osCode_boxed_429_, v_details_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_time_expired(uint32_t v_osCode_431_, lean_object* v_details_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(9, 1, 4);
lean_ctor_set(v___x_433_, 0, v_details_432_);
lean_ctor_set_uint32(v___x_433_, sizeof(void*)*1, v_osCode_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object* v_osCode_434_, lean_object* v_details_435_){
_start:
{
uint32_t v_osCode_boxed_436_; lean_object* v_res_437_; 
v_osCode_boxed_436_ = lean_unbox_uint32(v_osCode_434_);
lean_dec(v_osCode_434_);
v_res_437_ = lean_mk_io_error_time_expired(v_osCode_boxed_436_, v_details_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object* v_s_438_){
_start:
{
lean_object* v___x_439_; uint32_t v___x_440_; uint8_t v___y_442_; uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_string_utf8_get(v_s_438_, v___x_439_);
v___x_447_ = 65;
v___x_448_ = lean_uint32_dec_le(v___x_447_, v___x_440_);
if (v___x_448_ == 0)
{
v___y_442_ = v___x_448_;
goto v___jp_441_;
}
else
{
uint32_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 90;
v___x_450_ = lean_uint32_dec_le(v___x_440_, v___x_449_);
v___y_442_ = v___x_450_;
goto v___jp_441_;
}
v___jp_441_:
{
if (v___y_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_string_utf8_set(v_s_438_, v___x_439_, v___x_440_);
return v___x_443_;
}
else
{
uint32_t v___x_444_; uint32_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = 32;
v___x_445_ = lean_uint32_add(v___x_440_, v___x_444_);
v___x_446_ = lean_string_utf8_set(v_s_438_, v___x_439_, v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString(lean_object* v_gist_454_, lean_object* v_fn_455_, uint32_t v_code_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_458_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_454_);
v___x_459_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_460_ = lean_string_append(v___x_458_, v___x_459_);
v___x_461_ = lean_uint32_to_nat(v_code_456_);
v___x_462_ = l_Nat_reprFast(v___x_461_);
v___x_463_ = lean_string_append(v___x_460_, v___x_462_);
lean_dec_ref(v___x_462_);
v___x_464_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
v___x_465_ = lean_string_append(v___x_463_, v___x_464_);
v___x_466_ = lean_string_append(v___x_465_, v_fn_455_);
return v___x_466_;
}
else
{
lean_object* v_val_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_val_467_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v_x_457_, 1);
v___x_468_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_454_);
v___x_469_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_470_ = lean_string_append(v___x_468_, v___x_469_);
v___x_471_ = lean_uint32_to_nat(v_code_456_);
v___x_472_ = l_Nat_reprFast(v___x_471_);
v___x_473_ = lean_string_append(v___x_470_, v___x_472_);
lean_dec_ref(v___x_472_);
v___x_474_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
v___x_476_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_467_);
v___x_477_ = lean_string_append(v___x_475_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
v___x_480_ = lean_string_append(v___x_479_, v_fn_455_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object* v_gist_481_, lean_object* v_fn_482_, lean_object* v_code_483_, lean_object* v_x_484_){
_start:
{
uint32_t v_code_boxed_485_; lean_object* v_res_486_; 
v_code_boxed_485_ = lean_unbox_uint32(v_code_483_);
lean_dec(v_code_483_);
v_res_486_ = l_IO_Error_fopenErrorToString(v_gist_481_, v_fn_482_, v_code_boxed_485_, v_x_484_);
lean_dec_ref(v_fn_482_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString(lean_object* v_gist_488_, uint32_t v_code_489_, lean_object* v_x_490_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_491_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_488_);
v___x_492_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
v___x_494_ = lean_uint32_to_nat(v_code_489_);
v___x_495_ = l_Nat_reprFast(v___x_494_);
v___x_496_ = lean_string_append(v___x_493_, v___x_495_);
lean_dec_ref(v___x_495_);
v___x_497_ = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
v___x_498_ = lean_string_append(v___x_496_, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v_val_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_val_499_ = lean_ctor_get(v_x_490_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v_x_490_, 1);
v___x_500_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_488_);
v___x_501_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
v___x_502_ = lean_string_append(v___x_500_, v___x_501_);
v___x_503_ = lean_uint32_to_nat(v_code_489_);
v___x_504_ = l_Nat_reprFast(v___x_503_);
v___x_505_ = lean_string_append(v___x_502_, v___x_504_);
lean_dec_ref(v___x_504_);
v___x_506_ = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
v___x_507_ = lean_string_append(v___x_505_, v___x_506_);
v___x_508_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_499_);
v___x_509_ = lean_string_append(v___x_507_, v___x_508_);
lean_dec_ref(v___x_508_);
v___x_510_ = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
v___x_511_ = lean_string_append(v___x_509_, v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString___boxed(lean_object* v_gist_512_, lean_object* v_code_513_, lean_object* v_x_514_){
_start:
{
uint32_t v_code_boxed_515_; lean_object* v_res_516_; 
v_code_boxed_515_ = lean_unbox_uint32(v_code_513_);
lean_dec(v_code_513_);
v_res_516_ = l_IO_Error_otherErrorToString(v_gist_512_, v_code_boxed_515_, v_x_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* lean_io_error_to_string(lean_object* v_x_533_){
_start:
{
uint32_t v_code_535_; lean_object* v_details_536_; 
switch(lean_obj_tag(v_x_533_))
{
case 0:
{
lean_object* v_filename_539_; 
v_filename_539_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_filename_539_);
if (lean_obj_tag(v_filename_539_) == 0)
{
uint32_t v_osCode_540_; lean_object* v_details_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_osCode_540_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_541_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_541_);
lean_dec_ref_known(v_x_533_, 2);
v___x_542_ = ((lean_object*)(l_IO_Error_toString___closed__0));
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_details_541_);
v___x_544_ = l_IO_Error_otherErrorToString(v___x_542_, v_osCode_540_, v___x_543_);
return v___x_544_;
}
else
{
uint32_t v_osCode_545_; lean_object* v_details_546_; lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_556_; 
v_osCode_545_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_546_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_546_);
lean_dec_ref_known(v_x_533_, 2);
v_val_547_ = lean_ctor_get(v_filename_539_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_filename_539_);
if (v_isSharedCheck_556_ == 0)
{
v___x_549_ = v_filename_539_;
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v_filename_539_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = ((lean_object*)(l_IO_Error_toString___closed__0));
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_details_546_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_details_546_);
v___x_553_ = v_reuseFailAlloc_555_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; 
v___x_554_ = l_IO_Error_fopenErrorToString(v___x_551_, v_val_547_, v_osCode_545_, v___x_553_);
lean_dec(v_val_547_);
return v___x_554_;
}
}
}
}
case 1:
{
uint32_t v_osCode_557_; lean_object* v_details_558_; 
v_osCode_557_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
v_details_558_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_details_558_);
lean_dec_ref_known(v_x_533_, 1);
v_code_535_ = v_osCode_557_;
v_details_536_ = v_details_558_;
goto v___jp_534_;
}
case 2:
{
uint32_t v_osCode_559_; lean_object* v_details_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_osCode_559_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
v_details_560_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_details_560_);
lean_dec_ref_known(v_x_533_, 1);
v___x_561_ = ((lean_object*)(l_IO_Error_toString___closed__1));
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v_details_560_);
v___x_563_ = l_IO_Error_otherErrorToString(v___x_561_, v_osCode_559_, v___x_562_);
return v___x_563_;
}
case 3:
{
uint32_t v_osCode_564_; lean_object* v_details_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_osCode_564_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
v_details_565_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_details_565_);
lean_dec_ref_known(v_x_533_, 1);
v___x_566_ = ((lean_object*)(l_IO_Error_toString___closed__2));
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v_details_565_);
v___x_568_ = l_IO_Error_otherErrorToString(v___x_566_, v_osCode_564_, v___x_567_);
return v___x_568_;
}
case 4:
{
uint32_t v_osCode_569_; lean_object* v_details_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_osCode_569_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
v_details_570_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_details_570_);
lean_dec_ref_known(v_x_533_, 1);
v___x_571_ = ((lean_object*)(l_IO_Error_toString___closed__3));
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_details_570_);
v___x_573_ = l_IO_Error_otherErrorToString(v___x_571_, v_osCode_569_, v___x_572_);
return v___x_573_;
}
case 5:
{
uint32_t v_osCode_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_osCode_574_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
lean_dec_ref_known(v_x_533_, 1);
v___x_575_ = ((lean_object*)(l_IO_Error_toString___closed__4));
v___x_576_ = lean_box(0);
v___x_577_ = l_IO_Error_otherErrorToString(v___x_575_, v_osCode_574_, v___x_576_);
return v___x_577_;
}
case 6:
{
uint32_t v_osCode_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_osCode_578_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
lean_dec_ref_known(v_x_533_, 1);
v___x_579_ = ((lean_object*)(l_IO_Error_toString___closed__5));
v___x_580_ = lean_box(0);
v___x_581_ = l_IO_Error_otherErrorToString(v___x_579_, v_osCode_578_, v___x_580_);
return v___x_581_;
}
case 7:
{
uint32_t v_osCode_582_; lean_object* v_details_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_osCode_582_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
v_details_583_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_details_583_);
lean_dec_ref_known(v_x_533_, 1);
v___x_584_ = ((lean_object*)(l_IO_Error_toString___closed__6));
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_details_583_);
v___x_586_ = l_IO_Error_otherErrorToString(v___x_584_, v_osCode_582_, v___x_585_);
return v___x_586_;
}
case 8:
{
uint32_t v_osCode_587_; lean_object* v_details_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_osCode_587_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
v_details_588_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_details_588_);
lean_dec_ref_known(v_x_533_, 1);
v___x_589_ = ((lean_object*)(l_IO_Error_toString___closed__7));
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v_details_588_);
v___x_591_ = l_IO_Error_otherErrorToString(v___x_589_, v_osCode_587_, v___x_590_);
return v___x_591_;
}
case 9:
{
uint32_t v_osCode_592_; lean_object* v_details_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_osCode_592_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*1);
v_details_593_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_details_593_);
lean_dec_ref_known(v_x_533_, 1);
v___x_594_ = ((lean_object*)(l_IO_Error_toString___closed__8));
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v_details_593_);
v___x_596_ = l_IO_Error_otherErrorToString(v___x_594_, v_osCode_592_, v___x_595_);
return v___x_596_;
}
case 10:
{
lean_object* v_filename_597_; uint32_t v_osCode_598_; lean_object* v_details_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_filename_597_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_filename_597_);
v_osCode_598_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_599_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_599_);
lean_dec_ref_known(v_x_533_, 2);
v___x_600_ = ((lean_object*)(l_IO_Error_toString___closed__9));
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_details_599_);
v___x_602_ = l_IO_Error_fopenErrorToString(v___x_600_, v_filename_597_, v_osCode_598_, v___x_601_);
lean_dec_ref(v_filename_597_);
return v___x_602_;
}
case 11:
{
lean_object* v_filename_603_; uint32_t v_osCode_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_filename_603_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_filename_603_);
v_osCode_604_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
lean_dec_ref_known(v_x_533_, 2);
v___x_605_ = ((lean_object*)(l_IO_Error_toString___closed__10));
v___x_606_ = lean_box(0);
v___x_607_ = l_IO_Error_fopenErrorToString(v___x_605_, v_filename_603_, v_osCode_604_, v___x_606_);
lean_dec_ref(v_filename_603_);
return v___x_607_;
}
case 12:
{
lean_object* v_filename_608_; 
v_filename_608_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_filename_608_);
if (lean_obj_tag(v_filename_608_) == 0)
{
uint32_t v_osCode_609_; lean_object* v_details_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_osCode_609_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_610_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_610_);
lean_dec_ref_known(v_x_533_, 2);
v___x_611_ = ((lean_object*)(l_IO_Error_toString___closed__11));
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v_details_610_);
v___x_613_ = l_IO_Error_otherErrorToString(v___x_611_, v_osCode_609_, v___x_612_);
return v___x_613_;
}
else
{
uint32_t v_osCode_614_; lean_object* v_details_615_; lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_625_; 
v_osCode_614_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_615_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_615_);
lean_dec_ref_known(v_x_533_, 2);
v_val_616_ = lean_ctor_get(v_filename_608_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v_filename_608_);
if (v_isSharedCheck_625_ == 0)
{
v___x_618_ = v_filename_608_;
v_isShared_619_ = v_isSharedCheck_625_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_dec(v_filename_608_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_625_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = ((lean_object*)(l_IO_Error_toString___closed__11));
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_details_615_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_details_615_);
v___x_622_ = v_reuseFailAlloc_624_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; 
v___x_623_ = l_IO_Error_fopenErrorToString(v___x_620_, v_val_616_, v_osCode_614_, v___x_622_);
lean_dec(v_val_616_);
return v___x_623_;
}
}
}
}
case 13:
{
lean_object* v_filename_626_; 
v_filename_626_ = lean_ctor_get(v_x_533_, 0);
if (lean_obj_tag(v_filename_626_) == 0)
{
uint32_t v_osCode_627_; lean_object* v_details_628_; 
v_osCode_627_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_628_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_628_);
lean_dec_ref_known(v_x_533_, 2);
v_code_535_ = v_osCode_627_;
v_details_536_ = v_details_628_;
goto v___jp_534_;
}
else
{
uint32_t v_osCode_629_; lean_object* v_details_630_; lean_object* v_val_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_inc_ref(v_filename_626_);
v_osCode_629_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_630_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_630_);
lean_dec_ref_known(v_x_533_, 2);
v_val_631_ = lean_ctor_get(v_filename_626_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v_filename_626_, 1);
v___x_632_ = lean_box(0);
v___x_633_ = l_IO_Error_fopenErrorToString(v_details_630_, v_val_631_, v_osCode_629_, v___x_632_);
lean_dec(v_val_631_);
return v___x_633_;
}
}
case 14:
{
lean_object* v_filename_634_; 
v_filename_634_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_filename_634_);
if (lean_obj_tag(v_filename_634_) == 0)
{
uint32_t v_osCode_635_; lean_object* v_details_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_osCode_635_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_636_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_636_);
lean_dec_ref_known(v_x_533_, 2);
v___x_637_ = ((lean_object*)(l_IO_Error_toString___closed__12));
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_details_636_);
v___x_639_ = l_IO_Error_otherErrorToString(v___x_637_, v_osCode_635_, v___x_638_);
return v___x_639_;
}
else
{
uint32_t v_osCode_640_; lean_object* v_details_641_; lean_object* v_val_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_651_; 
v_osCode_640_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_641_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_641_);
lean_dec_ref_known(v_x_533_, 2);
v_val_642_ = lean_ctor_get(v_filename_634_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_filename_634_);
if (v_isSharedCheck_651_ == 0)
{
v___x_644_ = v_filename_634_;
v_isShared_645_ = v_isSharedCheck_651_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_val_642_);
lean_dec(v_filename_634_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_651_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = ((lean_object*)(l_IO_Error_toString___closed__12));
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_details_641_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_details_641_);
v___x_648_ = v_reuseFailAlloc_650_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; 
v___x_649_ = l_IO_Error_fopenErrorToString(v___x_646_, v_val_642_, v_osCode_640_, v___x_648_);
lean_dec(v_val_642_);
return v___x_649_;
}
}
}
}
case 15:
{
lean_object* v_filename_652_; 
v_filename_652_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_filename_652_);
if (lean_obj_tag(v_filename_652_) == 0)
{
uint32_t v_osCode_653_; lean_object* v_details_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_osCode_653_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_654_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_654_);
lean_dec_ref_known(v_x_533_, 2);
v___x_655_ = ((lean_object*)(l_IO_Error_toString___closed__13));
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v_details_654_);
v___x_657_ = l_IO_Error_otherErrorToString(v___x_655_, v_osCode_653_, v___x_656_);
return v___x_657_;
}
else
{
uint32_t v_osCode_658_; lean_object* v_details_659_; lean_object* v_val_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_669_; 
v_osCode_658_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_659_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_659_);
lean_dec_ref_known(v_x_533_, 2);
v_val_660_ = lean_ctor_get(v_filename_652_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v_filename_652_);
if (v_isSharedCheck_669_ == 0)
{
v___x_662_ = v_filename_652_;
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_val_660_);
lean_dec(v_filename_652_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = ((lean_object*)(l_IO_Error_toString___closed__13));
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v_details_659_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_details_659_);
v___x_666_ = v_reuseFailAlloc_668_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; 
v___x_667_ = l_IO_Error_fopenErrorToString(v___x_664_, v_val_660_, v_osCode_658_, v___x_666_);
lean_dec(v_val_660_);
return v___x_667_;
}
}
}
}
case 16:
{
lean_object* v_filename_670_; 
v_filename_670_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_filename_670_);
if (lean_obj_tag(v_filename_670_) == 0)
{
uint32_t v_osCode_671_; lean_object* v_details_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_osCode_671_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_672_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_672_);
lean_dec_ref_known(v_x_533_, 2);
v___x_673_ = ((lean_object*)(l_IO_Error_toString___closed__14));
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_details_672_);
v___x_675_ = l_IO_Error_otherErrorToString(v___x_673_, v_osCode_671_, v___x_674_);
return v___x_675_;
}
else
{
uint32_t v_osCode_676_; lean_object* v_details_677_; lean_object* v_val_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_687_; 
v_osCode_676_ = lean_ctor_get_uint32(v_x_533_, sizeof(void*)*2);
v_details_677_ = lean_ctor_get(v_x_533_, 1);
lean_inc_ref(v_details_677_);
lean_dec_ref_known(v_x_533_, 2);
v_val_678_ = lean_ctor_get(v_filename_670_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_filename_670_);
if (v_isSharedCheck_687_ == 0)
{
v___x_680_ = v_filename_670_;
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_val_678_);
lean_dec(v_filename_670_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = ((lean_object*)(l_IO_Error_toString___closed__14));
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v_details_677_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_details_677_);
v___x_684_ = v_reuseFailAlloc_686_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; 
v___x_685_ = l_IO_Error_fopenErrorToString(v___x_682_, v_val_678_, v_osCode_676_, v___x_684_);
lean_dec(v_val_678_);
return v___x_685_;
}
}
}
}
case 17:
{
lean_object* v___x_688_; 
v___x_688_ = ((lean_object*)(l_IO_Error_toString___closed__15));
return v___x_688_;
}
default: 
{
lean_object* v_msg_689_; 
v_msg_689_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_msg_689_);
lean_dec_ref_known(v_x_533_, 1);
return v_msg_689_;
}
}
v___jp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_box(0);
v___x_538_ = l_IO_Error_otherErrorToString(v_details_536_, v_code_535_, v___x_537_);
return v___x_538_;
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
