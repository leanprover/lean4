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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object*);
static const lean_string_object l_IO_Error_fopenErrorToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " (error code: "};
static const lean_object* l_IO_Error_fopenErrorToString___closed__0 = (const lean_object*)&l_IO_Error_fopenErrorToString___closed__0_value;
static const lean_string_object l_IO_Error_fopenErrorToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ")\n  file: "};
static const lean_object* l_IO_Error_fopenErrorToString___closed__1 = (const lean_object*)&l_IO_Error_fopenErrorToString___closed__1_value;
static const lean_string_object l_IO_Error_fopenErrorToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_IO_Error_fopenErrorToString___closed__2 = (const lean_object*)&l_IO_Error_fopenErrorToString___closed__2_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
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
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(10u);
return x_12;
}
case 11:
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(11u);
return x_13;
}
case 12:
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(12u);
return x_14;
}
case 13:
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(13u);
return x_15;
}
case 14:
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(14u);
return x_16;
}
case 15:
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(15u);
return x_17;
}
case 16:
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(16u);
return x_18;
}
case 17:
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(17u);
return x_19;
}
default: 
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(18u);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Error_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_box_uint32(x_4);
x_7 = lean_apply_3(x_2, x_3, x_6, x_5);
return x_7;
}
case 10:
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = lean_box_uint32(x_9);
x_12 = lean_apply_3(x_2, x_8, x_11, x_10);
return x_12;
}
case 11:
{
lean_object* x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_box_uint32(x_14);
x_17 = lean_apply_3(x_2, x_13, x_16, x_15);
return x_17;
}
case 12:
{
lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_box_uint32(x_19);
x_22 = lean_apply_3(x_2, x_18, x_21, x_20);
return x_22;
}
case 13:
{
lean_object* x_23; uint32_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_25 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_1);
x_26 = lean_box_uint32(x_24);
x_27 = lean_apply_3(x_2, x_23, x_26, x_25);
return x_27;
}
case 14:
{
lean_object* x_28; uint32_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_30 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_1);
x_31 = lean_box_uint32(x_29);
x_32 = lean_apply_3(x_2, x_28, x_31, x_30);
return x_32;
}
case 15:
{
lean_object* x_33; uint32_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_35 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_35);
lean_dec_ref(x_1);
x_36 = lean_box_uint32(x_34);
x_37 = lean_apply_3(x_2, x_33, x_36, x_35);
return x_37;
}
case 16:
{
lean_object* x_38; uint32_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_40 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_40);
lean_dec_ref(x_1);
x_41 = lean_box_uint32(x_39);
x_42 = lean_apply_3(x_2, x_38, x_41, x_40);
return x_42;
}
case 17:
{
return x_2;
}
case 18:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_43);
lean_dec_ref(x_1);
x_44 = lean_apply_1(x_2, x_43);
return x_44;
}
default: 
{
uint32_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_46 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_46);
lean_dec(x_1);
x_47 = lean_box_uint32(x_45);
x_48 = lean_apply_2(x_2, x_47, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_Error_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Error_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_Error_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Error_alreadyExists_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_alreadyExists_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherError_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherError_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceBusy_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceBusy_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceVanished_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceVanished_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsupportedOperation_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsupportedOperation_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_hardwareFault_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_hardwareFault_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsatisfiedConstraints_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unsatisfiedConstraints_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_illegalOperation_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_illegalOperation_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_protocolError_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_protocolError_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_timeExpired_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_timeExpired_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_interrupted_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_interrupted_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noFileOrDirectory_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noFileOrDirectory_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_invalidArgument_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_invalidArgument_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_permissionDenied_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_permissionDenied_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceExhausted_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_resourceExhausted_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_inappropriateType_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_inappropriateType_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noSuchThing_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_noSuchThing_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unexpectedEof_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_unexpectedEof_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_userError_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_userError_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_user_error(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set_uint32(x_5, sizeof(void*)*2, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExistsFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_already_exists_file(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_eof(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(17);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set_uint32(x_5, sizeof(void*)*2, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_inappropriate_type_file(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_interrupted(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(10, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInterrupted___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_interrupted(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set_uint32(x_5, sizeof(void*)*2, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_invalid_argument_file(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_file_or_directory(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_no_file_or_directory(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set_uint32(x_5, sizeof(void*)*2, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_no_such_thing_file(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set_uint32(x_5, sizeof(void*)*2, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_permission_denied_file(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set_uint32(x_5, sizeof(void*)*2, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_resource_exhausted_file(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_unsupported_operation(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(4, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_unsupported_operation(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_exhausted(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(14, 2, 4);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_resource_exhausted(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_already_exists(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_already_exists(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_inappropriate_type(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(15, 2, 4);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_inappropriate_type(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_no_such_thing(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(16, 2, 4);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkNoSuchThing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_no_such_thing(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_vanished(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(3, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_resource_vanished(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_resource_busy(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_resource_busy(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_invalid_argument(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(12, 2, 4);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_invalid_argument(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_other_error(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkOtherError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_other_error(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_permission_denied(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_permission_denied(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_hardware_fault(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(5, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_hardware_fault(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_unsatisfied_constraints(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_illegal_operation(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(7, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_illegal_operation(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_protocol_error(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(8, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkProtocolError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_protocol_error(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_io_error_time_expired(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(9, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_time_expired(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 65;
x_5 = lean_uint32_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_string_utf8_set(x_1, x_2, x_3);
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = 90;
x_8 = lean_uint32_dec_le(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_set(x_1, x_2, x_3);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; lean_object* x_12; 
x_10 = 32;
x_11 = lean_uint32_add(x_3, x_10);
x_12 = lean_string_utf8_set(x_1, x_2, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(x_1);
x_6 = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_uint32_to_nat(x_3);
x_9 = l_Nat_reprFast(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec_ref(x_4);
x_15 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(x_1);
x_16 = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_uint32_to_nat(x_3);
x_19 = l_Nat_reprFast(x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
x_22 = lean_string_append(x_20, x_21);
x_23 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(x_14);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__1));
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_2);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l_IO_Error_fopenErrorToString(x_1, x_2, x_5, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(x_1);
x_5 = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_uint32_to_nat(x_2);
x_8 = l_Nat_reprFast(x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(x_1);
x_14 = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__0));
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_uint32_to_nat(x_2);
x_17 = l_Nat_reprFast(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_IO_Error_fopenErrorToString___closed__2));
x_20 = lean_string_append(x_18, x_19);
x_21 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(x_12);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l_IO_Error_otherErrorToString___closed__0));
x_24 = lean_string_append(x_22, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_IO_Error_otherErrorToString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_IO_Error_otherErrorToString(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_io_error_to_string(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_IO_Error_toString___closed__0));
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = l_IO_Error_otherErrorToString(x_10, x_8, x_11);
return x_12;
}
else
{
uint32_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_13 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_7, 0);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
x_16 = x_7;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; lean_object* x_19; 
x_18 = ((lean_object*)(l_IO_Error_toString___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_14);
x_19 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_14);
x_19 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_20; 
x_20 = l_IO_Error_fopenErrorToString(x_18, x_15, x_13, x_19);
lean_dec(x_15);
return x_20;
}
}
}
}
case 1:
{
uint32_t x_25; lean_object* x_26; 
x_25 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_2 = x_25;
x_3 = x_26;
goto block_6;
}
case 2:
{
uint32_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_28 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = ((lean_object*)(l_IO_Error_toString___closed__1));
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = l_IO_Error_otherErrorToString(x_29, x_27, x_30);
return x_31;
}
case 3:
{
uint32_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_33 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_33);
lean_dec_ref(x_1);
x_34 = ((lean_object*)(l_IO_Error_toString___closed__2));
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_36 = l_IO_Error_otherErrorToString(x_34, x_32, x_35);
return x_36;
}
case 4:
{
uint32_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_38 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_38);
lean_dec_ref(x_1);
x_39 = ((lean_object*)(l_IO_Error_toString___closed__3));
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = l_IO_Error_otherErrorToString(x_39, x_37, x_40);
return x_41;
}
case 5:
{
uint32_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
lean_dec_ref(x_1);
x_43 = ((lean_object*)(l_IO_Error_toString___closed__4));
x_44 = lean_box(0);
x_45 = l_IO_Error_otherErrorToString(x_43, x_42, x_44);
return x_45;
}
case 6:
{
uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
lean_dec_ref(x_1);
x_47 = ((lean_object*)(l_IO_Error_toString___closed__5));
x_48 = lean_box(0);
x_49 = l_IO_Error_otherErrorToString(x_47, x_46, x_48);
return x_49;
}
case 7:
{
uint32_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_51 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_51);
lean_dec_ref(x_1);
x_52 = ((lean_object*)(l_IO_Error_toString___closed__6));
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_51);
x_54 = l_IO_Error_otherErrorToString(x_52, x_50, x_53);
return x_54;
}
case 8:
{
uint32_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_56 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_56);
lean_dec_ref(x_1);
x_57 = ((lean_object*)(l_IO_Error_toString___closed__7));
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = l_IO_Error_otherErrorToString(x_57, x_55, x_58);
return x_59;
}
case 9:
{
uint32_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_61 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_61);
lean_dec_ref(x_1);
x_62 = ((lean_object*)(l_IO_Error_toString___closed__8));
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_61);
x_64 = l_IO_Error_otherErrorToString(x_62, x_60, x_63);
return x_64;
}
case 10:
{
lean_object* x_65; uint32_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_67 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_1);
x_68 = ((lean_object*)(l_IO_Error_toString___closed__9));
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = l_IO_Error_fopenErrorToString(x_68, x_65, x_66, x_69);
lean_dec_ref(x_65);
return x_70;
}
case 11:
{
lean_object* x_71; uint32_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_73 = ((lean_object*)(l_IO_Error_toString___closed__10));
x_74 = lean_box(0);
x_75 = l_IO_Error_fopenErrorToString(x_73, x_71, x_72, x_74);
lean_dec_ref(x_71);
return x_75;
}
case 12:
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint32_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_78 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_78);
lean_dec_ref(x_1);
x_79 = ((lean_object*)(l_IO_Error_toString___closed__11));
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_78);
x_81 = l_IO_Error_otherErrorToString(x_79, x_77, x_80);
return x_81;
}
else
{
uint32_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_93; 
x_82 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_83 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_83);
lean_dec_ref(x_1);
x_84 = lean_ctor_get(x_76, 0);
x_93 = !lean_is_exclusive(x_76);
if (x_93 == 0)
{
x_85 = x_76;
x_86 = x_93;
goto block_92;
}
else
{
lean_inc(x_84);
lean_dec(x_76);
x_85 = lean_box(0);
x_86 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_87; lean_object* x_88; 
x_87 = ((lean_object*)(l_IO_Error_toString___closed__11));
if (x_86 == 0)
{
lean_ctor_set(x_85, 0, x_83);
x_88 = x_85;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_83);
x_88 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_89; 
x_89 = l_IO_Error_fopenErrorToString(x_87, x_84, x_82, x_88);
lean_dec(x_84);
return x_89;
}
}
}
}
case 13:
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_94) == 0)
{
uint32_t x_95; lean_object* x_96; 
x_95 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_96 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_96);
lean_dec_ref(x_1);
x_2 = x_95;
x_3 = x_96;
goto block_6;
}
else
{
uint32_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_inc_ref(x_94);
x_97 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_98 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_98);
lean_dec_ref(x_1);
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
lean_dec_ref(x_94);
x_100 = lean_box(0);
x_101 = l_IO_Error_fopenErrorToString(x_98, x_99, x_97, x_100);
lean_dec(x_99);
return x_101;
}
}
case 14:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
uint32_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_104 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_104);
lean_dec_ref(x_1);
x_105 = ((lean_object*)(l_IO_Error_toString___closed__12));
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_104);
x_107 = l_IO_Error_otherErrorToString(x_105, x_103, x_106);
return x_107;
}
else
{
uint32_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_119; 
x_108 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_109 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_109);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_102, 0);
x_119 = !lean_is_exclusive(x_102);
if (x_119 == 0)
{
x_111 = x_102;
x_112 = x_119;
goto block_118;
}
else
{
lean_inc(x_110);
lean_dec(x_102);
x_111 = lean_box(0);
x_112 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_113; lean_object* x_114; 
x_113 = ((lean_object*)(l_IO_Error_toString___closed__12));
if (x_112 == 0)
{
lean_ctor_set(x_111, 0, x_109);
x_114 = x_111;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_109);
x_114 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_115; 
x_115 = l_IO_Error_fopenErrorToString(x_113, x_110, x_108, x_114);
lean_dec(x_110);
return x_115;
}
}
}
}
case 15:
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
uint32_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_122 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_122);
lean_dec_ref(x_1);
x_123 = ((lean_object*)(l_IO_Error_toString___closed__13));
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_122);
x_125 = l_IO_Error_otherErrorToString(x_123, x_121, x_124);
return x_125;
}
else
{
uint32_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_137; 
x_126 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_127 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_127);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_120, 0);
x_137 = !lean_is_exclusive(x_120);
if (x_137 == 0)
{
x_129 = x_120;
x_130 = x_137;
goto block_136;
}
else
{
lean_inc(x_128);
lean_dec(x_120);
x_129 = lean_box(0);
x_130 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_131; lean_object* x_132; 
x_131 = ((lean_object*)(l_IO_Error_toString___closed__13));
if (x_130 == 0)
{
lean_ctor_set(x_129, 0, x_127);
x_132 = x_129;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_127);
x_132 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_133; 
x_133 = l_IO_Error_fopenErrorToString(x_131, x_128, x_126, x_132);
lean_dec(x_128);
return x_133;
}
}
}
}
case 16:
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
uint32_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_140 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_140);
lean_dec_ref(x_1);
x_141 = ((lean_object*)(l_IO_Error_toString___closed__14));
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_140);
x_143 = l_IO_Error_otherErrorToString(x_141, x_139, x_142);
return x_143;
}
else
{
uint32_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_155; 
x_144 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_145 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_145);
lean_dec_ref(x_1);
x_146 = lean_ctor_get(x_138, 0);
x_155 = !lean_is_exclusive(x_138);
if (x_155 == 0)
{
x_147 = x_138;
x_148 = x_155;
goto block_154;
}
else
{
lean_inc(x_146);
lean_dec(x_138);
x_147 = lean_box(0);
x_148 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_149; lean_object* x_150; 
x_149 = ((lean_object*)(l_IO_Error_toString___closed__14));
if (x_148 == 0)
{
lean_ctor_set(x_147, 0, x_145);
x_150 = x_147;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_145);
x_150 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_151; 
x_151 = l_IO_Error_fopenErrorToString(x_149, x_146, x_144, x_150);
lean_dec(x_146);
return x_151;
}
}
}
}
case 17:
{
lean_object* x_156; 
x_156 = ((lean_object*)(l_IO_Error_toString___closed__15));
return x_156;
}
default: 
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_157);
lean_dec_ref(x_1);
return x_157;
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_IO_Error_otherErrorToString(x_3, x_2, x_4);
return x_5;
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
res = runtime_initialize_Init_Data_ToString_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin)
;
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
res = initialize_Init_Data_ToString_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IOError(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_IOError(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_IOError(builtin);
}
#ifdef __cplusplus
}
#endif
