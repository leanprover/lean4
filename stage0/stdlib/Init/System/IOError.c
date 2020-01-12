// Lean compiler output
// Module: Init.System.IOError
// Imports: Init.Core Init.Data.UInt Init.Data.ToString Init.Data.String.Basic
#include "runtime/lean.h"
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
lean_object* lean_mk_io_error_invalid_argument(uint32_t, lean_object*);
lean_object* lean_mk_io_error_invalid_argument_file(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_toString___closed__12;
lean_object* l_IO_Error_toString___closed__11;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_Error_mkOtherError___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_error_permission_denied(uint32_t, lean_object*);
lean_object* lean_mk_io_error_no_file_or_directory(lean_object*, uint32_t, lean_object*);
lean_object* l_String_modify(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_toString___closed__3;
lean_object* l_IO_Error_fopenErrorToString___closed__1;
lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_otherErrorToString(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkNoSuchThing___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_fopenErrorToString(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* mk_io_user_error(lean_object*);
lean_object* l_IO_Error_Inhabited;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_IO_Error_toString___closed__7;
lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_HasToString;
lean_object* lean_mk_io_error_already_exists(uint32_t, lean_object*);
lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_toString___closed__8;
lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_otherErrorToString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_error_resource_exhausted(uint32_t, lean_object*);
lean_object* l_IO_Error_toString___closed__4;
lean_object* l___private_Init_System_IOError_1__downCaseFirst___closed__1;
lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_mkInterrupted___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_toString___closed__9;
lean_object* lean_mk_io_error_inappropriate_type_file(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_toString___closed__2;
lean_object* lean_mk_io_error_hardware_fault(uint32_t, lean_object*);
lean_object* l_Char_toLower___boxed(lean_object*);
lean_object* l_IO_Error_toString___closed__1;
lean_object* l_IO_Error_mkProtocolError___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* lean_mk_io_error_no_such_thing_file(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* lean_mk_io_error_other_error(uint32_t, lean_object*);
lean_object* l_IO_Error_Inhabited___closed__1;
lean_object* lean_mk_io_error_resource_exhausted_file(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_permission_denied_file(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_error_time_expired(uint32_t, lean_object*);
lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_error_unsupported_operation(uint32_t, lean_object*);
lean_object* l_IO_Error_toString___closed__14;
lean_object* lean_mk_io_error_protocol_error(uint32_t, lean_object*);
lean_object* lean_mk_io_error_illegal_operation(uint32_t, lean_object*);
lean_object* lean_mk_io_error_resource_vanished(uint32_t, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_IO_Error_toString___closed__15;
lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t, lean_object*);
lean_object* l_IO_Error_toString___closed__5;
lean_object* lean_mk_io_error_resource_busy(uint32_t, lean_object*);
lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_System_IOError_1__downCaseFirst(lean_object*);
lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_toString___closed__16;
lean_object* l_IO_Error_HasToString___closed__1;
lean_object* l_IO_Error_fopenErrorToString___closed__2;
lean_object* l_IO_Error_toString___closed__10;
lean_object* lean_mk_io_error_no_such_thing(uint32_t, lean_object*);
lean_object* lean_mk_io_error_inappropriate_type(uint32_t, lean_object*);
lean_object* lean_mk_io_error_eof;
lean_object* l_IO_Error_toString___closed__13;
lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_IO_Error_toString___closed__6;
lean_object* lean_mk_io_error_interrupted(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object*, lean_object*);
lean_object* mk_io_user_error(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_lean_mk_io_error_eof() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(17);
return x_1;
}
}
lean_object* lean_mk_io_error_inappropriate_type_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_inappropriate_type_file(x_1, x_4, x_3);
return x_5;
}
}
lean_object* lean_mk_io_error_interrupted(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* l_IO_Error_mkInterrupted___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_interrupted(x_1, x_4, x_3);
return x_5;
}
}
lean_object* lean_mk_io_error_invalid_argument_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_invalid_argument_file(x_1, x_4, x_3);
return x_5;
}
}
lean_object* lean_mk_io_error_no_file_or_directory(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_no_file_or_directory(x_1, x_4, x_3);
return x_5;
}
}
lean_object* lean_mk_io_error_no_such_thing_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_no_such_thing_file(x_1, x_4, x_3);
return x_5;
}
}
lean_object* lean_mk_io_error_permission_denied_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_permission_denied_file(x_1, x_4, x_3);
return x_5;
}
}
lean_object* lean_mk_io_error_resource_exhausted_file(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_mk_io_error_resource_exhausted_file(x_1, x_4, x_3);
return x_5;
}
}
lean_object* lean_mk_io_error_unsupported_operation(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(4, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_unsupported_operation(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_resource_exhausted(uint32_t x_1, lean_object* x_2) {
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
lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_resource_exhausted(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_already_exists(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_already_exists(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_inappropriate_type(uint32_t x_1, lean_object* x_2) {
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
lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_inappropriate_type(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_no_such_thing(uint32_t x_1, lean_object* x_2) {
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
lean_object* l_IO_Error_mkNoSuchThing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_no_such_thing(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_resource_vanished(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(3, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_resource_vanished(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_resource_busy(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_resource_busy(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_invalid_argument(uint32_t x_1, lean_object* x_2) {
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
lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_invalid_argument(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_other_error(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkOtherError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_other_error(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_permission_denied(uint32_t x_1, lean_object* x_2) {
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
lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_permission_denied(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_hardware_fault(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(5, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_hardware_fault(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_unsatisfied_constraints(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_illegal_operation(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(7, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_illegal_operation(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_protocol_error(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(8, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkProtocolError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_protocol_error(x_3, x_2);
return x_4;
}
}
lean_object* lean_mk_io_error_time_expired(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(9, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_io_error_time_expired(x_3, x_2);
return x_4;
}
}
lean_object* _init_l___private_Init_System_IOError_1__downCaseFirst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_toLower___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Init_System_IOError_1__downCaseFirst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_System_IOError_1__downCaseFirst___closed__1;
x_4 = l_String_modify(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_IO_Error_fopenErrorToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (error code: ");
return x_1;
}
}
lean_object* _init_l_IO_Error_fopenErrorToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")\n  file: ");
return x_1;
}
}
lean_object* l_IO_Error_fopenErrorToString(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_IO_Error_fopenErrorToString___closed__1;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_uint32_to_nat(x_3);
x_8 = l_Nat_repr(x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec(x_8);
x_10 = l_IO_Error_fopenErrorToString___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_IO_Error_fopenErrorToString___closed__1;
x_15 = lean_string_append(x_1, x_14);
x_16 = lean_uint32_to_nat(x_3);
x_17 = l_Nat_repr(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
x_19 = l_List_reprAux___main___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Init_System_IOError_1__downCaseFirst___closed__1;
x_23 = l_String_modify(x_13, x_21, x_22);
x_24 = lean_string_append(x_20, x_23);
lean_dec(x_23);
x_25 = l_IO_Error_fopenErrorToString___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_2);
return x_27;
}
}
}
lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l_IO_Error_fopenErrorToString(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_IO_Error_otherErrorToString(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_IO_Error_fopenErrorToString___closed__1;
x_5 = lean_string_append(x_1, x_4);
x_6 = lean_uint32_to_nat(x_2);
x_7 = l_Nat_repr(x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec(x_7);
x_9 = l_Option_HasRepr___rarg___closed__3;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_IO_Error_fopenErrorToString___closed__1;
x_13 = lean_string_append(x_1, x_12);
x_14 = lean_uint32_to_nat(x_2);
x_15 = l_Nat_repr(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = l_List_reprAux___main___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Init_System_IOError_1__downCaseFirst___closed__1;
x_21 = l_String_modify(x_11, x_19, x_20);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = l_Option_HasRepr___rarg___closed__3;
x_24 = lean_string_append(x_22, x_23);
return x_24;
}
}
}
lean_object* l_IO_Error_otherErrorToString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_IO_Error_otherErrorToString(x_1, x_4, x_3);
return x_5;
}
}
lean_object* _init_l_IO_Error_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Already exists");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Resource busy");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Resource vanished");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unsupported operation");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Hardware fault");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Directory not empty");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Illegal operation");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Protocol error");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Time expired");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Interrupted system call");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("No such file or directory");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Invalid argument");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Resource exhausted");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Inappropriate type");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("No such thing");
return x_1;
}
}
lean_object* _init_l_IO_Error_toString___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("End of file");
return x_1;
}
}
lean_object* lean_io_error_to_string(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_IO_Error_toString___closed__1;
x_6 = l_IO_Error_otherErrorToString(x_5, x_2, x_4);
return x_6;
}
case 1:
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = l_IO_Error_otherErrorToString(x_8, x_7, x_9);
return x_10;
}
case 2:
{
uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_IO_Error_toString___closed__2;
x_15 = l_IO_Error_otherErrorToString(x_14, x_11, x_13);
return x_15;
}
case 3:
{
uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_IO_Error_toString___closed__3;
x_20 = l_IO_Error_otherErrorToString(x_19, x_16, x_18);
return x_20;
}
case 4:
{
uint32_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_IO_Error_toString___closed__4;
x_25 = l_IO_Error_otherErrorToString(x_24, x_21, x_23);
return x_25;
}
case 5:
{
uint32_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = l_IO_Error_toString___closed__5;
x_29 = l_IO_Error_otherErrorToString(x_28, x_26, x_27);
return x_29;
}
case 6:
{
uint32_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = l_IO_Error_toString___closed__6;
x_33 = l_IO_Error_otherErrorToString(x_32, x_30, x_31);
return x_33;
}
case 7:
{
uint32_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_IO_Error_toString___closed__7;
x_38 = l_IO_Error_otherErrorToString(x_37, x_34, x_36);
return x_38;
}
case 8:
{
uint32_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_IO_Error_toString___closed__8;
x_43 = l_IO_Error_otherErrorToString(x_42, x_39, x_41);
return x_43;
}
case 9:
{
uint32_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_IO_Error_toString___closed__9;
x_48 = l_IO_Error_otherErrorToString(x_47, x_44, x_46);
return x_48;
}
case 10:
{
lean_object* x_49; uint32_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_IO_Error_toString___closed__10;
x_54 = l_IO_Error_fopenErrorToString(x_53, x_49, x_50, x_52);
lean_dec(x_49);
return x_54;
}
case 11:
{
lean_object* x_55; uint32_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = l_IO_Error_toString___closed__11;
x_59 = l_IO_Error_fopenErrorToString(x_58, x_55, x_56, x_57);
lean_dec(x_55);
return x_59;
}
case 12:
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint32_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_dec(x_1);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_IO_Error_toString___closed__12;
x_65 = l_IO_Error_otherErrorToString(x_64, x_61, x_63);
return x_65;
}
else
{
uint32_t x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_60, 0);
lean_ctor_set(x_60, 0, x_67);
x_70 = l_IO_Error_toString___closed__12;
x_71 = l_IO_Error_fopenErrorToString(x_70, x_69, x_66, x_60);
lean_dec(x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_60, 0);
lean_inc(x_72);
lean_dec(x_60);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_67);
x_74 = l_IO_Error_toString___closed__12;
x_75 = l_IO_Error_fopenErrorToString(x_74, x_72, x_66, x_73);
lean_dec(x_72);
return x_75;
}
}
}
case 13:
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint32_t x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
lean_dec(x_1);
x_79 = l_IO_Error_otherErrorToString(x_78, x_77, x_76);
return x_79;
}
else
{
uint32_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
lean_dec(x_1);
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
lean_dec(x_76);
x_83 = lean_box(0);
x_84 = l_IO_Error_fopenErrorToString(x_81, x_82, x_80, x_83);
lean_dec(x_82);
return x_84;
}
}
case 14:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
uint32_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
lean_dec(x_1);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_IO_Error_toString___closed__13;
x_90 = l_IO_Error_otherErrorToString(x_89, x_86, x_88);
return x_90;
}
else
{
uint32_t x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_92 = lean_ctor_get(x_1, 1);
lean_inc(x_92);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_85);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_85, 0);
lean_ctor_set(x_85, 0, x_92);
x_95 = l_IO_Error_toString___closed__13;
x_96 = l_IO_Error_fopenErrorToString(x_95, x_94, x_91, x_85);
lean_dec(x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
lean_dec(x_85);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_92);
x_99 = l_IO_Error_toString___closed__13;
x_100 = l_IO_Error_fopenErrorToString(x_99, x_97, x_91, x_98);
lean_dec(x_97);
return x_100;
}
}
}
case 15:
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_1, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
uint32_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
lean_dec(x_1);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_IO_Error_toString___closed__14;
x_106 = l_IO_Error_otherErrorToString(x_105, x_102, x_104);
return x_106;
}
else
{
uint32_t x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_101);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_101, 0);
lean_ctor_set(x_101, 0, x_108);
x_111 = l_IO_Error_toString___closed__14;
x_112 = l_IO_Error_fopenErrorToString(x_111, x_110, x_107, x_101);
lean_dec(x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
lean_dec(x_101);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_108);
x_115 = l_IO_Error_toString___closed__14;
x_116 = l_IO_Error_fopenErrorToString(x_115, x_113, x_107, x_114);
lean_dec(x_113);
return x_116;
}
}
}
case 16:
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_1, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint32_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_119 = lean_ctor_get(x_1, 1);
lean_inc(x_119);
lean_dec(x_1);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_IO_Error_toString___closed__15;
x_122 = l_IO_Error_otherErrorToString(x_121, x_118, x_120);
return x_122;
}
else
{
uint32_t x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_124 = lean_ctor_get(x_1, 1);
lean_inc(x_124);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_117);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_117, 0);
lean_ctor_set(x_117, 0, x_124);
x_127 = l_IO_Error_toString___closed__15;
x_128 = l_IO_Error_fopenErrorToString(x_127, x_126, x_123, x_117);
lean_dec(x_126);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_117, 0);
lean_inc(x_129);
lean_dec(x_117);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_124);
x_131 = l_IO_Error_toString___closed__15;
x_132 = l_IO_Error_fopenErrorToString(x_131, x_129, x_123, x_130);
lean_dec(x_129);
return x_132;
}
}
}
case 17:
{
lean_object* x_133; 
x_133 = l_IO_Error_toString___closed__16;
return x_133;
}
default: 
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_1, 0);
lean_inc(x_134);
lean_dec(x_1);
return x_134;
}
}
}
}
lean_object* _init_l_IO_Error_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_io_error_to_string), 1, 0);
return x_1;
}
}
lean_object* _init_l_IO_Error_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_Error_HasToString___closed__1;
return x_1;
}
}
lean_object* _init_l_IO_Error_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_IO_Error_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_Error_Inhabited___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_System_IOError(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lean_mk_io_error_eof = _init_lean_mk_io_error_eof();
lean_mark_persistent(lean_mk_io_error_eof);
l___private_Init_System_IOError_1__downCaseFirst___closed__1 = _init_l___private_Init_System_IOError_1__downCaseFirst___closed__1();
lean_mark_persistent(l___private_Init_System_IOError_1__downCaseFirst___closed__1);
l_IO_Error_fopenErrorToString___closed__1 = _init_l_IO_Error_fopenErrorToString___closed__1();
lean_mark_persistent(l_IO_Error_fopenErrorToString___closed__1);
l_IO_Error_fopenErrorToString___closed__2 = _init_l_IO_Error_fopenErrorToString___closed__2();
lean_mark_persistent(l_IO_Error_fopenErrorToString___closed__2);
l_IO_Error_toString___closed__1 = _init_l_IO_Error_toString___closed__1();
lean_mark_persistent(l_IO_Error_toString___closed__1);
l_IO_Error_toString___closed__2 = _init_l_IO_Error_toString___closed__2();
lean_mark_persistent(l_IO_Error_toString___closed__2);
l_IO_Error_toString___closed__3 = _init_l_IO_Error_toString___closed__3();
lean_mark_persistent(l_IO_Error_toString___closed__3);
l_IO_Error_toString___closed__4 = _init_l_IO_Error_toString___closed__4();
lean_mark_persistent(l_IO_Error_toString___closed__4);
l_IO_Error_toString___closed__5 = _init_l_IO_Error_toString___closed__5();
lean_mark_persistent(l_IO_Error_toString___closed__5);
l_IO_Error_toString___closed__6 = _init_l_IO_Error_toString___closed__6();
lean_mark_persistent(l_IO_Error_toString___closed__6);
l_IO_Error_toString___closed__7 = _init_l_IO_Error_toString___closed__7();
lean_mark_persistent(l_IO_Error_toString___closed__7);
l_IO_Error_toString___closed__8 = _init_l_IO_Error_toString___closed__8();
lean_mark_persistent(l_IO_Error_toString___closed__8);
l_IO_Error_toString___closed__9 = _init_l_IO_Error_toString___closed__9();
lean_mark_persistent(l_IO_Error_toString___closed__9);
l_IO_Error_toString___closed__10 = _init_l_IO_Error_toString___closed__10();
lean_mark_persistent(l_IO_Error_toString___closed__10);
l_IO_Error_toString___closed__11 = _init_l_IO_Error_toString___closed__11();
lean_mark_persistent(l_IO_Error_toString___closed__11);
l_IO_Error_toString___closed__12 = _init_l_IO_Error_toString___closed__12();
lean_mark_persistent(l_IO_Error_toString___closed__12);
l_IO_Error_toString___closed__13 = _init_l_IO_Error_toString___closed__13();
lean_mark_persistent(l_IO_Error_toString___closed__13);
l_IO_Error_toString___closed__14 = _init_l_IO_Error_toString___closed__14();
lean_mark_persistent(l_IO_Error_toString___closed__14);
l_IO_Error_toString___closed__15 = _init_l_IO_Error_toString___closed__15();
lean_mark_persistent(l_IO_Error_toString___closed__15);
l_IO_Error_toString___closed__16 = _init_l_IO_Error_toString___closed__16();
lean_mark_persistent(l_IO_Error_toString___closed__16);
l_IO_Error_HasToString___closed__1 = _init_l_IO_Error_HasToString___closed__1();
lean_mark_persistent(l_IO_Error_HasToString___closed__1);
l_IO_Error_HasToString = _init_l_IO_Error_HasToString();
lean_mark_persistent(l_IO_Error_HasToString);
l_IO_Error_Inhabited___closed__1 = _init_l_IO_Error_Inhabited___closed__1();
lean_mark_persistent(l_IO_Error_Inhabited___closed__1);
l_IO_Error_Inhabited = _init_l_IO_Error_Inhabited();
lean_mark_persistent(l_IO_Error_Inhabited);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
