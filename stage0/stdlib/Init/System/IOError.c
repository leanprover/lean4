// Lean compiler output
// Module: Init.System.IOError
// Imports: Init.Core Init.Data.UInt Init.Data.ToString.Basic Init.Data.String.Basic
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
lean_object* lean_mk_io_error_invalid_argument(uint32_t, lean_object*);
lean_object* lean_mk_io_error_invalid_argument_file(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_fopenErrorToString_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Error_toString___closed__12;
static lean_object* l_IO_Error_toString___closed__11;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_Error_mkOtherError___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_error_permission_denied(uint32_t, lean_object*);
lean_object* l_IO_Error_toString_match__1(lean_object*);
lean_object* lean_mk_io_error_no_file_or_directory(lean_object*, uint32_t, lean_object*);
static lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1;
lean_object* l_String_modify(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_mkResourceVanished___boxed(lean_object*, lean_object*);
static lean_object* l_IO_Error_toString___closed__3;
static lean_object* l_IO_Error_fopenErrorToString___closed__1;
lean_object* l_IO_Error_fopenErrorToString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_otherErrorToString(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkNoSuchThing___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_fopenErrorToString(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* mk_io_user_error(lean_object*);
lean_object* l_IO_Error_toString_match__1___rarg___boxed(lean_object**);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_IO_Error_toString___closed__7;
lean_object* l_IO_Error_mkAlreadyExists___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_error_already_exists(uint32_t, lean_object*);
lean_object* l_IO_Error_mkPermissionDeniedFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Error_toString___closed__8;
lean_object* l_IO_Error_mkPermissionDenied___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_instToStringError;
lean_object* l_IO_Error_mkNoFileOrDirectory___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Error_otherErrorToString___closed__1;
static lean_object* l_IO_instInhabitedError___closed__3;
lean_object* l_IO_Error_otherErrorToString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instCoeStringError;
lean_object* lean_mk_io_error_resource_exhausted(uint32_t, lean_object*);
static lean_object* l_IO_Error_toString___closed__4;
lean_object* l_IO_Error_mkInappropriateType___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_fopenErrorToString_match__1(lean_object*);
static lean_object* l_instCoeStringError___closed__1;
lean_object* l_IO_Error_mkTimeExpired___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_mkInterrupted___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Error_mkInappropriateTypeFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Error_toString___closed__9;
lean_object* lean_mk_io_error_inappropriate_type_file(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkHardwareFault___boxed(lean_object*, lean_object*);
static lean_object* l_IO_Error_toString___closed__2;
lean_object* lean_mk_io_error_hardware_fault(uint32_t, lean_object*);
lean_object* l_Char_toLower___boxed(lean_object*);
static lean_object* l_IO_Error_toString___closed__1;
static lean_object* l_IO_instInhabitedError___closed__2;
lean_object* l_IO_Error_mkProtocolError___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_mkResourceBusy___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static uint32_t l_IO_instInhabitedError___closed__1;
lean_object* lean_mk_io_error_no_such_thing_file(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkInvalidArgument___boxed(lean_object*, lean_object*);
static lean_object* l_IO_Error_fopenErrorToString___closed__3;
lean_object* lean_mk_io_error_other_error(uint32_t, lean_object*);
lean_object* lean_mk_io_error_resource_exhausted_file(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_io_error_permission_denied_file(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkNoSuchThingFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_error_time_expired(uint32_t, lean_object*);
lean_object* l_IO_Error_mkResourceExhaustedFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_error_unsupported_operation(uint32_t, lean_object*);
static lean_object* l_IO_Error_toString___closed__14;
lean_object* lean_mk_io_error_protocol_error(uint32_t, lean_object*);
lean_object* lean_mk_io_error_illegal_operation(uint32_t, lean_object*);
lean_object* lean_mk_io_error_resource_vanished(uint32_t, lean_object*);
lean_object* l_IO_Error_toString_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Error_toString___closed__15;
lean_object* lean_mk_io_error_unsatisfied_constraints(uint32_t, lean_object*);
static lean_object* l_IO_Error_toString___closed__5;
lean_object* lean_mk_io_error_resource_busy(uint32_t, lean_object*);
lean_object* l_IO_Error_mkResourceExhausted___boxed(lean_object*, lean_object*);
lean_object* l_IO_Error_mkUnsatisfiedConstraints___boxed(lean_object*, lean_object*);
static lean_object* l_IO_Error_instToStringError___closed__1;
lean_object* l_IO_Error_mkInvalidArgumentFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Error_toString___closed__16;
static lean_object* l_IO_Error_fopenErrorToString___closed__2;
lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object*);
static lean_object* l_IO_Error_toString___closed__10;
lean_object* l_IO_instInhabitedError;
lean_object* lean_mk_io_error_no_such_thing(uint32_t, lean_object*);
lean_object* lean_mk_io_error_inappropriate_type(uint32_t, lean_object*);
lean_object* lean_mk_io_error_eof(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_IO_Error_toString___closed__13;
lean_object* l_IO_Error_mkIllegalOperation___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_IO_Error_toString___closed__6;
lean_object* lean_mk_io_error_interrupted(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_Error_mkUnsupportedOperation___boxed(lean_object*, lean_object*);
static uint32_t _init_l_IO_instInhabitedError___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_instInhabitedError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_IO_instInhabitedError___closed__3() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_instInhabitedError___closed__1;
x_2 = l_IO_instInhabitedError___closed__2;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_instInhabitedError() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_instInhabitedError___closed__3;
return x_1;
}
}
lean_object* mk_io_user_error(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instCoeStringError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(mk_io_user_error), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instCoeStringError() {
_start:
{
lean_object* x_1; 
x_1 = l_instCoeStringError___closed__1;
return x_1;
}
}
lean_object* lean_mk_io_error_eof(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(17);
return x_2;
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
static lean_object* _init_l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_toLower___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Init_System_IOError_0__IO_Error_downCaseFirst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1;
x_4 = l_String_modify(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_Error_fopenErrorToString_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_IO_Error_fopenErrorToString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Error_fopenErrorToString_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_IO_Error_fopenErrorToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (error code: ");
return x_1;
}
}
static lean_object* _init_l_IO_Error_fopenErrorToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")\n  file: ");
return x_1;
}
}
static lean_object* _init_l_IO_Error_fopenErrorToString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
lean_object* l_IO_Error_fopenErrorToString(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1;
x_7 = l_String_modify(x_1, x_5, x_6);
x_8 = l_IO_Error_fopenErrorToString___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_uint32_to_nat(x_3);
x_11 = l_Nat_repr(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = l_IO_Error_fopenErrorToString___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1;
x_19 = l_String_modify(x_1, x_17, x_18);
x_20 = l_IO_Error_fopenErrorToString___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_uint32_to_nat(x_3);
x_23 = l_Nat_repr(x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec(x_23);
x_25 = l_IO_Error_fopenErrorToString___closed__3;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_String_modify(x_16, x_17, x_18);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = l_IO_Error_fopenErrorToString___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_2);
return x_31;
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
static lean_object* _init_l_IO_Error_otherErrorToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
lean_object* l_IO_Error_otherErrorToString(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1;
x_6 = l_String_modify(x_1, x_4, x_5);
x_7 = l_IO_Error_fopenErrorToString___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_uint32_to_nat(x_2);
x_10 = l_Nat_repr(x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = l_IO_Error_otherErrorToString___closed__1;
x_13 = lean_string_append(x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1;
x_17 = l_String_modify(x_1, x_15, x_16);
x_18 = l_IO_Error_fopenErrorToString___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_uint32_to_nat(x_2);
x_21 = l_Nat_repr(x_20);
x_22 = lean_string_append(x_19, x_21);
lean_dec(x_21);
x_23 = l_IO_Error_fopenErrorToString___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_String_modify(x_14, x_15, x_16);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_IO_Error_otherErrorToString___closed__1;
x_28 = lean_string_append(x_26, x_27);
return x_28;
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
lean_object* l_IO_Error_toString_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint32_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_box_uint32(x_26);
x_29 = lean_apply_2(x_15, x_28, x_27);
return x_29;
}
case 1:
{
uint32_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_box_uint32(x_30);
x_33 = lean_apply_2(x_16, x_32, x_31);
return x_33;
}
case 2:
{
uint32_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_box_uint32(x_34);
x_37 = lean_apply_2(x_17, x_36, x_35);
return x_37;
}
case 3:
{
uint32_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_box_uint32(x_38);
x_41 = lean_apply_2(x_18, x_40, x_39);
return x_41;
}
case 4:
{
uint32_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_box_uint32(x_42);
x_45 = lean_apply_2(x_24, x_44, x_43);
return x_45;
}
case 5:
{
uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_box_uint32(x_46);
x_49 = lean_apply_2(x_19, x_48, x_47);
return x_49;
}
case 6:
{
uint32_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_box_uint32(x_50);
x_53 = lean_apply_2(x_23, x_52, x_51);
return x_53;
}
case 7:
{
uint32_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_box_uint32(x_54);
x_57 = lean_apply_2(x_20, x_56, x_55);
return x_57;
}
case 8:
{
uint32_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_box_uint32(x_58);
x_61 = lean_apply_2(x_21, x_60, x_59);
return x_61;
}
case 9:
{
uint32_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_box_uint32(x_62);
x_65 = lean_apply_2(x_22, x_64, x_63);
return x_65;
}
case 10:
{
lean_object* x_66; uint32_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_box_uint32(x_67);
x_70 = lean_apply_3(x_5, x_66, x_69, x_68);
return x_70;
}
case 11:
{
lean_object* x_71; uint32_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_box_uint32(x_72);
x_75 = lean_apply_3(x_8, x_71, x_74, x_73);
return x_75;
}
case 12:
{
lean_object* x_76; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint32_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_6);
x_77 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
lean_dec(x_1);
x_79 = lean_box_uint32(x_77);
x_80 = lean_apply_2(x_7, x_79, x_78);
return x_80;
}
else
{
uint32_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_7);
x_81 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
lean_dec(x_1);
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_box_uint32(x_81);
x_85 = lean_apply_3(x_6, x_83, x_84, x_82);
return x_85;
}
}
case 13:
{
lean_object* x_86; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint32_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_11);
x_87 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_box_uint32(x_87);
x_90 = lean_apply_2(x_12, x_89, x_88);
return x_90;
}
else
{
uint32_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_12);
x_91 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_92 = lean_ctor_get(x_1, 1);
lean_inc(x_92);
lean_dec(x_1);
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
lean_dec(x_86);
x_94 = lean_box_uint32(x_91);
x_95 = lean_apply_3(x_11, x_93, x_94, x_92);
return x_95;
}
}
case 14:
{
lean_object* x_96; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
uint32_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_13);
x_97 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_98 = lean_ctor_get(x_1, 1);
lean_inc(x_98);
lean_dec(x_1);
x_99 = lean_box_uint32(x_97);
x_100 = lean_apply_2(x_14, x_99, x_98);
return x_100;
}
else
{
uint32_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_14);
x_101 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_102 = lean_ctor_get(x_1, 1);
lean_inc(x_102);
lean_dec(x_1);
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
lean_dec(x_96);
x_104 = lean_box_uint32(x_101);
x_105 = lean_apply_3(x_13, x_103, x_104, x_102);
return x_105;
}
}
case 15:
{
lean_object* x_106; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
uint32_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
x_107 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
lean_dec(x_1);
x_109 = lean_box_uint32(x_107);
x_110 = lean_apply_2(x_4, x_109, x_108);
return x_110;
}
else
{
uint32_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_4);
x_111 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_113 = lean_ctor_get(x_106, 0);
lean_inc(x_113);
lean_dec(x_106);
x_114 = lean_box_uint32(x_111);
x_115 = lean_apply_3(x_3, x_113, x_114, x_112);
return x_115;
}
}
case 16:
{
lean_object* x_116; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_1, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
uint32_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_9);
x_117 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
lean_dec(x_1);
x_119 = lean_box_uint32(x_117);
x_120 = lean_apply_2(x_10, x_119, x_118);
return x_120;
}
else
{
uint32_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_10);
x_121 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_122 = lean_ctor_get(x_1, 1);
lean_inc(x_122);
lean_dec(x_1);
x_123 = lean_ctor_get(x_116, 0);
lean_inc(x_123);
lean_dec(x_116);
x_124 = lean_box_uint32(x_121);
x_125 = lean_apply_3(x_9, x_123, x_124, x_122);
return x_125;
}
}
case 17:
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = lean_box(0);
x_127 = lean_apply_1(x_2, x_126);
return x_127;
}
default: 
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_1, 0);
lean_inc(x_128);
lean_dec(x_1);
x_129 = lean_apply_1(x_25, x_128);
return x_129;
}
}
}
}
lean_object* l_IO_Error_toString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Error_toString_match__1___rarg___boxed), 25, 0);
return x_2;
}
}
lean_object* l_IO_Error_toString_match__1___rarg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
lean_object* x_26; 
x_26 = l_IO_Error_toString_match__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
return x_26;
}
}
static lean_object* _init_l_IO_Error_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("already exists");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resource busy");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resource vanished");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsupported operation");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hardware fault");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("directory not empty");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("illegal operation");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("protocol error");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("time expired");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("interrupted system call");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no such file or directory");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid argument");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resource exhausted");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inappropriate type");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no such thing");
return x_1;
}
}
static lean_object* _init_l_IO_Error_toString___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("end of file");
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
uint32_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = l_IO_Error_otherErrorToString(x_78, x_77, x_79);
return x_80;
}
else
{
uint32_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
lean_dec(x_1);
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_box(0);
x_85 = l_IO_Error_fopenErrorToString(x_82, x_83, x_81, x_84);
lean_dec(x_83);
return x_85;
}
}
case 14:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint32_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_IO_Error_toString___closed__13;
x_91 = l_IO_Error_otherErrorToString(x_90, x_87, x_89);
return x_91;
}
else
{
uint32_t x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_93 = lean_ctor_get(x_1, 1);
lean_inc(x_93);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 0);
lean_ctor_set(x_86, 0, x_93);
x_96 = l_IO_Error_toString___closed__13;
x_97 = l_IO_Error_fopenErrorToString(x_96, x_95, x_92, x_86);
lean_dec(x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
lean_dec(x_86);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_93);
x_100 = l_IO_Error_toString___closed__13;
x_101 = l_IO_Error_fopenErrorToString(x_100, x_98, x_92, x_99);
lean_dec(x_98);
return x_101;
}
}
}
case 15:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
uint32_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_104 = lean_ctor_get(x_1, 1);
lean_inc(x_104);
lean_dec(x_1);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_IO_Error_toString___closed__14;
x_107 = l_IO_Error_otherErrorToString(x_106, x_103, x_105);
return x_107;
}
else
{
uint32_t x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_109 = lean_ctor_get(x_1, 1);
lean_inc(x_109);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_102);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_102, 0);
lean_ctor_set(x_102, 0, x_109);
x_112 = l_IO_Error_toString___closed__14;
x_113 = l_IO_Error_fopenErrorToString(x_112, x_111, x_108, x_102);
lean_dec(x_111);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_102, 0);
lean_inc(x_114);
lean_dec(x_102);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_109);
x_116 = l_IO_Error_toString___closed__14;
x_117 = l_IO_Error_fopenErrorToString(x_116, x_114, x_108, x_115);
lean_dec(x_114);
return x_117;
}
}
}
case 16:
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint32_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
lean_dec(x_1);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_IO_Error_toString___closed__15;
x_123 = l_IO_Error_otherErrorToString(x_122, x_119, x_121);
return x_123;
}
else
{
uint32_t x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_125 = lean_ctor_get(x_1, 1);
lean_inc(x_125);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_118);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_118, 0);
lean_ctor_set(x_118, 0, x_125);
x_128 = l_IO_Error_toString___closed__15;
x_129 = l_IO_Error_fopenErrorToString(x_128, x_127, x_124, x_118);
lean_dec(x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_118, 0);
lean_inc(x_130);
lean_dec(x_118);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_125);
x_132 = l_IO_Error_toString___closed__15;
x_133 = l_IO_Error_fopenErrorToString(x_132, x_130, x_124, x_131);
lean_dec(x_130);
return x_133;
}
}
}
case 17:
{
lean_object* x_134; 
x_134 = l_IO_Error_toString___closed__16;
return x_134;
}
default: 
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
lean_dec(x_1);
return x_135;
}
}
}
}
static lean_object* _init_l_IO_Error_instToStringError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_io_error_to_string), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IO_Error_instToStringError() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_Error_instToStringError___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_System_IOError(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_instInhabitedError___closed__1 = _init_l_IO_instInhabitedError___closed__1();
l_IO_instInhabitedError___closed__2 = _init_l_IO_instInhabitedError___closed__2();
lean_mark_persistent(l_IO_instInhabitedError___closed__2);
l_IO_instInhabitedError___closed__3 = _init_l_IO_instInhabitedError___closed__3();
lean_mark_persistent(l_IO_instInhabitedError___closed__3);
l_IO_instInhabitedError = _init_l_IO_instInhabitedError();
lean_mark_persistent(l_IO_instInhabitedError);
l_instCoeStringError___closed__1 = _init_l_instCoeStringError___closed__1();
lean_mark_persistent(l_instCoeStringError___closed__1);
l_instCoeStringError = _init_l_instCoeStringError();
lean_mark_persistent(l_instCoeStringError);
l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1 = _init_l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1();
lean_mark_persistent(l___private_Init_System_IOError_0__IO_Error_downCaseFirst___closed__1);
l_IO_Error_fopenErrorToString___closed__1 = _init_l_IO_Error_fopenErrorToString___closed__1();
lean_mark_persistent(l_IO_Error_fopenErrorToString___closed__1);
l_IO_Error_fopenErrorToString___closed__2 = _init_l_IO_Error_fopenErrorToString___closed__2();
lean_mark_persistent(l_IO_Error_fopenErrorToString___closed__2);
l_IO_Error_fopenErrorToString___closed__3 = _init_l_IO_Error_fopenErrorToString___closed__3();
lean_mark_persistent(l_IO_Error_fopenErrorToString___closed__3);
l_IO_Error_otherErrorToString___closed__1 = _init_l_IO_Error_otherErrorToString___closed__1();
lean_mark_persistent(l_IO_Error_otherErrorToString___closed__1);
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
l_IO_Error_instToStringError___closed__1 = _init_l_IO_Error_instToStringError___closed__1();
lean_mark_persistent(l_IO_Error_instToStringError___closed__1);
l_IO_Error_instToStringError = _init_l_IO_Error_instToStringError();
lean_mark_persistent(l_IO_Error_instToStringError);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
