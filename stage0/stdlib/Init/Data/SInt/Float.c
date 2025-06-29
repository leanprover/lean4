// Lean compiler output
// Module: Init.Data.SInt.Float
// Imports: Init.Data.Float Init.Data.SInt.Basic
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
LEAN_EXPORT lean_object* l_ISize_toFloat___boxed(lean_object*);
size_t lean_float_to_isize(double);
double lean_int64_to_float(uint64_t);
uint32_t lean_float_to_int32(double);
LEAN_EXPORT lean_object* l_Float_toInt8___boxed(lean_object*);
uint8_t lean_float_to_int8(double);
double lean_isize_to_float(size_t);
LEAN_EXPORT lean_object* l_Int8_toFloat___boxed(lean_object*);
double lean_int16_to_float(uint16_t);
LEAN_EXPORT lean_object* l_Float_toInt64___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int32_toFloat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int64_toFloat___boxed(lean_object*);
uint64_t lean_float_to_int64(double);
LEAN_EXPORT lean_object* l_Float_toInt32___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_toISize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int16_toFloat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_toInt16___boxed(lean_object*);
uint16_t lean_float_to_int16(double);
double lean_int32_to_float(uint32_t);
double lean_int8_to_float(uint8_t);
LEAN_EXPORT lean_object* l_Float_toInt8___boxed(lean_object* x_1) {
_start:
{
double x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_int8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_toInt16___boxed(lean_object* x_1) {
_start:
{
double x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_int16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_toInt32___boxed(lean_object* x_1) {
_start:
{
double x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_int32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_toInt64___boxed(lean_object* x_1) {
_start:
{
double x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_int64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_toISize___boxed(lean_object* x_1) {
_start:
{
double x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_isize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_toFloat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = lean_int8_to_float(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_toFloat___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = lean_int16_to_float(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_toFloat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_to_float(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_toFloat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_to_float(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_toFloat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_to_float(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Float(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Float(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
