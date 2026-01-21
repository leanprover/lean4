// Lean compiler output
// Module: Init.Data.Ord.SInt
// Imports: public import Init.Data.Order.Ord public import Init.Data.SInt.Lemmas
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
LEAN_EXPORT lean_object* l_Int8_instOrd___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int32_instOrd;
LEAN_EXPORT lean_object* l_Int16_instOrd___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_int8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_ISize_instOrd___lam__0(size_t, size_t);
static lean_object* l_Int64_instOrd___closed__0;
LEAN_EXPORT lean_object* l_Int16_instOrd;
LEAN_EXPORT uint8_t l_Int16_instOrd___lam__0(uint16_t, uint16_t);
uint8_t lean_int32_dec_lt(uint32_t, uint32_t);
uint8_t lean_int64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_instOrd;
LEAN_EXPORT uint8_t l_Int8_instOrd___lam__0(uint8_t, uint8_t);
static lean_object* l_ISize_instOrd___closed__0;
static lean_object* l_Int32_instOrd___closed__0;
LEAN_EXPORT uint8_t l_Int64_instOrd___lam__0(uint64_t, uint64_t);
static lean_object* l_Int16_instOrd___closed__0;
uint8_t lean_int64_dec_eq(uint64_t, uint64_t);
uint8_t lean_isize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Int32_instOrd___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int64_instOrd___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_int8_dec_lt(uint8_t, uint8_t);
uint8_t lean_int16_dec_eq(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int8_instOrd;
uint8_t lean_int16_dec_lt(uint16_t, uint16_t);
uint8_t lean_isize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Int32_instOrd___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Int8_instOrd___closed__0;
uint8_t lean_int32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_ISize_instOrd;
LEAN_EXPORT lean_object* l_ISize_instOrd___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int8_instOrd___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int8_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_int8_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int8_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Int8_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Int8_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int8_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int8_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_Int8_instOrd___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Int16_instOrd___lam__0(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int16_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_int16_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int16_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Int16_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Int16_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int16_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int16_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_Int16_instOrd___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Int32_instOrd___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int32_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_int32_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int32_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Int32_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Int32_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int32_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int32_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_Int32_instOrd___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Int64_instOrd___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int64_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_int64_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int64_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Int64_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Int64_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int64_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int64_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_Int64_instOrd___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_ISize_instOrd___lam__0(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_isize_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_isize_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_ISize_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_ISize_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_ISize_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ISize_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_ISize_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_ISize_instOrd___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_SInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int8_instOrd___closed__0 = _init_l_Int8_instOrd___closed__0();
lean_mark_persistent(l_Int8_instOrd___closed__0);
l_Int8_instOrd = _init_l_Int8_instOrd();
lean_mark_persistent(l_Int8_instOrd);
l_Int16_instOrd___closed__0 = _init_l_Int16_instOrd___closed__0();
lean_mark_persistent(l_Int16_instOrd___closed__0);
l_Int16_instOrd = _init_l_Int16_instOrd();
lean_mark_persistent(l_Int16_instOrd);
l_Int32_instOrd___closed__0 = _init_l_Int32_instOrd___closed__0();
lean_mark_persistent(l_Int32_instOrd___closed__0);
l_Int32_instOrd = _init_l_Int32_instOrd();
lean_mark_persistent(l_Int32_instOrd);
l_Int64_instOrd___closed__0 = _init_l_Int64_instOrd___closed__0();
lean_mark_persistent(l_Int64_instOrd___closed__0);
l_Int64_instOrd = _init_l_Int64_instOrd();
lean_mark_persistent(l_Int64_instOrd);
l_ISize_instOrd___closed__0 = _init_l_ISize_instOrd___closed__0();
lean_mark_persistent(l_ISize_instOrd___closed__0);
l_ISize_instOrd = _init_l_ISize_instOrd();
lean_mark_persistent(l_ISize_instOrd);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
