// Lean compiler output
// Module: Init.Data.Ord.UInt
// Imports: public import Init.Data.Order.Ord public import Init.Data.UInt.Lemmas
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
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt32_instOrd___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_USize_instOrd___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_USize_instOrd___lam__0(size_t, size_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instOrd___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt16_instOrd___lam__0(uint16_t, uint16_t);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_instOrd;
LEAN_EXPORT uint8_t l_UInt8_instOrd___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt64_instOrd;
LEAN_EXPORT lean_object* l_UInt8_instOrd___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt32_instOrd___lam__0(uint32_t, uint32_t);
static lean_object* l_UInt8_instOrd___closed__0;
static lean_object* l_UInt16_instOrd___closed__0;
LEAN_EXPORT uint8_t l_UInt64_instOrd___lam__0(uint64_t, uint64_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt32_instOrd;
static lean_object* l_USize_instOrd___closed__0;
LEAN_EXPORT lean_object* l_UInt16_instOrd;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l_UInt64_instOrd___closed__0;
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
static lean_object* l_UInt32_instOrd___closed__0;
LEAN_EXPORT lean_object* l_UInt64_instOrd___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_UInt8_instOrd;
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_UInt8_instOrd___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint8_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint8_dec_eq(x_1, x_2);
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
LEAN_EXPORT lean_object* l_UInt8_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_UInt8_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_UInt8_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_UInt8_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt8_instOrd___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_UInt16_instOrd___lam__0(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint16_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint16_dec_eq(x_1, x_2);
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
LEAN_EXPORT lean_object* l_UInt16_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_UInt16_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_UInt16_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_UInt16_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt16_instOrd___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_UInt32_instOrd___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint32_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint32_dec_eq(x_1, x_2);
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
LEAN_EXPORT lean_object* l_UInt32_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_UInt32_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_UInt32_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_UInt32_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt32_instOrd___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_UInt64_instOrd___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint64_dec_eq(x_1, x_2);
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
LEAN_EXPORT lean_object* l_UInt64_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_UInt64_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_UInt64_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_UInt64_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_UInt64_instOrd___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_USize_instOrd___lam__0(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_usize_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_1, x_2);
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
LEAN_EXPORT lean_object* l_USize_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_USize_instOrd___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_USize_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_USize_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_USize_instOrd___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_UInt8_instOrd___closed__0 = _init_l_UInt8_instOrd___closed__0();
lean_mark_persistent(l_UInt8_instOrd___closed__0);
l_UInt8_instOrd = _init_l_UInt8_instOrd();
lean_mark_persistent(l_UInt8_instOrd);
l_UInt16_instOrd___closed__0 = _init_l_UInt16_instOrd___closed__0();
lean_mark_persistent(l_UInt16_instOrd___closed__0);
l_UInt16_instOrd = _init_l_UInt16_instOrd();
lean_mark_persistent(l_UInt16_instOrd);
l_UInt32_instOrd___closed__0 = _init_l_UInt32_instOrd___closed__0();
lean_mark_persistent(l_UInt32_instOrd___closed__0);
l_UInt32_instOrd = _init_l_UInt32_instOrd();
lean_mark_persistent(l_UInt32_instOrd);
l_UInt64_instOrd___closed__0 = _init_l_UInt64_instOrd___closed__0();
lean_mark_persistent(l_UInt64_instOrd___closed__0);
l_UInt64_instOrd = _init_l_UInt64_instOrd();
lean_mark_persistent(l_UInt64_instOrd);
l_USize_instOrd___closed__0 = _init_l_USize_instOrd___closed__0();
lean_mark_persistent(l_USize_instOrd___closed__0);
l_USize_instOrd = _init_l_USize_instOrd();
lean_mark_persistent(l_USize_instOrd);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
