// Lean compiler output
// Module: Init.Grind.CommRing.SInt
// Imports: Init.Grind.CommRing.Basic Init.Data.SInt.Lemmas
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
lean_object* l_Int8_instOfNat___boxed(lean_object*);
extern lean_object* l_instPowInt16Nat;
extern lean_object* l_instAddISize;
extern lean_object* l_instMulInt8;
LEAN_EXPORT uint64_t l_Lean_Grind_instIntCastInt64(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16;
LEAN_EXPORT uint32_t l_Lean_Grind_instIntCastInt32(lean_object*);
size_t lean_isize_of_int(lean_object*);
extern lean_object* l_instSubInt8;
uint16_t lean_int16_of_int(lean_object*);
lean_object* l_Int32_instOfNat___boxed(lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt64___closed__1;
static lean_object* l_Lean_Grind_instCommRingInt32___closed__1;
extern lean_object* l_Int8_instNeg;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32;
extern lean_object* l_instAddInt64;
lean_object* l_Int16_instOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastInt16___boxed(lean_object*);
extern lean_object* l_Int64_instNeg;
static lean_object* l_Lean_Grind_instCommRingInt8___closed__1;
extern lean_object* l_instSubInt32;
static lean_object* l_Lean_Grind_instCommRingInt8___closed__3;
extern lean_object* l_instPowInt64Nat;
static lean_object* l_Lean_Grind_instCommRingInt64___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastInt8___boxed(lean_object*);
lean_object* l_Int64_instOfNat___boxed(lean_object*);
extern lean_object* l_instPowInt32Nat;
static lean_object* l_Lean_Grind_instCommRingISize___closed__1;
static lean_object* l_Lean_Grind_instCommRingInt16___closed__1;
extern lean_object* l_instAddInt8;
extern lean_object* l_instSubISize;
static lean_object* l_Lean_Grind_instCommRingISize___closed__2;
static lean_object* l_Lean_Grind_instCommRingISize___closed__3;
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastInt64___boxed(lean_object*);
lean_object* l_ISize_instOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64;
static lean_object* l_Lean_Grind_instCommRingInt32___closed__2;
LEAN_EXPORT size_t l_Lean_Grind_instIntCastISize(lean_object*);
extern lean_object* l_Int16_instNeg;
extern lean_object* l_instSubInt16;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize;
extern lean_object* l_instSubInt64;
extern lean_object* l_ISize_instNeg;
extern lean_object* l_instPowISizeNat;
static lean_object* l_Lean_Grind_instCommRingInt32___closed__3;
extern lean_object* l_instAddInt32;
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastInt32___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instIntCastInt8(lean_object*);
extern lean_object* l_instMulInt32;
uint64_t lean_int64_of_int(lean_object*);
extern lean_object* l_instMulInt16;
uint8_t lean_int8_of_int(lean_object*);
extern lean_object* l_instAddInt16;
static lean_object* l_Lean_Grind_instCommRingInt8___closed__2;
static lean_object* l_Lean_Grind_instCommRingInt64___closed__3;
static lean_object* l_Lean_Grind_instCommRingInt16___closed__3;
static lean_object* l_Lean_Grind_instCommRingInt16___closed__2;
extern lean_object* l_instMulISize;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8;
extern lean_object* l_instMulInt64;
extern lean_object* l_Int32_instNeg;
extern lean_object* l_instPowInt8Nat;
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastISize___boxed(lean_object*);
uint32_t lean_int32_of_int(lean_object*);
lean_object* l_instHPow___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Grind_instIntCastInt16(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instIntCastInt8(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_int8_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_instIntCastInt8(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowInt8Nat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int8_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddInt8;
x_2 = l_instMulInt8;
x_3 = l_Int8_instNeg;
x_4 = l_instSubInt8;
x_5 = l_Lean_Grind_instCommRingInt8___closed__1;
x_6 = l_Lean_Grind_instCommRingInt8___closed__2;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingInt8___closed__3;
return x_1;
}
}
LEAN_EXPORT uint16_t l_Lean_Grind_instIntCastInt16(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_int16_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastInt16___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_instIntCastInt16(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt16___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowInt16Nat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt16___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int16_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt16___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddInt16;
x_2 = l_instMulInt16;
x_3 = l_Int16_instNeg;
x_4 = l_instSubInt16;
x_5 = l_Lean_Grind_instCommRingInt16___closed__1;
x_6 = l_Lean_Grind_instCommRingInt16___closed__2;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingInt16___closed__3;
return x_1;
}
}
LEAN_EXPORT uint32_t l_Lean_Grind_instIntCastInt32(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_int32_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_instIntCastInt32(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt32___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowInt32Nat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt32___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int32_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt32___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddInt32;
x_2 = l_instMulInt32;
x_3 = l_Int32_instNeg;
x_4 = l_instSubInt32;
x_5 = l_Lean_Grind_instCommRingInt32___closed__1;
x_6 = l_Lean_Grind_instCommRingInt32___closed__2;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingInt32___closed__3;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_instIntCastInt64(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_int64_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_instIntCastInt64(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt64___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowInt64Nat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt64___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int64_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt64___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddInt64;
x_2 = l_instMulInt64;
x_3 = l_Int64_instNeg;
x_4 = l_instSubInt64;
x_5 = l_Lean_Grind_instCommRingInt64___closed__1;
x_6 = l_Lean_Grind_instCommRingInt64___closed__2;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingInt64___closed__3;
return x_1;
}
}
LEAN_EXPORT size_t l_Lean_Grind_instIntCastISize(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_isize_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instIntCastISize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_instIntCastISize(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingISize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowISizeNat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingISize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ISize_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingISize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddISize;
x_2 = l_instMulISize;
x_3 = l_ISize_instNeg;
x_4 = l_instSubISize;
x_5 = l_Lean_Grind_instCommRingISize___closed__1;
x_6 = l_Lean_Grind_instCommRingISize___closed__2;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingISize() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingISize___closed__3;
return x_1;
}
}
lean_object* initialize_Init_Grind_CommRing_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_CommRing_SInt(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_CommRing_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instCommRingInt8___closed__1 = _init_l_Lean_Grind_instCommRingInt8___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingInt8___closed__1);
l_Lean_Grind_instCommRingInt8___closed__2 = _init_l_Lean_Grind_instCommRingInt8___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingInt8___closed__2);
l_Lean_Grind_instCommRingInt8___closed__3 = _init_l_Lean_Grind_instCommRingInt8___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingInt8___closed__3);
l_Lean_Grind_instCommRingInt8 = _init_l_Lean_Grind_instCommRingInt8();
lean_mark_persistent(l_Lean_Grind_instCommRingInt8);
l_Lean_Grind_instCommRingInt16___closed__1 = _init_l_Lean_Grind_instCommRingInt16___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingInt16___closed__1);
l_Lean_Grind_instCommRingInt16___closed__2 = _init_l_Lean_Grind_instCommRingInt16___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingInt16___closed__2);
l_Lean_Grind_instCommRingInt16___closed__3 = _init_l_Lean_Grind_instCommRingInt16___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingInt16___closed__3);
l_Lean_Grind_instCommRingInt16 = _init_l_Lean_Grind_instCommRingInt16();
lean_mark_persistent(l_Lean_Grind_instCommRingInt16);
l_Lean_Grind_instCommRingInt32___closed__1 = _init_l_Lean_Grind_instCommRingInt32___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingInt32___closed__1);
l_Lean_Grind_instCommRingInt32___closed__2 = _init_l_Lean_Grind_instCommRingInt32___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingInt32___closed__2);
l_Lean_Grind_instCommRingInt32___closed__3 = _init_l_Lean_Grind_instCommRingInt32___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingInt32___closed__3);
l_Lean_Grind_instCommRingInt32 = _init_l_Lean_Grind_instCommRingInt32();
lean_mark_persistent(l_Lean_Grind_instCommRingInt32);
l_Lean_Grind_instCommRingInt64___closed__1 = _init_l_Lean_Grind_instCommRingInt64___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingInt64___closed__1);
l_Lean_Grind_instCommRingInt64___closed__2 = _init_l_Lean_Grind_instCommRingInt64___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingInt64___closed__2);
l_Lean_Grind_instCommRingInt64___closed__3 = _init_l_Lean_Grind_instCommRingInt64___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingInt64___closed__3);
l_Lean_Grind_instCommRingInt64 = _init_l_Lean_Grind_instCommRingInt64();
lean_mark_persistent(l_Lean_Grind_instCommRingInt64);
l_Lean_Grind_instCommRingISize___closed__1 = _init_l_Lean_Grind_instCommRingISize___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingISize___closed__1);
l_Lean_Grind_instCommRingISize___closed__2 = _init_l_Lean_Grind_instCommRingISize___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingISize___closed__2);
l_Lean_Grind_instCommRingISize___closed__3 = _init_l_Lean_Grind_instCommRingISize___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingISize___closed__3);
l_Lean_Grind_instCommRingISize = _init_l_Lean_Grind_instCommRingISize();
lean_mark_persistent(l_Lean_Grind_instCommRingISize);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
