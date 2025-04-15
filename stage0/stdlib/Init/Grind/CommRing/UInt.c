// Lean compiler output
// Module: Init.Grind.CommRing.UInt
// Imports: Init.Grind.CommRing.Basic Init.Data.UInt.Lemmas
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
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt16;
extern lean_object* l_instPowUInt32Nat;
static lean_object* l_Lean_Grind_instCommRingUInt8___closed__1;
static lean_object* l_Lean_Grind_instCommRingUInt64___closed__1;
extern lean_object* l_instMulUInt64;
static lean_object* l_Lean_Grind_instCommRingUInt32___closed__3;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt8;
uint16_t l_UInt16_ofInt(lean_object*);
extern lean_object* l_instAddUInt64;
static lean_object* l_Lean_Grind_instCommRingUSize___closed__2;
uint64_t l_UInt64_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_instIntCast___boxed(lean_object*);
extern lean_object* l_instMulUInt16;
LEAN_EXPORT lean_object* l_UInt64_instIntCast___boxed(lean_object*);
extern lean_object* l_instAddUInt16;
LEAN_EXPORT lean_object* l_UInt16_instIntCast___boxed(lean_object*);
uint32_t l_UInt32_ofInt(lean_object*);
lean_object* l_USize_instOfNat___boxed(lean_object*);
static lean_object* l_Lean_Grind_instCommRingUSize___closed__3;
LEAN_EXPORT size_t l_USize_instIntCast(lean_object*);
static lean_object* l_Lean_Grind_instCommRingUInt16___closed__2;
extern lean_object* l_instPowUInt8Nat;
extern lean_object* l_instMulUInt32;
lean_object* l_UInt32_instOfNat___boxed(lean_object*);
lean_object* l_UInt64_instOfNat___boxed(lean_object*);
size_t l_USize_ofInt(lean_object*);
extern lean_object* l_instSubUInt32;
extern lean_object* l_instAddUInt32;
LEAN_EXPORT uint64_t l_UInt64_instIntCast(lean_object*);
uint8_t l_UInt8_ofInt(lean_object*);
extern lean_object* l_instSubUInt8;
extern lean_object* l_instAddUInt8;
extern lean_object* l_instMulUSize;
extern lean_object* l_instNegUInt32;
static lean_object* l_Lean_Grind_instCommRingUInt32___closed__1;
LEAN_EXPORT lean_object* l_USize_instIntCast___boxed(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_instIntCast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64;
static lean_object* l_Lean_Grind_instCommRingUSize___closed__1;
extern lean_object* l_instNegUInt16;
LEAN_EXPORT lean_object* l_UInt8_instIntCast___boxed(lean_object*);
extern lean_object* l_instSubUInt64;
static lean_object* l_Lean_Grind_instCommRingUInt64___closed__2;
extern lean_object* l_instNegUInt8;
static lean_object* l_Lean_Grind_instCommRingUInt8___closed__2;
extern lean_object* l_instNegUSize;
static lean_object* l_Lean_Grind_instCommRingUInt16___closed__3;
extern lean_object* l_instPowUInt16Nat;
static lean_object* l_Lean_Grind_instCommRingUInt8___closed__3;
extern lean_object* l_instMulUInt8;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32;
static lean_object* l_Lean_Grind_instCommRingUInt32___closed__2;
static lean_object* l_Lean_Grind_instCommRingUInt16___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize;
extern lean_object* l_instPowUInt64Nat;
LEAN_EXPORT uint8_t l_UInt8_instIntCast(lean_object*);
lean_object* l_UInt16_instOfNat___boxed(lean_object*);
extern lean_object* l_instSubUSize;
extern lean_object* l_instSubUInt16;
lean_object* l_UInt8_instOfNat___boxed(lean_object*);
extern lean_object* l_instPowUSizeNat;
extern lean_object* l_instAddUSize;
static lean_object* l_Lean_Grind_instCommRingUInt64___closed__3;
extern lean_object* l_instNegUInt64;
lean_object* l_instHPow___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_UInt16_instIntCast(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instIntCast(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_UInt8_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UInt8_instIntCast___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_UInt8_instIntCast(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint16_t l_UInt16_instIntCast(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = l_UInt16_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UInt16_instIntCast___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_UInt16_instIntCast(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_UInt32_instIntCast(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = l_UInt32_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UInt32_instIntCast___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_UInt32_instIntCast(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_UInt64_instIntCast(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_UInt64_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UInt64_instIntCast___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_UInt64_instIntCast(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_USize_instIntCast(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = l_USize_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_USize_instIntCast___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_USize_instIntCast(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowUInt8Nat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddUInt8;
x_2 = l_instMulUInt8;
x_3 = l_instNegUInt8;
x_4 = l_instSubUInt8;
x_5 = l_Lean_Grind_instCommRingUInt8___closed__1;
x_6 = l_Lean_Grind_instCommRingUInt8___closed__2;
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
static lean_object* _init_l_Lean_Grind_instCommRingUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUInt8___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt16___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowUInt16Nat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt16___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt16___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddUInt16;
x_2 = l_instMulUInt16;
x_3 = l_instNegUInt16;
x_4 = l_instSubUInt16;
x_5 = l_Lean_Grind_instCommRingUInt16___closed__1;
x_6 = l_Lean_Grind_instCommRingUInt16___closed__2;
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
static lean_object* _init_l_Lean_Grind_instCommRingUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUInt16___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt32___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowUInt32Nat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt32___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt32___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddUInt32;
x_2 = l_instMulUInt32;
x_3 = l_instNegUInt32;
x_4 = l_instSubUInt32;
x_5 = l_Lean_Grind_instCommRingUInt32___closed__1;
x_6 = l_Lean_Grind_instCommRingUInt32___closed__2;
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
static lean_object* _init_l_Lean_Grind_instCommRingUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUInt32___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt64___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowUInt64Nat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt64___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt64___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddUInt64;
x_2 = l_instMulUInt64;
x_3 = l_instNegUInt64;
x_4 = l_instSubUInt64;
x_5 = l_Lean_Grind_instCommRingUInt64___closed__1;
x_6 = l_Lean_Grind_instCommRingUInt64___closed__2;
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
static lean_object* _init_l_Lean_Grind_instCommRingUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUInt64___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUSize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instPowUSizeNat;
x_2 = lean_alloc_closure((void*)(l_instHPow___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUSize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_instOfNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUSize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_instAddUSize;
x_2 = l_instMulUSize;
x_3 = l_instNegUSize;
x_4 = l_instSubUSize;
x_5 = l_Lean_Grind_instCommRingUSize___closed__1;
x_6 = l_Lean_Grind_instCommRingUSize___closed__2;
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
static lean_object* _init_l_Lean_Grind_instCommRingUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUSize___closed__3;
return x_1;
}
}
lean_object* initialize_Init_Grind_CommRing_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_CommRing_UInt(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_CommRing_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instCommRingUInt8___closed__1 = _init_l_Lean_Grind_instCommRingUInt8___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt8___closed__1);
l_Lean_Grind_instCommRingUInt8___closed__2 = _init_l_Lean_Grind_instCommRingUInt8___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt8___closed__2);
l_Lean_Grind_instCommRingUInt8___closed__3 = _init_l_Lean_Grind_instCommRingUInt8___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt8___closed__3);
l_Lean_Grind_instCommRingUInt8 = _init_l_Lean_Grind_instCommRingUInt8();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt8);
l_Lean_Grind_instCommRingUInt16___closed__1 = _init_l_Lean_Grind_instCommRingUInt16___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt16___closed__1);
l_Lean_Grind_instCommRingUInt16___closed__2 = _init_l_Lean_Grind_instCommRingUInt16___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt16___closed__2);
l_Lean_Grind_instCommRingUInt16___closed__3 = _init_l_Lean_Grind_instCommRingUInt16___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt16___closed__3);
l_Lean_Grind_instCommRingUInt16 = _init_l_Lean_Grind_instCommRingUInt16();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt16);
l_Lean_Grind_instCommRingUInt32___closed__1 = _init_l_Lean_Grind_instCommRingUInt32___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt32___closed__1);
l_Lean_Grind_instCommRingUInt32___closed__2 = _init_l_Lean_Grind_instCommRingUInt32___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt32___closed__2);
l_Lean_Grind_instCommRingUInt32___closed__3 = _init_l_Lean_Grind_instCommRingUInt32___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt32___closed__3);
l_Lean_Grind_instCommRingUInt32 = _init_l_Lean_Grind_instCommRingUInt32();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt32);
l_Lean_Grind_instCommRingUInt64___closed__1 = _init_l_Lean_Grind_instCommRingUInt64___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt64___closed__1);
l_Lean_Grind_instCommRingUInt64___closed__2 = _init_l_Lean_Grind_instCommRingUInt64___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt64___closed__2);
l_Lean_Grind_instCommRingUInt64___closed__3 = _init_l_Lean_Grind_instCommRingUInt64___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt64___closed__3);
l_Lean_Grind_instCommRingUInt64 = _init_l_Lean_Grind_instCommRingUInt64();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt64);
l_Lean_Grind_instCommRingUSize___closed__1 = _init_l_Lean_Grind_instCommRingUSize___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUSize___closed__1);
l_Lean_Grind_instCommRingUSize___closed__2 = _init_l_Lean_Grind_instCommRingUSize___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingUSize___closed__2);
l_Lean_Grind_instCommRingUSize___closed__3 = _init_l_Lean_Grind_instCommRingUSize___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingUSize___closed__3);
l_Lean_Grind_instCommRingUSize = _init_l_Lean_Grind_instCommRingUSize();
lean_mark_persistent(l_Lean_Grind_instCommRingUSize);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
