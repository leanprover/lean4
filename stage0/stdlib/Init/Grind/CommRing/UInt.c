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
static lean_object* l_Lean_Grind_instCommRingUInt8___closed__1;
static lean_object* l_Lean_Grind_instCommRingUInt64___closed__1;
extern lean_object* l_instMulUInt64;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt8;
extern lean_object* l_instAddUInt64;
extern lean_object* l_instMulUInt16;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__2;
extern lean_object* l_instAddUInt16;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__2;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__2;
extern lean_object* l_instMulUInt32;
extern lean_object* l_instAddUInt32;
extern lean_object* l_instAddUInt8;
extern lean_object* l_instMulUSize;
extern lean_object* l_instNegUInt32;
static lean_object* l_Lean_Grind_instCommRingUInt32___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64;
static lean_object* l_Lean_Grind_instCommRingUSize___closed__1;
extern lean_object* l_instNegUInt16;
extern lean_object* l_instNegUInt8;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__1;
extern lean_object* l_instNegUSize;
extern lean_object* l_instMulUInt8;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32;
static lean_object* l_Lean_Grind_instCommRingUInt16___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__1;
extern lean_object* l_instAddUSize;
extern lean_object* l_instNegUInt64;
static lean_object* _init_l_Lean_Grind_instCommRingUInt8___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = 0;
x_2 = 1;
x_3 = l_instAddUInt8;
x_4 = l_instMulUInt8;
x_5 = l_instNegUInt8;
x_6 = lean_box(x_1);
x_7 = lean_box(x_2);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt16___closed__1() {
_start:
{
uint16_t x_1; uint16_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = 0;
x_2 = 1;
x_3 = l_instAddUInt16;
x_4 = l_instMulUInt16;
x_5 = l_instNegUInt16;
x_6 = lean_box(x_1);
x_7 = lean_box(x_2);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt32___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_instAddUInt32;
x_2 = l_instMulUInt32;
x_3 = l_instNegUInt32;
x_4 = l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__1;
x_5 = l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__2;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set(x_6, 4, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__2() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt64___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_instAddUInt64;
x_2 = l_instMulUInt64;
x_3 = l_instNegUInt64;
x_4 = l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__1;
x_5 = l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__2;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set(x_6, 4, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__2() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUSize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_instAddUSize;
x_2 = l_instMulUSize;
x_3 = l_instNegUSize;
x_4 = l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__1;
x_5 = l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__2;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set(x_6, 4, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingUSize___closed__1;
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
l_Lean_Grind_instCommRingUInt8 = _init_l_Lean_Grind_instCommRingUInt8();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt8);
l_Lean_Grind_instCommRingUInt16___closed__1 = _init_l_Lean_Grind_instCommRingUInt16___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt16___closed__1);
l_Lean_Grind_instCommRingUInt16 = _init_l_Lean_Grind_instCommRingUInt16();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt16);
l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__1 = _init_l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__1);
l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__2 = _init_l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__2();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt32___closed__1___boxed__const__2);
l_Lean_Grind_instCommRingUInt32___closed__1 = _init_l_Lean_Grind_instCommRingUInt32___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt32___closed__1);
l_Lean_Grind_instCommRingUInt32 = _init_l_Lean_Grind_instCommRingUInt32();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt32);
l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__1 = _init_l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__1);
l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__2 = _init_l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__2();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt64___closed__1___boxed__const__2);
l_Lean_Grind_instCommRingUInt64___closed__1 = _init_l_Lean_Grind_instCommRingUInt64___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt64___closed__1);
l_Lean_Grind_instCommRingUInt64 = _init_l_Lean_Grind_instCommRingUInt64();
lean_mark_persistent(l_Lean_Grind_instCommRingUInt64);
l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__1 = _init_l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__1);
l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__2 = _init_l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__2();
lean_mark_persistent(l_Lean_Grind_instCommRingUSize___closed__1___boxed__const__2);
l_Lean_Grind_instCommRingUSize___closed__1 = _init_l_Lean_Grind_instCommRingUSize___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingUSize___closed__1);
l_Lean_Grind_instCommRingUSize = _init_l_Lean_Grind_instCommRingUSize();
lean_mark_persistent(l_Lean_Grind_instCommRingUSize);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
