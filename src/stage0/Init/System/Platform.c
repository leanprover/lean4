// Lean compiler output
// Module: Init.System.Platform
// Imports: Init.Data.Nat.Basic
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
lean_object* l_System_Platform_getNumBits___boxed(lean_object*);
lean_object* l_System_Platform_numBits___closed__1;
uint8_t l_System_Platform_isWindows___closed__1;
uint8_t l_System_Platform_isWindows;
lean_object* l_System_Platform_getIsOSX___boxed(lean_object*);
uint8_t l_System_Platform_isOSX___closed__1;
uint8_t lean_system_platform_osx(lean_object*);
uint8_t l_System_Platform_isOSX;
lean_object* lean_system_platform_nbits(lean_object*);
lean_object* l_System_Platform_numBits;
uint8_t lean_system_platform_windows(lean_object*);
lean_object* l_System_Platform_getIsWindows___boxed(lean_object*);
lean_object* l_System_Platform_getNumBits___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_system_platform_nbits(x_1);
return x_2;
}
}
lean_object* l_System_Platform_getIsWindows___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_system_platform_windows(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_System_Platform_getIsOSX___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_system_platform_osx(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_System_Platform_numBits___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_nbits(x_1);
return x_2;
}
}
lean_object* _init_l_System_Platform_numBits() {
_start:
{
lean_object* x_1; 
x_1 = l_System_Platform_numBits___closed__1;
return x_1;
}
}
uint8_t _init_l_System_Platform_isWindows___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_windows(x_1);
return x_2;
}
}
uint8_t _init_l_System_Platform_isWindows() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows___closed__1;
return x_1;
}
}
uint8_t _init_l_System_Platform_isOSX___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_osx(x_1);
return x_2;
}
}
uint8_t _init_l_System_Platform_isOSX() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isOSX___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Data_Nat_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_System_Platform(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Nat_Basic(w);
if (lean_io_result_is_error(w)) return w;
l_System_Platform_numBits___closed__1 = _init_l_System_Platform_numBits___closed__1();
lean_mark_persistent(l_System_Platform_numBits___closed__1);
l_System_Platform_numBits = _init_l_System_Platform_numBits();
lean_mark_persistent(l_System_Platform_numBits);
l_System_Platform_isWindows___closed__1 = _init_l_System_Platform_isWindows___closed__1();
l_System_Platform_isWindows = _init_l_System_Platform_isWindows();
l_System_Platform_isOSX___closed__1 = _init_l_System_Platform_isOSX___closed__1();
l_System_Platform_isOSX = _init_l_System_Platform_isOSX();
return w;
}
#ifdef __cplusplus
}
#endif
