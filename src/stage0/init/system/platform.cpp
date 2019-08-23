// Lean compiler output
// Module: init.system.platform
// Imports: init.data.nat.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" {
obj* l_System_Platform_getNumBits___boxed(obj*);
obj* l_System_Platform_numBits___closed__1;
uint8 l_System_Platform_isWindows___closed__1;
uint8 l_System_Platform_isWindows;
obj* l_System_Platform_getIsOSX___boxed(obj*);
uint8 l_System_Platform_isOSX___closed__1;
uint8 lean_system_platform_osx(obj*);
uint8 l_System_Platform_isOSX;
obj* lean_system_platform_nbits(obj*);
obj* l_System_Platform_numBits;
uint8 lean_system_platform_windows(obj*);
obj* l_System_Platform_getIsWindows___boxed(obj*);
obj* l_System_Platform_getNumBits___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_system_platform_nbits(x_1);
return x_2;
}
}
obj* l_System_Platform_getIsWindows___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean_system_platform_windows(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_System_Platform_getIsOSX___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean_system_platform_osx(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_System_Platform_numBits___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean_system_platform_nbits(x_1);
return x_2;
}
}
obj* _init_l_System_Platform_numBits() {
_start:
{
obj* x_1; 
x_1 = l_System_Platform_numBits___closed__1;
return x_1;
}
}
uint8 _init_l_System_Platform_isWindows___closed__1() {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::box(0);
x_2 = lean_system_platform_windows(x_1);
return x_2;
}
}
uint8 _init_l_System_Platform_isWindows() {
_start:
{
uint8 x_1; 
x_1 = l_System_Platform_isWindows___closed__1;
return x_1;
}
}
uint8 _init_l_System_Platform_isOSX___closed__1() {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::box(0);
x_2 = lean_system_platform_osx(x_1);
return x_2;
}
}
uint8 _init_l_System_Platform_isOSX() {
_start:
{
uint8 x_1; 
x_1 = l_System_Platform_isOSX___closed__1;
return x_1;
}
}
obj* initialize_init_data_nat_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_system_platform(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (lean::io_result_is_error(w)) return w;
l_System_Platform_numBits___closed__1 = _init_l_System_Platform_numBits___closed__1();
lean::mark_persistent(l_System_Platform_numBits___closed__1);
l_System_Platform_numBits = _init_l_System_Platform_numBits();
lean::mark_persistent(l_System_Platform_numBits);
l_System_Platform_isWindows___closed__1 = _init_l_System_Platform_isWindows___closed__1();
l_System_Platform_isWindows = _init_l_System_Platform_isWindows();
l_System_Platform_isOSX___closed__1 = _init_l_System_Platform_isOSX___closed__1();
l_System_Platform_isOSX = _init_l_System_Platform_isOSX();
return w;
}
}
