// Lean compiler output
// Module: Init.System.Platform
// Imports: Init.Data.Nat.Basic Init.Data.String.Basic
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
static uint8_t l_System_Platform_isWindows___closed__0;
LEAN_EXPORT uint8_t l_System_Platform_isOSX;
uint8_t lean_system_platform_windows(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsEmscripten___boxed(lean_object*);
static uint8_t l_System_Platform_isEmscripten___closed__0;
static lean_object* l_System_Platform_target___closed__0;
uint8_t lean_system_platform_emscripten(lean_object*);
LEAN_EXPORT uint8_t l_System_Platform_isEmscripten;
static uint8_t l_System_Platform_isOSX___closed__0;
LEAN_EXPORT lean_object* l_System_Platform_getIsWindows___boxed(lean_object*);
uint8_t lean_system_platform_osx(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_target;
LEAN_EXPORT uint8_t l_System_Platform_isWindows;
lean_object* lean_system_platform_target(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsOSX___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsWindows___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_system_platform_windows(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_Platform_getIsOSX___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_system_platform_osx(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_Platform_getIsEmscripten___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_system_platform_emscripten(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint8_t _init_l_System_Platform_isWindows___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_windows(x_1);
return x_2;
}
}
static uint8_t _init_l_System_Platform_isWindows() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows___closed__0;
return x_1;
}
}
static uint8_t _init_l_System_Platform_isOSX___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_osx(x_1);
return x_2;
}
}
static uint8_t _init_l_System_Platform_isOSX() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isOSX___closed__0;
return x_1;
}
}
static uint8_t _init_l_System_Platform_isEmscripten___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_emscripten(x_1);
return x_2;
}
}
static uint8_t _init_l_System_Platform_isEmscripten() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isEmscripten___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_Platform_getTarget___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_system_platform_target(x_1);
return x_2;
}
}
static lean_object* _init_l_System_Platform_target___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_target(x_1);
return x_2;
}
}
static lean_object* _init_l_System_Platform_target() {
_start:
{
lean_object* x_1; 
x_1 = l_System_Platform_target___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Platform(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_Platform_isWindows___closed__0 = _init_l_System_Platform_isWindows___closed__0();
l_System_Platform_isWindows = _init_l_System_Platform_isWindows();
l_System_Platform_isOSX___closed__0 = _init_l_System_Platform_isOSX___closed__0();
l_System_Platform_isOSX = _init_l_System_Platform_isOSX();
l_System_Platform_isEmscripten___closed__0 = _init_l_System_Platform_isEmscripten___closed__0();
l_System_Platform_isEmscripten = _init_l_System_Platform_isEmscripten();
l_System_Platform_target___closed__0 = _init_l_System_Platform_target___closed__0();
lean_mark_persistent(l_System_Platform_target___closed__0);
l_System_Platform_target = _init_l_System_Platform_target();
lean_mark_persistent(l_System_Platform_target);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
