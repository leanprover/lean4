// Lean compiler output
// Module: Init.System.Platform
// Imports: public import Init.Data.Nat.Div.Basic public import Init.SimpLemmas import Init.Data.Nat.Basic import Init.Data.String.Bootstrap
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
uint8_t lean_system_platform_windows(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsWindows___boxed(lean_object*);
uint8_t lean_system_platform_osx(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsOSX___boxed(lean_object*);
uint8_t lean_system_platform_emscripten(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsEmscripten___boxed(lean_object*);
static lean_once_cell_t l_System_Platform_isWindows___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_Platform_isWindows___closed__0;
LEAN_EXPORT uint8_t l_System_Platform_isWindows;
static lean_once_cell_t l_System_Platform_isOSX___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_Platform_isOSX___closed__0;
LEAN_EXPORT uint8_t l_System_Platform_isOSX;
static lean_once_cell_t l_System_Platform_isEmscripten___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_Platform_isEmscripten___closed__0;
LEAN_EXPORT uint8_t l_System_Platform_isEmscripten;
lean_object* lean_system_platform_target(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getTarget___boxed(lean_object*);
static lean_once_cell_t l_System_Platform_target___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Platform_target___closed__0;
LEAN_EXPORT lean_object* l_System_Platform_target;
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
static uint8_t _init_l_System_Platform_isWindows___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_windows(x_1);
return x_2;
}
}
static uint8_t _init_l_System_Platform_isWindows(void) {
_start:
{
uint8_t x_1; 
x_1 = lean_uint8_once(&l_System_Platform_isWindows___closed__0, &l_System_Platform_isWindows___closed__0_once, _init_l_System_Platform_isWindows___closed__0);
return x_1;
}
}
static uint8_t _init_l_System_Platform_isOSX___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_osx(x_1);
return x_2;
}
}
static uint8_t _init_l_System_Platform_isOSX(void) {
_start:
{
uint8_t x_1; 
x_1 = lean_uint8_once(&l_System_Platform_isOSX___closed__0, &l_System_Platform_isOSX___closed__0_once, _init_l_System_Platform_isOSX___closed__0);
return x_1;
}
}
static uint8_t _init_l_System_Platform_isEmscripten___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_emscripten(x_1);
return x_2;
}
}
static uint8_t _init_l_System_Platform_isEmscripten(void) {
_start:
{
uint8_t x_1; 
x_1 = lean_uint8_once(&l_System_Platform_isEmscripten___closed__0, &l_System_Platform_isEmscripten___closed__0_once, _init_l_System_Platform_isEmscripten___closed__0);
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
static lean_object* _init_l_System_Platform_target___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_system_platform_target(x_1);
return x_2;
}
}
static lean_object* _init_l_System_Platform_target(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_System_Platform_target___closed__0, &l_System_Platform_target___closed__0_once, _init_l_System_Platform_target___closed__0);
return x_1;
}
}
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Platform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_Platform_isWindows = _init_l_System_Platform_isWindows();
l_System_Platform_isOSX = _init_l_System_Platform_isOSX();
l_System_Platform_isEmscripten = _init_l_System_Platform_isEmscripten();
l_System_Platform_target = _init_l_System_Platform_target();
lean_mark_persistent(l_System_Platform_target);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
