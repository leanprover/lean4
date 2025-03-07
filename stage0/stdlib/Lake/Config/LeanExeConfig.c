// Lean compiler output
// Module: Lake.Config.LeanExeConfig
// Imports: Lake.Build.Facets Lake.Config.LeanConfig
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_instInhabitedLeanExeConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_instInhabitedLeanExeConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1(uint8_t);
static lean_object* l_Lake_instInhabitedLeanExeConfig___closed__4;
static lean_object* l_Lake_instInhabitedLeanExeConfig___closed__1;
static lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig;
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1;
x_4 = 2;
x_5 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_3);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_1);
lean_ctor_set(x_5, 9, x_3);
lean_ctor_set(x_5, 10, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*11, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*11 + 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instInhabitedLeanExeConfig___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lake_instInhabitedLeanExeConfig___closed__1;
x_2 = lean_box(0);
x_3 = l_Lake_instInhabitedLeanExeConfig___closed__2;
x_4 = l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1;
x_5 = 0;
x_6 = l_Lake_instInhabitedLeanExeConfig___closed__3;
x_7 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_2);
lean_ctor_set(x_7, 4, x_3);
lean_ctor_set(x_7, 5, x_4);
lean_ctor_set(x_7, 6, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*7, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLeanExeConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_instInhabitedLeanExeConfig___lambda__1(x_2);
return x_3;
}
}
lean_object* initialize_Lake_Build_Facets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_LeanConfig(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_LeanExeConfig(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Facets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1 = _init_l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1);
l_Lake_instInhabitedLeanExeConfig___closed__1 = _init_l_Lake_instInhabitedLeanExeConfig___closed__1();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___closed__1);
l_Lake_instInhabitedLeanExeConfig___closed__2 = _init_l_Lake_instInhabitedLeanExeConfig___closed__2();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___closed__2);
l_Lake_instInhabitedLeanExeConfig___closed__3 = _init_l_Lake_instInhabitedLeanExeConfig___closed__3();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___closed__3);
l_Lake_instInhabitedLeanExeConfig___closed__4 = _init_l_Lake_instInhabitedLeanExeConfig___closed__4();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___closed__4);
l_Lake_instInhabitedLeanExeConfig = _init_l_Lake_instInhabitedLeanExeConfig();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
