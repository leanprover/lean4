// Lean compiler output
// Module: Lake.Config.Script
// Imports: Init Lake.Util.Exit Lake.Config.Context
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
static uint32_t l_Lake_instInhabitedScript___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript;
static lean_object* l_Lake_instInhabitedScript___lambda__1___closed__3;
static lean_object* l_Lake_instInhabitedScript___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedScript___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedScript___closed__1;
uint32_t lean_uint32_of_nat(lean_object*);
static uint32_t _init_l_Lake_instInhabitedScript___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedScript___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedScript___lambda__1___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_instInhabitedScript___lambda__1___closed__1;
x_3 = l_Lake_instInhabitedScript___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_instInhabitedScript___lambda__1___closed__3;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedScript___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instInhabitedScript___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedScript___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_instInhabitedScript___lambda__1___closed__2;
x_3 = l_Lake_instInhabitedScript___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedScript() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedScript___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instInhabitedScript___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Script_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_3(x_5, x_1, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Context(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Script(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Context(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedScript___lambda__1___closed__1 = _init_l_Lake_instInhabitedScript___lambda__1___closed__1();
l_Lake_instInhabitedScript___lambda__1___closed__2 = _init_l_Lake_instInhabitedScript___lambda__1___closed__2();
lean_mark_persistent(l_Lake_instInhabitedScript___lambda__1___closed__2);
l_Lake_instInhabitedScript___lambda__1___closed__3 = _init_l_Lake_instInhabitedScript___lambda__1___closed__3();
lean_mark_persistent(l_Lake_instInhabitedScript___lambda__1___closed__3);
l_Lake_instInhabitedScript___closed__1 = _init_l_Lake_instInhabitedScript___closed__1();
lean_mark_persistent(l_Lake_instInhabitedScript___closed__1);
l_Lake_instInhabitedScript___closed__2 = _init_l_Lake_instInhabitedScript___closed__2();
lean_mark_persistent(l_Lake_instInhabitedScript___closed__2);
l_Lake_instInhabitedScript = _init_l_Lake_instInhabitedScript();
lean_mark_persistent(l_Lake_instInhabitedScript);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
