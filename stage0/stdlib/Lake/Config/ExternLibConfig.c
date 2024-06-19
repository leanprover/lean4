// Lean compiler output
// Module: Lake.Config.ExternLibConfig
// Imports: Init Lake.Build.Job Lake.Build.Data
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
static lean_object* l_Lake_instInhabitedExternLibConfig___closed__3;
static lean_object* l_Lake_instInhabitedExternLibConfig___closed__7;
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
static lean_object* l_Lake_instInhabitedExternLibConfig___closed__5;
static lean_object* l_Lake_instInhabitedExternLibConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_BuildTrace_nil;
static lean_object* l_Lake_instInhabitedExternLibConfig___closed__4;
static lean_object* l_Lake_instInhabitedExternLibConfig___closed__6;
static lean_object* l_Lake_instInhabitedExternLibConfig___closed__2;
static lean_object* _init_l_Lake_instInhabitedExternLibConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedExternLibConfig___closed__1;
x_2 = l_Lake_BuildTrace_nil;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedExternLibConfig___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedExternLibConfig___closed__2;
x_2 = l_Lake_instInhabitedExternLibConfig___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instInhabitedExternLibConfig___closed__5;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedExternLibConfig___closed__6;
x_2 = l_Lake_instInhabitedExternLibConfig___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instInhabitedExternLibConfig___closed__7;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instInhabitedExternLibConfig(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Data(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_ExternLibConfig(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Data(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedExternLibConfig___closed__1 = _init_l_Lake_instInhabitedExternLibConfig___closed__1();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig___closed__1);
l_Lake_instInhabitedExternLibConfig___closed__2 = _init_l_Lake_instInhabitedExternLibConfig___closed__2();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig___closed__2);
l_Lake_instInhabitedExternLibConfig___closed__3 = _init_l_Lake_instInhabitedExternLibConfig___closed__3();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig___closed__3);
l_Lake_instInhabitedExternLibConfig___closed__4 = _init_l_Lake_instInhabitedExternLibConfig___closed__4();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig___closed__4);
l_Lake_instInhabitedExternLibConfig___closed__5 = _init_l_Lake_instInhabitedExternLibConfig___closed__5();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig___closed__5);
l_Lake_instInhabitedExternLibConfig___closed__6 = _init_l_Lake_instInhabitedExternLibConfig___closed__6();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig___closed__6);
l_Lake_instInhabitedExternLibConfig___closed__7 = _init_l_Lake_instInhabitedExternLibConfig___closed__7();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
