// Lean compiler output
// Module: Lake.Config.ExternLibConfig
// Imports: public import Lake.Build.Job.Basic
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
static lean_object* l_Lake_instInhabitedExternLibConfig_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig_default___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
static lean_object* l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2;
static lean_object* l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0;
extern lean_object* l_Lake_instInhabitedJobState_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig_default___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig_default___lam__0___boxed(lean_object*);
static lean_object* l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1;
extern lean_object* l_Lake_Log_instInhabitedPos_default;
static lean_object* _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedJobState_default;
x_2 = l_Lake_Log_instInhabitedPos_default;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2;
x_3 = lean_box(0);
x_4 = l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig_default___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig_default___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedExternLibConfig_default___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedExternLibConfig_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instInhabitedExternLibConfig_default___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedExternLibConfig_default___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig_default___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedExternLibConfig_default(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedExternLibConfig_default___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedExternLibConfig___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedExternLibConfig(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_ExternLibConfig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0 = _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0);
l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1 = _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1);
l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2 = _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2);
l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3 = _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3);
l_Lake_instInhabitedExternLibConfig_default___closed__0 = _init_l_Lake_instInhabitedExternLibConfig_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedExternLibConfig_default___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
