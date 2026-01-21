// Lean compiler output
// Module: Lake.Config.Script
// Imports: public import Init.Dynamic public import Init.System.IO public import Lake.Util.Exit public import Lake.Config.Context
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
static lean_object* l_Lake_instInhabitedScript_default___closed__2;
static lean_object* l_Lake_instTypeNameScriptFn_unsafe__1___closed__2;
static lean_object* l_Lake_instTypeNameScriptFn_unsafe__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript;
LEAN_EXPORT lean_object* l_Lake_instTypeNameScriptFn_unsafe__1;
LEAN_EXPORT lean_object* l_Lake_Script_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedScript_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default;
static lean_object* l_Lake_instInhabitedScript_default___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedScript_default___closed__0;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instTypeNameScriptFn;
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedScript_default___lam__0___closed__0;
static lean_object* l_Lake_instTypeNameScriptFn_unsafe__1___closed__0;
static lean_object* _init_l_Lake_instTypeNameScriptFn_unsafe__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instTypeNameScriptFn_unsafe__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ScriptFn", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_instTypeNameScriptFn_unsafe__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instTypeNameScriptFn_unsafe__1___closed__1;
x_2 = l_Lake_instTypeNameScriptFn_unsafe__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instTypeNameScriptFn_unsafe__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instTypeNameScriptFn_unsafe__1___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_instTypeNameScriptFn() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instTypeNameScriptFn_unsafe__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedScript_default___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(`Inhabited.default` for `IO.Error`)", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedScript_default___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instInhabitedScript_default___lam__0___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_instInhabitedScript_default___lam__0___closed__1;
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instInhabitedScript_default___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedScript_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instInhabitedScript_default___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedScript_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedScript_default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_instInhabitedScript_default___closed__0;
x_3 = l_Lake_instInhabitedScript_default___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedScript_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedScript_default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedScript() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedScript_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Script_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_3(x_5, x_1, x_3, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Script_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Script_run(x_1, x_2, x_3);
return x_5;
}
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin);
lean_object* initialize_Lake_Config_Context(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Script(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instTypeNameScriptFn_unsafe__1___closed__0 = _init_l_Lake_instTypeNameScriptFn_unsafe__1___closed__0();
lean_mark_persistent(l_Lake_instTypeNameScriptFn_unsafe__1___closed__0);
l_Lake_instTypeNameScriptFn_unsafe__1___closed__1 = _init_l_Lake_instTypeNameScriptFn_unsafe__1___closed__1();
lean_mark_persistent(l_Lake_instTypeNameScriptFn_unsafe__1___closed__1);
l_Lake_instTypeNameScriptFn_unsafe__1___closed__2 = _init_l_Lake_instTypeNameScriptFn_unsafe__1___closed__2();
lean_mark_persistent(l_Lake_instTypeNameScriptFn_unsafe__1___closed__2);
l_Lake_instTypeNameScriptFn_unsafe__1 = _init_l_Lake_instTypeNameScriptFn_unsafe__1();
lean_mark_persistent(l_Lake_instTypeNameScriptFn_unsafe__1);
l_Lake_instTypeNameScriptFn = _init_l_Lake_instTypeNameScriptFn();
lean_mark_persistent(l_Lake_instTypeNameScriptFn);
l_Lake_instInhabitedScript_default___lam__0___closed__0 = _init_l_Lake_instInhabitedScript_default___lam__0___closed__0();
lean_mark_persistent(l_Lake_instInhabitedScript_default___lam__0___closed__0);
l_Lake_instInhabitedScript_default___lam__0___closed__1 = _init_l_Lake_instInhabitedScript_default___lam__0___closed__1();
lean_mark_persistent(l_Lake_instInhabitedScript_default___lam__0___closed__1);
l_Lake_instInhabitedScript_default___closed__0 = _init_l_Lake_instInhabitedScript_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedScript_default___closed__0);
l_Lake_instInhabitedScript_default___closed__1 = _init_l_Lake_instInhabitedScript_default___closed__1();
lean_mark_persistent(l_Lake_instInhabitedScript_default___closed__1);
l_Lake_instInhabitedScript_default___closed__2 = _init_l_Lake_instInhabitedScript_default___closed__2();
lean_mark_persistent(l_Lake_instInhabitedScript_default___closed__2);
l_Lake_instInhabitedScript_default = _init_l_Lake_instInhabitedScript_default();
lean_mark_persistent(l_Lake_instInhabitedScript_default);
l_Lake_instInhabitedScript = _init_l_Lake_instInhabitedScript();
lean_mark_persistent(l_Lake_instInhabitedScript);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
