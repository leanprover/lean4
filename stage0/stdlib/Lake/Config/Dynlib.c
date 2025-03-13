// Lean compiler output
// Module: Lake.Config.Dynlib
// Imports: Lake.Config.OutFormat
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
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_System_FilePath_parent(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Dynlib_dir_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToTextDynlib(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToJsonDynlib(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lake_Config_OutFormat(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_OutFormat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
