// Lean compiler output
// Module: Lake.Config.Opaque
// Imports: Init Lake.Util.Name Lake.Util.Opaque
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
LEAN_EXPORT lean_object* l_Lake_OpaqueTargetConfig_nonemptyType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_nonemptyType;
LEAN_EXPORT lean_object* l_Lake_OpaqueTargetConfig_nonemptyType(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_OpaqueWorkspace_nonemptyType() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueTargetConfig_nonemptyType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueTargetConfig_nonemptyType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_OpaqueTargetConfig_nonemptyType(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Opaque(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Opaque(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Opaque(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_OpaqueWorkspace_nonemptyType = _init_l_Lake_OpaqueWorkspace_nonemptyType();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
