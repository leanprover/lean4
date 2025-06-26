// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Config
// Imports: Init.Core
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
static lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedConfig;
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 0, 4);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 3, x_6);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_Config(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__0);
l_Lean_Compiler_LCNF_Simp_instInhabitedConfig = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedConfig();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedConfig);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
