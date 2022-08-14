// Lean compiler output
// Module: Lean.Compiler.Simp
// Imports: Init Lean.Compiler.CompilerM Lean.Compiler.Decl
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
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_State_unit___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Config_increaseFactor___default;
static lean_object* _init_l_Lean_Compiler_Simp_Config_increaseFactor___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_State_unit___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Decl(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Decl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_Simp_Config_increaseFactor___default = _init_l_Lean_Compiler_Simp_Config_increaseFactor___default();
lean_mark_persistent(l_Lean_Compiler_Simp_Config_increaseFactor___default);
l_Lean_Compiler_Simp_State_unit___default = _init_l_Lean_Compiler_Simp_State_unit___default();
lean_mark_persistent(l_Lean_Compiler_Simp_State_unit___default);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
