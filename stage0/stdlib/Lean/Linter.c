// Lean compiler output
// Module: Lean.Linter
// Imports: Lean.Linter.Util Lean.Linter.Builtin Lean.Linter.ConstructorAsVariable Lean.Linter.Deprecated Lean.Linter.UnusedVariables Lean.Linter.MissingDocs Lean.Linter.Omit Lean.Linter.List
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
lean_object* initialize_Lean_Linter_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_Builtin(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_ConstructorAsVariable(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_UnusedVariables(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_MissingDocs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_Omit(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_List(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Builtin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_ConstructorAsVariable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_UnusedVariables(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_MissingDocs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Omit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
