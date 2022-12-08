// Lean compiler output
// Module: Lean.Elab.Tactic.Conv
// Imports: Init Lean.Elab.Tactic.Conv.Basic Lean.Elab.Tactic.Conv.Congr Lean.Elab.Tactic.Conv.Rewrite Lean.Elab.Tactic.Conv.Change Lean.Elab.Tactic.Conv.Simp Lean.Elab.Tactic.Conv.Pattern Lean.Elab.Tactic.Conv.Delta Lean.Elab.Tactic.Conv.Unfold
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Congr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Change(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Pattern(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Delta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Unfold(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Congr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Change(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Pattern(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Delta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Unfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
