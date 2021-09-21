// Lean compiler output
// Module: Lean.Elab.Tactic
// Imports: Init Lean.Elab.Term Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Induction Lean.Elab.Tactic.Generalize Lean.Elab.Tactic.Injection Lean.Elab.Tactic.Match Lean.Elab.Tactic.Rewrite Lean.Elab.Tactic.Location Lean.Elab.Tactic.Simp Lean.Elab.Tactic.BuiltinTactic Lean.Elab.Tactic.Split Lean.Elab.Tactic.Conv Lean.Elab.Tactic.Delta
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Induction(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Generalize(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Injection(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Match(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Rewrite(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BuiltinTactic(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Split(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Delta(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Induction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Generalize(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Injection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rewrite(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BuiltinTactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Split(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Delta(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
