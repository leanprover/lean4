// Lean compiler output
// Module: Lean.Elab.Tactic
// Imports: Lean.Elab.Term Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Induction Lean.Elab.Tactic.Generalize Lean.Elab.Tactic.Injection Lean.Elab.Tactic.Match Lean.Elab.Tactic.Rewrite Lean.Elab.Tactic.Location Lean.Elab.Tactic.SimpTrace Lean.Elab.Tactic.Simp Lean.Elab.Tactic.Simproc Lean.Elab.Tactic.BuiltinTactic Lean.Elab.Tactic.Split Lean.Elab.Tactic.Conv Lean.Elab.Tactic.Delta Lean.Elab.Tactic.Meta Lean.Elab.Tactic.Unfold Lean.Elab.Tactic.Cache Lean.Elab.Tactic.Calc Lean.Elab.Tactic.Congr Lean.Elab.Tactic.Guard Lean.Elab.Tactic.RCases Lean.Elab.Tactic.Repeat Lean.Elab.Tactic.Ext Lean.Elab.Tactic.Change Lean.Elab.Tactic.FalseOrByContra Lean.Elab.Tactic.Omega Lean.Elab.Tactic.Simpa Lean.Elab.Tactic.NormCast Lean.Elab.Tactic.Symm Lean.Elab.Tactic.SolveByElim Lean.Elab.Tactic.LibrarySearch Lean.Elab.Tactic.ShowTerm Lean.Elab.Tactic.Rfl Lean.Elab.Tactic.Rewrites Lean.Elab.Tactic.DiscrTreeKey Lean.Elab.Tactic.BVDecide Lean.Elab.Tactic.BoolToPropSimps Lean.Elab.Tactic.Classical
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
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Induction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Generalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BuiltinTactic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Delta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Unfold(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Cache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Calc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Congr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Guard(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_RCases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Repeat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Change(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Omega(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_NormCast(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Symm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_SolveByElim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_LibrarySearch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ShowTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Rfl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Rewrites(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_DiscrTreeKey(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BoolToPropSimps(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Classical(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Induction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Generalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SimpTrace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BuiltinTactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Delta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Unfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Cache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Calc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Congr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Guard(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_RCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Repeat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Change(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_FalseOrByContra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simpa(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_NormCast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Symm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SolveByElim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_LibrarySearch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ShowTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rfl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rewrites(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Classical(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
