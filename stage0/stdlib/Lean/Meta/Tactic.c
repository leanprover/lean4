// Lean compiler output
// Module: Lean.Meta.Tactic
// Imports: Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Contradiction Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Generalize Lean.Meta.Tactic.Replace Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Cases Lean.Meta.Tactic.ElimInfo Lean.Meta.Tactic.Delta Lean.Meta.Tactic.Constructor Lean.Meta.Tactic.Simp Lean.Meta.Tactic.AuxLemma Lean.Meta.Tactic.SplitIf Lean.Meta.Tactic.Split Lean.Meta.Tactic.TryThis Lean.Meta.Tactic.Cleanup Lean.Meta.Tactic.Unfold Lean.Meta.Tactic.Rename Lean.Meta.Tactic.LinearArith Lean.Meta.Tactic.AC Lean.Meta.Tactic.Refl Lean.Meta.Tactic.Congr Lean.Meta.Tactic.Repeat Lean.Meta.Tactic.NormCast Lean.Meta.Tactic.IndependentOf Lean.Meta.Tactic.Symm Lean.Meta.Tactic.Backtrack Lean.Meta.Tactic.SolveByElim Lean.Meta.Tactic.FunInd Lean.Meta.Tactic.Rfl Lean.Meta.Tactic.Rewrites Lean.Meta.Tactic.Grind Lean.Meta.Tactic.Ext Lean.Meta.Tactic.Try
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
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Induction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_LinearArith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AC(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Congr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Symm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FunInd(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rfl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Try(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Generalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Induction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ElimInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Constructor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Unfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_LinearArith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Congr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Repeat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_NormCast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_IndependentOf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Symm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Backtrack(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SolveByElim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FunInd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rfl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrites(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Try(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
