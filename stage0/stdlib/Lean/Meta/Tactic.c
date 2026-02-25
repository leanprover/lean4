// Lean compiler output
// Module: Lean.Meta.Tactic
// Imports: public import Lean.Meta.Tactic.Intro public import Lean.Meta.Tactic.Assumption public import Lean.Meta.Tactic.Contradiction public import Lean.Meta.Tactic.Apply public import Lean.Meta.Tactic.Revert public import Lean.Meta.Tactic.Clear public import Lean.Meta.Tactic.Assert public import Lean.Meta.Tactic.Rewrite public import Lean.Meta.Tactic.Generalize public import Lean.Meta.Tactic.Replace public import Lean.Meta.Tactic.Lets public import Lean.Meta.Tactic.Induction public import Lean.Meta.Tactic.Cases public import Lean.Meta.Tactic.ElimInfo public import Lean.Meta.Tactic.Delta public import Lean.Meta.Tactic.Constructor public import Lean.Meta.Tactic.Simp public import Lean.Meta.Tactic.AuxLemma public import Lean.Meta.Tactic.SplitIf public import Lean.Meta.Tactic.Split public import Lean.Meta.Tactic.TryThis public import Lean.Meta.Tactic.Cleanup public import Lean.Meta.Tactic.Unfold public import Lean.Meta.Tactic.Rename public import Lean.Meta.Tactic.AC public import Lean.Meta.Tactic.Refl public import Lean.Meta.Tactic.Congr public import Lean.Meta.Tactic.Repeat public import Lean.Meta.Tactic.NormCast public import Lean.Meta.Tactic.IndependentOf public import Lean.Meta.Tactic.Symm public import Lean.Meta.Tactic.Backtrack public import Lean.Meta.Tactic.SolveByElim public import Lean.Meta.Tactic.FunInd public import Lean.Meta.Tactic.Rfl public import Lean.Meta.Tactic.Rewrites public import Lean.Meta.Tactic.Grind public import Lean.Meta.Tactic.Ext public import Lean.Meta.Tactic.Try public import Lean.Meta.Tactic.Cbv
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
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Lets(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Induction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_AC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Congr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_FunInd(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rfl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Ext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Try(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ElimInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_NormCast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_IndependentOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FunInd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rfl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrites(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
