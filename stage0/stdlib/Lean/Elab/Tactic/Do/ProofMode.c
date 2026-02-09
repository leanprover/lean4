// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.MGoal public import Lean.Elab.Tactic.Do.ProofMode.Delab public import Lean.Elab.Tactic.Do.ProofMode.Basic public import Lean.Elab.Tactic.Do.ProofMode.Clear public import Lean.Elab.Tactic.Do.ProofMode.Intro public import Lean.Elab.Tactic.Do.ProofMode.Revert public import Lean.Elab.Tactic.Do.ProofMode.Exact public import Lean.Elab.Tactic.Do.ProofMode.Assumption public import Lean.Elab.Tactic.Do.ProofMode.Pure public import Lean.Elab.Tactic.Do.ProofMode.Frame public import Lean.Elab.Tactic.Do.ProofMode.LeftRight public import Lean.Elab.Tactic.Do.ProofMode.Constructor public import Lean.Elab.Tactic.Do.ProofMode.RenameI public import Lean.Elab.Tactic.Do.ProofMode.Specialize public import Lean.Elab.Tactic.Do.ProofMode.Cases public import Lean.Elab.Tactic.Do.ProofMode.Exfalso public import Lean.Elab.Tactic.Do.ProofMode.Have public import Lean.Elab.Tactic.Do.ProofMode.Refine
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
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Have(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
