// Lean compiler output
// Module: Lean.ErrorExplanations
// Imports: public import Lean.ErrorExplanations.CtorResultingTypeMismatch public import Lean.ErrorExplanations.DependsOnNoncomputable public import Lean.ErrorExplanations.InductiveParamMismatch public import Lean.ErrorExplanations.InductiveParamMissing public import Lean.ErrorExplanations.InferBinderTypeFailed public import Lean.ErrorExplanations.InferDefTypeFailed public import Lean.ErrorExplanations.InvalidDottedIdent public import Lean.ErrorExplanations.ProjNonPropFromProp public import Lean.ErrorExplanations.PropRecLargeElim public import Lean.ErrorExplanations.RedundantMatchAlt public import Lean.ErrorExplanations.UnknownIdentifier
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
lean_object* initialize_Lean_ErrorExplanations_CtorResultingTypeMismatch(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_DependsOnNoncomputable(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_InductiveParamMismatch(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_InductiveParamMissing(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_InferBinderTypeFailed(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_InferDefTypeFailed(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_InvalidDottedIdent(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_ProjNonPropFromProp(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_PropRecLargeElim(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_RedundantMatchAlt(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanations_UnknownIdentifier(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ErrorExplanations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ErrorExplanations_CtorResultingTypeMismatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_DependsOnNoncomputable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InductiveParamMismatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InductiveParamMissing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InferBinderTypeFailed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InferDefTypeFailed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InvalidDottedIdent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_ProjNonPropFromProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_PropRecLargeElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_RedundantMatchAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_UnknownIdentifier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
