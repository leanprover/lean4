// Lean compiler output
// Module: Lean.ErrorExplanations
// Imports: Lean.ErrorExplanations.CtorResultingTypeMismatch Lean.ErrorExplanations.DependsOnNoncomputable Lean.ErrorExplanations.InductiveParamMismatch Lean.ErrorExplanations.InductiveParamMissing Lean.ErrorExplanations.InferBinderTypeFailed Lean.ErrorExplanations.InferDefTypeFailed Lean.ErrorExplanations.InvalidDottedIdent Lean.ErrorExplanations.ProjNonPropFromProp Lean.ErrorExplanations.PropRecLargeElim Lean.ErrorExplanations.RedundantMatchAlt Lean.ErrorExplanations.UnknownIdentifier
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
lean_object* initialize_Lean_ErrorExplanations_CtorResultingTypeMismatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_DependsOnNoncomputable(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_InductiveParamMismatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_InductiveParamMissing(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_InferBinderTypeFailed(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_InferDefTypeFailed(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_InvalidDottedIdent(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_ProjNonPropFromProp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_PropRecLargeElim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_RedundantMatchAlt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanations_UnknownIdentifier(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ErrorExplanations(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ErrorExplanations_CtorResultingTypeMismatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_DependsOnNoncomputable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InductiveParamMismatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InductiveParamMissing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InferBinderTypeFailed(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InferDefTypeFailed(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_InvalidDottedIdent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_ProjNonPropFromProp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_PropRecLargeElim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_RedundantMatchAlt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanations_UnknownIdentifier(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
