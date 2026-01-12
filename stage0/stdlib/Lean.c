// Lean compiler output
// Module: Lean
// Imports: public import Init public import Lean.Data public import Lean.Compiler public import Lean.Environment public import Lean.Modifiers public import Lean.ProjFns public import Lean.Runtime public import Lean.ResolveName public import Lean.Attributes public import Lean.Parser public import Lean.ReducibilityAttrs public import Lean.Elab public import Lean.Class public import Lean.LocalContext public import Lean.MetavarContext public import Lean.AuxRecursor public import Lean.Meta public import Lean.Util public import Lean.Structure public import Lean.PrettyPrinter public import Lean.CoreM public import Lean.ReservedNameAction public import Lean.InternalExceptionId public import Lean.Server public import Lean.ScopedEnvExtension public import Lean.DocString public import Lean.DeclarationRange public import Lean.LoadDynlib public import Lean.Widget public import Lean.Log public import Lean.Linter public import Lean.SubExpr public import Lean.LabelAttribute public import Lean.AddDecl public import Lean.Replay public import Lean.PrivateName public import Lean.LibrarySuggestions public import Lean.Namespace public import Lean.EnvExtension public import Lean.ErrorExplanation public import Lean.DefEqAttrib public import Lean.Shell public import Lean.ExtraModUses
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_Data(uint8_t builtin);
lean_object* initialize_Lean_Compiler(uint8_t builtin);
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Modifiers(uint8_t builtin);
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
lean_object* initialize_Lean_Runtime(uint8_t builtin);
lean_object* initialize_Lean_ResolveName(uint8_t builtin);
lean_object* initialize_Lean_Attributes(uint8_t builtin);
lean_object* initialize_Lean_Parser(uint8_t builtin);
lean_object* initialize_Lean_ReducibilityAttrs(uint8_t builtin);
lean_object* initialize_Lean_Elab(uint8_t builtin);
lean_object* initialize_Lean_Class(uint8_t builtin);
lean_object* initialize_Lean_LocalContext(uint8_t builtin);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin);
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin);
lean_object* initialize_Lean_Meta(uint8_t builtin);
lean_object* initialize_Lean_Util(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin);
lean_object* initialize_Lean_Server(uint8_t builtin);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_LoadDynlib(uint8_t builtin);
lean_object* initialize_Lean_Widget(uint8_t builtin);
lean_object* initialize_Lean_Log(uint8_t builtin);
lean_object* initialize_Lean_Linter(uint8_t builtin);
lean_object* initialize_Lean_SubExpr(uint8_t builtin);
lean_object* initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Replay(uint8_t builtin);
lean_object* initialize_Lean_PrivateName(uint8_t builtin);
lean_object* initialize_Lean_LibrarySuggestions(uint8_t builtin);
lean_object* initialize_Lean_Namespace(uint8_t builtin);
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanation(uint8_t builtin);
lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin);
lean_object* initialize_Lean_Shell(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Modifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReducibilityAttrs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Class(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_InternalExceptionId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LoadDynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Replay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrivateName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LibrarySuggestions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Namespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Shell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
