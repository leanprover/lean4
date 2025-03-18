// Lean compiler output
// Module: Lean
// Imports: Init Lean.Data Lean.Compiler Lean.Environment Lean.Modifiers Lean.ProjFns Lean.Runtime Lean.ResolveName Lean.Attributes Lean.Parser Lean.ReducibilityAttrs Lean.Elab Lean.Class Lean.LocalContext Lean.MetavarContext Lean.AuxRecursor Lean.Meta Lean.Util Lean.Structure Lean.PrettyPrinter Lean.CoreM Lean.ReservedNameAction Lean.InternalExceptionId Lean.Server Lean.ScopedEnvExtension Lean.DocString Lean.DeclarationRange Lean.LoadDynlib Lean.Widget Lean.Log Lean.Linter Lean.SubExpr Lean.LabelAttribute Lean.AddDecl Lean.Replay Lean.PrivateName Lean.PremiseSelection Lean.Namespace
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
lean_object* initialize_Lean_Data(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Modifiers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Runtime(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ReducibilityAttrs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Class(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LocalContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LoadDynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_SubExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LabelAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Replay(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrivateName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PremiseSelection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Namespace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Modifiers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReducibilityAttrs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Class(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_InternalExceptionId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LoadDynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_SubExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LabelAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Replay(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrivateName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PremiseSelection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Namespace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
