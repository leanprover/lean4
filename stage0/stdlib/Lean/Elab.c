// Lean compiler output
// Module: Lean.Elab
// Imports: Init Lean.Elab.Import Lean.Elab.Exception Lean.Elab.Command Lean.Elab.Term Lean.Elab.App Lean.Elab.Binders Lean.Elab.LetRec Lean.Elab.Frontend Lean.Elab.BuiltinNotation Lean.Elab.Declaration Lean.Elab.Tactic Lean.Elab.Match Lean.Elab.Quotation Lean.Elab.Syntax Lean.Elab.Do Lean.Elab.StructInst Lean.Elab.Inductive Lean.Elab.Structure Lean.Elab.Print Lean.Elab.MutualDef Lean.Elab.PreDefinition Lean.Elab.Deriving Lean.Elab.DeclarationRange Lean.Elab.Extra Lean.Elab.GenInjective Lean.Elab.BuiltinTerm Lean.Elab.Arg Lean.Elab.PatternVar Lean.Elab.ElabRules Lean.Elab.Macro Lean.Elab.Notation Lean.Elab.Mixfix Lean.Elab.MacroRules Lean.Elab.BuiltinCommand
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
lean_object* initialize_Lean_Elab_Import(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_App(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_LetRec(lean_object*);
lean_object* initialize_Lean_Elab_Frontend(lean_object*);
lean_object* initialize_Lean_Elab_BuiltinNotation(lean_object*);
lean_object* initialize_Lean_Elab_Declaration(lean_object*);
lean_object* initialize_Lean_Elab_Tactic(lean_object*);
lean_object* initialize_Lean_Elab_Match(lean_object*);
lean_object* initialize_Lean_Elab_Quotation(lean_object*);
lean_object* initialize_Lean_Elab_Syntax(lean_object*);
lean_object* initialize_Lean_Elab_Do(lean_object*);
lean_object* initialize_Lean_Elab_StructInst(lean_object*);
lean_object* initialize_Lean_Elab_Inductive(lean_object*);
lean_object* initialize_Lean_Elab_Structure(lean_object*);
lean_object* initialize_Lean_Elab_Print(lean_object*);
lean_object* initialize_Lean_Elab_MutualDef(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition(lean_object*);
lean_object* initialize_Lean_Elab_Deriving(lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(lean_object*);
lean_object* initialize_Lean_Elab_Extra(lean_object*);
lean_object* initialize_Lean_Elab_GenInjective(lean_object*);
lean_object* initialize_Lean_Elab_BuiltinTerm(lean_object*);
lean_object* initialize_Lean_Elab_Arg(lean_object*);
lean_object* initialize_Lean_Elab_PatternVar(lean_object*);
lean_object* initialize_Lean_Elab_ElabRules(lean_object*);
lean_object* initialize_Lean_Elab_Macro(lean_object*);
lean_object* initialize_Lean_Elab_Notation(lean_object*);
lean_object* initialize_Lean_Elab_Mixfix(lean_object*);
lean_object* initialize_Lean_Elab_MacroRules(lean_object*);
lean_object* initialize_Lean_Elab_BuiltinCommand(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_LetRec(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Frontend(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Declaration(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_StructInst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Print(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualDef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Extra(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_GenInjective(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Arg(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PatternVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ElabRules(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Macro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Notation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Mixfix(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MacroRules(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinCommand(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
