// Lean compiler output
// Module: Lean.Elab
// Imports: Init Lean.Elab.Import Lean.Elab.Exception Lean.Elab.Config Lean.Elab.Command Lean.Elab.Term Lean.Elab.App Lean.Elab.Binders Lean.Elab.LetRec Lean.Elab.Frontend Lean.Elab.BuiltinNotation Lean.Elab.Declaration Lean.Elab.Tactic Lean.Elab.Match Lean.Elab.Quotation Lean.Elab.Syntax Lean.Elab.Do Lean.Elab.StructInst Lean.Elab.Inductive Lean.Elab.Structure Lean.Elab.Print Lean.Elab.MutualDef Lean.Elab.AuxDef Lean.Elab.PreDefinition Lean.Elab.Deriving Lean.Elab.DeclarationRange Lean.Elab.Extra Lean.Elab.GenInjective Lean.Elab.BuiltinTerm Lean.Elab.Arg Lean.Elab.PatternVar Lean.Elab.ElabRules Lean.Elab.Macro Lean.Elab.Notation Lean.Elab.Mixfix Lean.Elab.MacroRules Lean.Elab.BuiltinCommand Lean.Elab.RecAppSyntax Lean.Elab.Eval Lean.Elab.Calc
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
lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_App(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_LetRec(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Declaration(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Quotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Do(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_StructInst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Inductive(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Print(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MutualDef(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_GenInjective(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BuiltinTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Arg(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PatternVar(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Macro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Notation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Mixfix(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MacroRules(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BuiltinCommand(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Calc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_LetRec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Frontend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Declaration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_StructInst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Print(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_GenInjective(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Arg(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PatternVar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ElabRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Mixfix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MacroRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinCommand(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Calc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
