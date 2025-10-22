// Lean compiler output
// Module: Lean.Elab.CheckTactic
// Imports: public import Lean.Elab.Tactic.ElabTerm public import Lean.Elab.Command public import Lean.Elab.Tactic.Meta public import Lean.Meta.CheckTactic
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
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__3;
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1;
LEAN_EXPORT uint8_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(uint8_t, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8;
lean_object* l_Lean_Elab_Command_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2;
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__0;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__1;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__4;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11;
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2;
extern lean_object* l_Lean_Elab_macroAttribute;
extern lean_object* l_Lean_Elab_pp_macroStack;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6;
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__4;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1;
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5;
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2;
lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9;
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__2;
lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7;
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__0;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
lean_inc_ref(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 0, x_19);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_4, 2);
lean_inc(x_24);
lean_inc_ref(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_3, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_4, 2);
lean_inc(x_36);
lean_inc_ref(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(3, 2, 0);
} else {
 x_38 = x_33;
 lean_ctor_set_tag(x_38, 3);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("while expanding", 15, 15);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_dec(x_9);
lean_inc_ref(x_1);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_2);
x_10 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_8);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_2 = x_13;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
x_18 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_17);
x_19 = l_Lean_MessageData_ofSyntax(x_16);
x_20 = l_Lean_indentD(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_2 = x_21;
x_3 = x_15;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
lean_inc_ref(x_1);
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(7, 2, 0);
} else {
 x_27 = x_26;
 lean_ctor_set_tag(x_27, 7);
}
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_1);
x_28 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofSyntax(x_25);
x_31 = l_Lean_indentD(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_2 = x_32;
x_3 = x_24;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_pp_macroStack;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("with resulting expansion", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__0;
x_7 = l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__2(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__1;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_1);
x_15 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofSyntax(x_12);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3(x_14, x_19, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__1;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofSyntax(x_22);
x_28 = l_Lean_indentD(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3(x_23, x_29, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
lean_inc(x_14);
x_15 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg(x_12, x_14, x_6, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Elab_getBetterRef(x_9, x_14);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_18);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = l_Lean_Elab_getBetterRef(x_9, x_14);
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec_ref(x_2);
lean_inc(x_25);
x_26 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg(x_23, x_25, x_6, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = l_Lean_Elab_getBetterRef(x_9, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_29;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_27 = lean_ctor_get(x_7, 12);
x_28 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_29 = lean_ctor_get(x_7, 13);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_30 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_15);
lean_ctor_set(x_31, 2, x_16);
lean_ctor_set(x_31, 3, x_17);
lean_ctor_set(x_31, 4, x_18);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_20);
lean_ctor_set(x_31, 7, x_21);
lean_ctor_set(x_31, 8, x_22);
lean_ctor_set(x_31, 9, x_23);
lean_ctor_set(x_31, 10, x_24);
lean_ctor_set(x_31, 11, x_25);
lean_ctor_set(x_31, 12, x_27);
lean_ctor_set(x_31, 13, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*14, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*14 + 1, x_28);
x_32 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_31, x_8, x_9);
lean_dec_ref(x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_1);
x_9 = lean_st_ref_set(x_2, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
x_20 = lean_ctor_get(x_5, 5);
x_21 = lean_ctor_get(x_5, 6);
x_22 = lean_ctor_get(x_5, 7);
x_23 = lean_ctor_get(x_5, 8);
x_24 = lean_ctor_get(x_5, 9);
x_25 = lean_ctor_get(x_5, 10);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_18);
lean_ctor_set(x_26, 4, x_19);
lean_ctor_set(x_26, 5, x_20);
lean_ctor_set(x_26, 6, x_21);
lean_ctor_set(x_26, 7, x_22);
lean_ctor_set(x_26, 8, x_23);
lean_ctor_set(x_26, 9, x_24);
lean_ctor_set(x_26, 10, x_25);
x_27 = lean_st_ref_set(x_2, x_26, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg(x_1, x_4, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_4);
x_12 = lean_apply_3(x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg(x_9, x_4, x_14);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec_ref(x_12);
x_22 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg(x_9, x_4, x_21);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" closed goal, but is expected to reduce to ", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term reduces to", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nbut is expected to reduce to ", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" produced multiple goals, but is expected to reduce to ", 55, 55);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_box(0);
x_21 = lean_box(x_2);
x_22 = lean_box(x_2);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_22);
x_24 = 1;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_25 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), x_23, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_26);
x_28 = lean_infer_type(x_26, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
lean_inc(x_29);
x_31 = l_Lean_Meta_CheckTactic_mkCheckGoalType(x_26, x_29, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = 0;
x_36 = lean_box(0);
lean_inc_ref(x_11);
x_37 = l_Lean_Meta_mkFreshExprMVar(x_34, x_35, x_36, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_29);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_41 = l_Lean_Elab_Term_elabTerm(x_3, x_40, x_2, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Lean_Expr_mvarId_x21(x_38);
lean_dec(x_38);
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0;
x_50 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1;
x_51 = 5;
lean_inc(x_4);
x_52 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_4);
lean_ctor_set(x_52, 3, x_4);
lean_ctor_set_usize(x_52, 4, x_51);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_48);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set(x_54, 6, x_20);
lean_ctor_set_uint8(x_54, sizeof(void*)*7, x_2);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 1, x_2);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 2, x_46);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 3, x_2);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 4, x_2);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 5, x_46);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 6, x_46);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 7, x_46);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 8, x_2);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 9, x_46);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 10, x_2);
x_55 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set(x_55, 3, x_45);
lean_ctor_set(x_55, 4, x_45);
lean_ctor_set(x_55, 5, x_53);
lean_ctor_set(x_55, 6, x_45);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_6);
x_56 = l_Lean_Elab_runTactic(x_44, x_6, x_54, x_55, x_11, x_12, x_13, x_14, x_43);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_dec(x_60);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec_ref(x_56);
x_62 = l_Lean_MessageData_ofSyntax(x_6);
x_63 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_63);
lean_ctor_set(x_57, 0, x_62);
x_64 = l_Lean_indentExpr(x_42);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_67, x_9, x_10, x_11, x_12, x_13, x_14, x_61);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_free_object(x_57);
lean_dec(x_6);
x_70 = lean_ctor_get(x_56, 1);
lean_inc(x_70);
lean_dec_ref(x_56);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_72 = x_59;
} else {
 lean_dec_ref(x_59);
 x_72 = lean_box(0);
}
x_73 = l_Lean_MVarId_getType(x_71, x_11, x_12, x_13, x_14, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_76 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_7, x_74, x_11, x_12, x_13, x_14, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_111; uint8_t x_112; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_111 = l_Lean_Meta_Context_config(x_11);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_113 = lean_ctor_get_uint8(x_11, sizeof(void*)*7);
x_114 = lean_ctor_get(x_11, 1);
x_115 = lean_ctor_get(x_11, 2);
x_116 = lean_ctor_get(x_11, 3);
x_117 = lean_ctor_get(x_11, 4);
x_118 = lean_ctor_get(x_11, 5);
x_119 = lean_ctor_get(x_11, 6);
x_120 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 1);
x_121 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 2);
x_122 = 2;
lean_ctor_set_uint8(x_111, 9, x_122);
x_123 = l_Lean_Meta_Context_configKey(x_11);
x_124 = 2;
x_125 = lean_uint64_shift_right(x_123, x_124);
x_126 = lean_uint64_shift_left(x_125, x_124);
x_127 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10;
x_128 = lean_uint64_lor(x_126, x_127);
x_129 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_129, 0, x_111);
lean_ctor_set_uint64(x_129, sizeof(void*)*1, x_128);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc_ref(x_115);
lean_inc(x_114);
x_130 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_114);
lean_ctor_set(x_130, 2, x_115);
lean_ctor_set(x_130, 3, x_116);
lean_ctor_set(x_130, 4, x_117);
lean_ctor_set(x_130, 5, x_118);
lean_ctor_set(x_130, 6, x_119);
lean_ctor_set_uint8(x_130, sizeof(void*)*7, x_113);
lean_ctor_set_uint8(x_130, sizeof(void*)*7 + 1, x_120);
lean_ctor_set_uint8(x_130, sizeof(void*)*7 + 2, x_121);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_42);
lean_inc(x_79);
x_131 = l_Lean_Meta_isExprDefEq(x_79, x_42, x_130, x_12, x_13, x_14, x_78);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
x_134 = lean_unbox(x_132);
lean_dec(x_132);
x_81 = x_134;
x_82 = x_133;
goto block_110;
}
else
{
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
lean_dec_ref(x_131);
x_137 = lean_unbox(x_135);
lean_dec(x_135);
x_81 = x_137;
x_82 = x_136;
goto block_110;
}
else
{
uint8_t x_138; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_138 = !lean_is_exclusive(x_131);
if (x_138 == 0)
{
return x_131;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_131, 0);
x_140 = lean_ctor_get(x_131, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_131);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; lean_object* x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; uint64_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_142 = lean_ctor_get_uint8(x_111, 0);
x_143 = lean_ctor_get_uint8(x_111, 1);
x_144 = lean_ctor_get_uint8(x_111, 2);
x_145 = lean_ctor_get_uint8(x_111, 3);
x_146 = lean_ctor_get_uint8(x_111, 4);
x_147 = lean_ctor_get_uint8(x_111, 5);
x_148 = lean_ctor_get_uint8(x_111, 6);
x_149 = lean_ctor_get_uint8(x_111, 7);
x_150 = lean_ctor_get_uint8(x_111, 8);
x_151 = lean_ctor_get_uint8(x_111, 10);
x_152 = lean_ctor_get_uint8(x_111, 11);
x_153 = lean_ctor_get_uint8(x_111, 12);
x_154 = lean_ctor_get_uint8(x_111, 13);
x_155 = lean_ctor_get_uint8(x_111, 14);
x_156 = lean_ctor_get_uint8(x_111, 15);
x_157 = lean_ctor_get_uint8(x_111, 16);
x_158 = lean_ctor_get_uint8(x_111, 17);
x_159 = lean_ctor_get_uint8(x_111, 18);
lean_dec(x_111);
x_160 = lean_ctor_get_uint8(x_11, sizeof(void*)*7);
x_161 = lean_ctor_get(x_11, 1);
x_162 = lean_ctor_get(x_11, 2);
x_163 = lean_ctor_get(x_11, 3);
x_164 = lean_ctor_get(x_11, 4);
x_165 = lean_ctor_get(x_11, 5);
x_166 = lean_ctor_get(x_11, 6);
x_167 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 1);
x_168 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 2);
x_169 = 2;
x_170 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_170, 0, x_142);
lean_ctor_set_uint8(x_170, 1, x_143);
lean_ctor_set_uint8(x_170, 2, x_144);
lean_ctor_set_uint8(x_170, 3, x_145);
lean_ctor_set_uint8(x_170, 4, x_146);
lean_ctor_set_uint8(x_170, 5, x_147);
lean_ctor_set_uint8(x_170, 6, x_148);
lean_ctor_set_uint8(x_170, 7, x_149);
lean_ctor_set_uint8(x_170, 8, x_150);
lean_ctor_set_uint8(x_170, 9, x_169);
lean_ctor_set_uint8(x_170, 10, x_151);
lean_ctor_set_uint8(x_170, 11, x_152);
lean_ctor_set_uint8(x_170, 12, x_153);
lean_ctor_set_uint8(x_170, 13, x_154);
lean_ctor_set_uint8(x_170, 14, x_155);
lean_ctor_set_uint8(x_170, 15, x_156);
lean_ctor_set_uint8(x_170, 16, x_157);
lean_ctor_set_uint8(x_170, 17, x_158);
lean_ctor_set_uint8(x_170, 18, x_159);
x_171 = l_Lean_Meta_Context_configKey(x_11);
x_172 = 2;
x_173 = lean_uint64_shift_right(x_171, x_172);
x_174 = lean_uint64_shift_left(x_173, x_172);
x_175 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10;
x_176 = lean_uint64_lor(x_174, x_175);
x_177 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set_uint64(x_177, sizeof(void*)*1, x_176);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc_ref(x_162);
lean_inc(x_161);
x_178 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_161);
lean_ctor_set(x_178, 2, x_162);
lean_ctor_set(x_178, 3, x_163);
lean_ctor_set(x_178, 4, x_164);
lean_ctor_set(x_178, 5, x_165);
lean_ctor_set(x_178, 6, x_166);
lean_ctor_set_uint8(x_178, sizeof(void*)*7, x_160);
lean_ctor_set_uint8(x_178, sizeof(void*)*7 + 1, x_167);
lean_ctor_set_uint8(x_178, sizeof(void*)*7 + 2, x_168);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_42);
lean_inc(x_79);
x_179 = l_Lean_Meta_isExprDefEq(x_79, x_42, x_178, x_12, x_13, x_14, x_78);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec_ref(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_81 = x_182;
x_82 = x_181;
goto block_110;
}
else
{
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
lean_dec_ref(x_179);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_81 = x_185;
x_82 = x_184;
goto block_110;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_186 = lean_ctor_get(x_179, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_179, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_188 = x_179;
} else {
 lean_dec_ref(x_179);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
block_110:
{
if (x_81 == 0)
{
if (x_2 == 0)
{
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_16 = x_82;
goto block_19;
}
else
{
lean_object* x_83; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_83 = l_Lean_Meta_addPPExplicitToExposeDiff(x_79, x_42, x_11, x_12, x_13, x_14, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
x_89 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7;
x_90 = l_Lean_indentExpr(x_87);
lean_ctor_set_tag(x_84, 7);
lean_ctor_set(x_84, 1, x_90);
lean_ctor_set(x_84, 0, x_89);
x_91 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9;
if (lean_is_scalar(x_80)) {
 x_92 = lean_alloc_ctor(7, 2, 0);
} else {
 x_92 = x_80;
 lean_ctor_set_tag(x_92, 7);
}
lean_ctor_set(x_92, 0, x_84);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_indentExpr(x_88);
if (lean_is_scalar(x_72)) {
 x_94 = lean_alloc_ctor(7, 2, 0);
} else {
 x_94 = x_72;
 lean_ctor_set_tag(x_94, 7);
}
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_94, x_9, x_10, x_11, x_12, x_13, x_14, x_85);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_84, 0);
x_97 = lean_ctor_get(x_84, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_84);
x_98 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7;
x_99 = l_Lean_indentExpr(x_96);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9;
if (lean_is_scalar(x_80)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_80;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_indentExpr(x_97);
if (lean_is_scalar(x_72)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_72;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_104, x_9, x_10, x_11, x_12, x_13, x_14, x_85);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_106 = !lean_is_exclusive(x_83);
if (x_106 == 0)
{
return x_83;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_83, 0);
x_108 = lean_ctor_get(x_83, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_83);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_16 = x_82;
goto block_19;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_190 = !lean_is_exclusive(x_76);
if (x_190 == 0)
{
return x_76;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_76, 0);
x_192 = lean_ctor_get(x_76, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_76);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_194 = !lean_is_exclusive(x_73);
if (x_194 == 0)
{
return x_73;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_73, 0);
x_196 = lean_ctor_get(x_73, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_73);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_59);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_59, 1);
lean_dec(x_199);
x_200 = lean_ctor_get(x_59, 0);
lean_dec(x_200);
x_201 = lean_ctor_get(x_56, 1);
lean_inc(x_201);
lean_dec_ref(x_56);
x_202 = !lean_is_exclusive(x_69);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_69, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_69, 0);
lean_dec(x_204);
x_205 = l_Lean_MessageData_ofSyntax(x_6);
x_206 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12;
lean_ctor_set_tag(x_69, 7);
lean_ctor_set(x_69, 1, x_206);
lean_ctor_set(x_69, 0, x_205);
x_207 = l_Lean_indentExpr(x_42);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_207);
lean_ctor_set(x_59, 0, x_69);
x_208 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_208);
x_209 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_57, x_9, x_10, x_11, x_12, x_13, x_14, x_201);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_69);
x_210 = l_Lean_MessageData_ofSyntax(x_6);
x_211 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12;
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_indentExpr(x_42);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_213);
lean_ctor_set(x_59, 0, x_212);
x_214 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_214);
x_215 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_57, x_9, x_10, x_11, x_12, x_13, x_14, x_201);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_59);
x_216 = lean_ctor_get(x_56, 1);
lean_inc(x_216);
lean_dec_ref(x_56);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_217 = x_69;
} else {
 lean_dec_ref(x_69);
 x_217 = lean_box(0);
}
x_218 = l_Lean_MessageData_ofSyntax(x_6);
x_219 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12;
if (lean_is_scalar(x_217)) {
 x_220 = lean_alloc_ctor(7, 2, 0);
} else {
 x_220 = x_217;
 lean_ctor_set_tag(x_220, 7);
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_indentExpr(x_42);
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_223);
lean_ctor_set(x_57, 0, x_222);
x_224 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_57, x_9, x_10, x_11, x_12, x_13, x_14, x_216);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_224;
}
}
}
}
else
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_57, 0);
lean_inc(x_225);
lean_dec(x_57);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_226 = lean_ctor_get(x_56, 1);
lean_inc(x_226);
lean_dec_ref(x_56);
x_227 = l_Lean_MessageData_ofSyntax(x_6);
x_228 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3;
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_indentExpr(x_42);
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5;
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_233, x_9, x_10, x_11, x_12, x_13, x_14, x_226);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_234;
}
else
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_6);
x_236 = lean_ctor_get(x_56, 1);
lean_inc(x_236);
lean_dec_ref(x_56);
x_237 = lean_ctor_get(x_225, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_238 = x_225;
} else {
 lean_dec_ref(x_225);
 x_238 = lean_box(0);
}
x_239 = l_Lean_MVarId_getType(x_237, x_11, x_12, x_13, x_14, x_236);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec_ref(x_239);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_242 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_7, x_240, x_11, x_12, x_13, x_14, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; uint8_t x_285; uint8_t x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_296; uint8_t x_297; lean_object* x_298; uint64_t x_299; uint64_t x_300; uint64_t x_301; uint64_t x_302; uint64_t x_303; uint64_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec_ref(x_242);
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_268 = l_Lean_Meta_Context_config(x_11);
x_269 = lean_ctor_get_uint8(x_268, 0);
x_270 = lean_ctor_get_uint8(x_268, 1);
x_271 = lean_ctor_get_uint8(x_268, 2);
x_272 = lean_ctor_get_uint8(x_268, 3);
x_273 = lean_ctor_get_uint8(x_268, 4);
x_274 = lean_ctor_get_uint8(x_268, 5);
x_275 = lean_ctor_get_uint8(x_268, 6);
x_276 = lean_ctor_get_uint8(x_268, 7);
x_277 = lean_ctor_get_uint8(x_268, 8);
x_278 = lean_ctor_get_uint8(x_268, 10);
x_279 = lean_ctor_get_uint8(x_268, 11);
x_280 = lean_ctor_get_uint8(x_268, 12);
x_281 = lean_ctor_get_uint8(x_268, 13);
x_282 = lean_ctor_get_uint8(x_268, 14);
x_283 = lean_ctor_get_uint8(x_268, 15);
x_284 = lean_ctor_get_uint8(x_268, 16);
x_285 = lean_ctor_get_uint8(x_268, 17);
x_286 = lean_ctor_get_uint8(x_268, 18);
if (lean_is_exclusive(x_268)) {
 x_287 = x_268;
} else {
 lean_dec_ref(x_268);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get_uint8(x_11, sizeof(void*)*7);
x_289 = lean_ctor_get(x_11, 1);
x_290 = lean_ctor_get(x_11, 2);
x_291 = lean_ctor_get(x_11, 3);
x_292 = lean_ctor_get(x_11, 4);
x_293 = lean_ctor_get(x_11, 5);
x_294 = lean_ctor_get(x_11, 6);
x_295 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 1);
x_296 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 2);
x_297 = 2;
if (lean_is_scalar(x_287)) {
 x_298 = lean_alloc_ctor(0, 0, 19);
} else {
 x_298 = x_287;
}
lean_ctor_set_uint8(x_298, 0, x_269);
lean_ctor_set_uint8(x_298, 1, x_270);
lean_ctor_set_uint8(x_298, 2, x_271);
lean_ctor_set_uint8(x_298, 3, x_272);
lean_ctor_set_uint8(x_298, 4, x_273);
lean_ctor_set_uint8(x_298, 5, x_274);
lean_ctor_set_uint8(x_298, 6, x_275);
lean_ctor_set_uint8(x_298, 7, x_276);
lean_ctor_set_uint8(x_298, 8, x_277);
lean_ctor_set_uint8(x_298, 9, x_297);
lean_ctor_set_uint8(x_298, 10, x_278);
lean_ctor_set_uint8(x_298, 11, x_279);
lean_ctor_set_uint8(x_298, 12, x_280);
lean_ctor_set_uint8(x_298, 13, x_281);
lean_ctor_set_uint8(x_298, 14, x_282);
lean_ctor_set_uint8(x_298, 15, x_283);
lean_ctor_set_uint8(x_298, 16, x_284);
lean_ctor_set_uint8(x_298, 17, x_285);
lean_ctor_set_uint8(x_298, 18, x_286);
x_299 = l_Lean_Meta_Context_configKey(x_11);
x_300 = 2;
x_301 = lean_uint64_shift_right(x_299, x_300);
x_302 = lean_uint64_shift_left(x_301, x_300);
x_303 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10;
x_304 = lean_uint64_lor(x_302, x_303);
x_305 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set_uint64(x_305, sizeof(void*)*1, x_304);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc_ref(x_291);
lean_inc_ref(x_290);
lean_inc(x_289);
x_306 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_289);
lean_ctor_set(x_306, 2, x_290);
lean_ctor_set(x_306, 3, x_291);
lean_ctor_set(x_306, 4, x_292);
lean_ctor_set(x_306, 5, x_293);
lean_ctor_set(x_306, 6, x_294);
lean_ctor_set_uint8(x_306, sizeof(void*)*7, x_288);
lean_ctor_set_uint8(x_306, sizeof(void*)*7 + 1, x_295);
lean_ctor_set_uint8(x_306, sizeof(void*)*7 + 2, x_296);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_42);
lean_inc(x_245);
x_307 = l_Lean_Meta_isExprDefEq(x_245, x_42, x_306, x_12, x_13, x_14, x_244);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec_ref(x_307);
x_310 = lean_unbox(x_308);
lean_dec(x_308);
x_247 = x_310;
x_248 = x_309;
goto block_267;
}
else
{
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = lean_ctor_get(x_307, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_307, 1);
lean_inc(x_312);
lean_dec_ref(x_307);
x_313 = lean_unbox(x_311);
lean_dec(x_311);
x_247 = x_313;
x_248 = x_312;
goto block_267;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_238);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_314 = lean_ctor_get(x_307, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_307, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_316 = x_307;
} else {
 lean_dec_ref(x_307);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
block_267:
{
if (x_247 == 0)
{
if (x_2 == 0)
{
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_238);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_16 = x_248;
goto block_19;
}
else
{
lean_object* x_249; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_249 = l_Lean_Meta_addPPExplicitToExposeDiff(x_245, x_42, x_11, x_12, x_13, x_14, x_248);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec_ref(x_249);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_254 = x_250;
} else {
 lean_dec_ref(x_250);
 x_254 = lean_box(0);
}
x_255 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7;
x_256 = l_Lean_indentExpr(x_252);
if (lean_is_scalar(x_254)) {
 x_257 = lean_alloc_ctor(7, 2, 0);
} else {
 x_257 = x_254;
 lean_ctor_set_tag(x_257, 7);
}
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9;
if (lean_is_scalar(x_246)) {
 x_259 = lean_alloc_ctor(7, 2, 0);
} else {
 x_259 = x_246;
 lean_ctor_set_tag(x_259, 7);
}
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = l_Lean_indentExpr(x_253);
if (lean_is_scalar(x_238)) {
 x_261 = lean_alloc_ctor(7, 2, 0);
} else {
 x_261 = x_238;
 lean_ctor_set_tag(x_261, 7);
}
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_261, x_9, x_10, x_11, x_12, x_13, x_14, x_251);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_246);
lean_dec(x_238);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_263 = lean_ctor_get(x_249, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_249, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_265 = x_249;
} else {
 lean_dec_ref(x_249);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
else
{
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_238);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_16 = x_248;
goto block_19;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_238);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_318 = lean_ctor_get(x_242, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_242, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_320 = x_242;
} else {
 lean_dec_ref(x_242);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_238);
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_322 = lean_ctor_get(x_239, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_239, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_324 = x_239;
} else {
 lean_dec_ref(x_239);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_326 = x_225;
} else {
 lean_dec_ref(x_225);
 x_326 = lean_box(0);
}
x_327 = lean_ctor_get(x_56, 1);
lean_inc(x_327);
lean_dec_ref(x_56);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_328 = x_235;
} else {
 lean_dec_ref(x_235);
 x_328 = lean_box(0);
}
x_329 = l_Lean_MessageData_ofSyntax(x_6);
x_330 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12;
if (lean_is_scalar(x_328)) {
 x_331 = lean_alloc_ctor(7, 2, 0);
} else {
 x_331 = x_328;
 lean_ctor_set_tag(x_331, 7);
}
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Lean_indentExpr(x_42);
if (lean_is_scalar(x_326)) {
 x_333 = lean_alloc_ctor(7, 2, 0);
} else {
 x_333 = x_326;
 lean_ctor_set_tag(x_333, 7);
}
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5;
x_335 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_7, x_335, x_9, x_10, x_11, x_12, x_13, x_14, x_327);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_336;
}
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_337 = !lean_is_exclusive(x_56);
if (x_337 == 0)
{
return x_56;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_56, 0);
x_339 = lean_ctor_get(x_56, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_56);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_38);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_341 = !lean_is_exclusive(x_41);
if (x_341 == 0)
{
return x_41;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_41, 0);
x_343 = lean_ctor_get(x_41, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_41);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_345 = !lean_is_exclusive(x_37);
if (x_345 == 0)
{
return x_37;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_37, 0);
x_347 = lean_ctor_get(x_37, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_37);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
else
{
uint8_t x_349; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_349 = !lean_is_exclusive(x_31);
if (x_349 == 0)
{
return x_31;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_31, 0);
x_351 = lean_ctor_get(x_31, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_31);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_353 = !lean_is_exclusive(x_28);
if (x_353 == 0)
{
return x_28;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_28, 0);
x_355 = lean_ctor_get(x_28, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_28);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
uint8_t x_357; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_357 = !lean_is_exclusive(x_25);
if (x_357 == 0)
{
return x_25;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_25, 0);
x_359 = lean_ctor_get(x_25, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_25);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkTactic", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(5u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_box(0);
x_20 = lean_box(x_6);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed), 15, 7);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_16);
lean_closure_set(x_21, 3, x_12);
lean_closure_set(x_21, 4, x_19);
lean_closure_set(x_21, 5, x_18);
lean_closure_set(x_21, 6, x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lean_Environment_unlockAsync(x_11);
x_24 = l_Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7___redArg(x_23, x_22, x_2, x_3, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7_spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
x_17 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_17;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CheckTactic", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabCheckTactic", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1;
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3;
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(24u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(95u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(95u);
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(24u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_unsigned_to_nat(24u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__4;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = l_Lean_MVarId_getType(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_15 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_dec(x_20);
x_21 = l_Lean_indentExpr(x_19);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_21);
lean_ctor_set(x_16, 0, x_2);
x_2 = x_16;
x_3 = x_11;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = l_Lean_indentExpr(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
x_2 = x_25;
x_3 = x_11;
x_8 = x_17;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = l_Lean_MVarId_getType(x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_17 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_15, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_dec(x_22);
x_23 = l_Lean_indentExpr(x_21);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_23);
lean_ctor_set(x_18, 0, x_2);
x_24 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_18, x_13, x_6, x_7, x_8, x_9, x_19);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lean_indentExpr(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_27, x_13, x_6, x_7, x_8, x_9, x_19);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_runTactic(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" expected to fail on ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", but closed goal.", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", but returned: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", but returned goals:", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_19; lean_object* x_191; lean_object* x_192; 
x_191 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1);
x_192 = l_Lean_Elab_Term_elabTerm(x_1, x_191, x_2, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec_ref(x_192);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_193);
x_195 = lean_infer_type(x_193, x_10, x_11, x_12, x_13, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = l_Lean_Meta_CheckTactic_mkCheckGoalType(x_193, x_196, x_10, x_11, x_12, x_13, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec_ref(x_198);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_199);
x_202 = 0;
x_203 = lean_box(0);
lean_inc_ref(x_10);
x_204 = l_Lean_Meta_mkFreshExprMVar(x_201, x_202, x_203, x_10, x_11, x_12, x_13, x_200);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; size_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec_ref(x_204);
x_207 = l_Lean_Expr_mvarId_x21(x_205);
lean_dec(x_205);
x_208 = lean_box(0);
x_209 = 0;
x_210 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__8;
x_211 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0;
x_212 = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1;
x_213 = 5;
lean_inc(x_5);
x_214 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_211);
lean_ctor_set(x_214, 2, x_5);
lean_ctor_set(x_214, 3, x_5);
lean_ctor_set_usize(x_214, 4, x_213);
x_215 = lean_box(1);
x_216 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_216, 0, x_191);
lean_ctor_set(x_216, 1, x_208);
lean_ctor_set(x_216, 2, x_214);
lean_ctor_set(x_216, 3, x_210);
lean_ctor_set(x_216, 4, x_215);
lean_ctor_set(x_216, 5, x_215);
lean_ctor_set(x_216, 6, x_191);
lean_ctor_set_uint8(x_216, sizeof(void*)*7, x_2);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 1, x_2);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 2, x_209);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 3, x_2);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 4, x_2);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 5, x_209);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 6, x_209);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 7, x_209);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 8, x_2);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 9, x_209);
lean_ctor_set_uint8(x_216, sizeof(void*)*7 + 10, x_2);
x_217 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_217, 0, x_6);
lean_ctor_set(x_217, 1, x_215);
lean_ctor_set(x_217, 2, x_208);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set(x_217, 4, x_208);
lean_ctor_set(x_217, 5, x_215);
lean_ctor_set(x_217, 6, x_208);
lean_inc(x_3);
x_218 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed), 11, 4);
lean_closure_set(x_218, 0, x_207);
lean_closure_set(x_218, 1, x_3);
lean_closure_set(x_218, 2, x_216);
lean_closure_set(x_218, 3, x_217);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_219 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_218, x_8, x_9, x_10, x_11, x_12, x_13, x_206);
if (lean_obj_tag(x_219) == 0)
{
x_19 = x_219;
goto block_190;
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
x_224 = l_Lean_Exception_isInterrupt(x_220);
if (x_224 == 0)
{
uint8_t x_225; 
x_225 = l_Lean_Exception_isRuntime(x_220);
lean_dec(x_220);
x_222 = x_225;
goto block_223;
}
else
{
lean_dec(x_220);
x_222 = x_224;
goto block_223;
}
block_223:
{
if (x_222 == 0)
{
lean_dec_ref(x_219);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_15 = x_221;
goto block_18;
}
else
{
lean_dec(x_221);
x_19 = x_219;
goto block_190;
}
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_204);
if (x_226 == 0)
{
return x_204;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_204, 0);
x_228 = lean_ctor_get(x_204, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_204);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_198);
if (x_230 == 0)
{
return x_198;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_198, 0);
x_232 = lean_ctor_get(x_198, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_198);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_193);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_195);
if (x_234 == 0)
{
return x_195;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_195, 0);
x_236 = lean_ctor_get(x_195, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_195);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_192);
if (x_238 == 0)
{
return x_192;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_192, 0);
x_240 = lean_ctor_get(x_192, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_192);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
block_190:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_15 = x_21;
goto block_18;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec_ref(x_19);
x_27 = l_Lean_MessageData_ofSyntax(x_3);
x_28 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_28);
lean_ctor_set(x_22, 0, x_27);
x_29 = l_Lean_MessageData_ofSyntax(x_1);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_32, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec_ref(x_19);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_dec(x_38);
x_39 = l_Lean_MVarId_getType(x_37, x_10, x_11, x_12, x_13, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_42 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_4, x_40, x_10, x_11, x_12, x_13, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_dec(x_47);
x_48 = l_Lean_indentExpr(x_46);
x_49 = l_Lean_MessageData_ofSyntax(x_3);
x_50 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_50);
lean_ctor_set(x_43, 0, x_49);
x_51 = l_Lean_MessageData_ofSyntax(x_1);
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_51);
lean_ctor_set(x_24, 0, x_43);
x_52 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_52);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_22);
lean_ctor_set(x_53, 1, x_48);
x_54 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_53, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
lean_dec(x_43);
x_56 = l_Lean_indentExpr(x_55);
x_57 = l_Lean_MessageData_ofSyntax(x_3);
x_58 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_MessageData_ofSyntax(x_1);
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_60);
lean_ctor_set(x_24, 0, x_59);
x_61 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_61);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_22);
lean_ctor_set(x_62, 1, x_56);
x_63 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_free_object(x_24);
lean_free_object(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_42);
if (x_64 == 0)
{
return x_42;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_42, 0);
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_42);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_free_object(x_24);
lean_free_object(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_39);
if (x_68 == 0)
{
return x_39;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_39, 0);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_39);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_24, 0);
lean_inc(x_72);
lean_dec(x_24);
x_73 = l_Lean_MVarId_getType(x_72, x_10, x_11, x_12, x_13, x_35);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_76 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_4, x_74, x_10, x_11, x_12, x_13, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = l_Lean_indentExpr(x_79);
x_82 = l_Lean_MessageData_ofSyntax(x_3);
x_83 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(7, 2, 0);
} else {
 x_84 = x_80;
 lean_ctor_set_tag(x_84, 7);
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_MessageData_ofSyntax(x_1);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_87);
lean_ctor_set(x_22, 0, x_86);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_22);
lean_ctor_set(x_88, 1, x_81);
x_89 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_88, x_8, x_9, x_10, x_11, x_12, x_13, x_78);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_90 = lean_ctor_get(x_76, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_92 = x_76;
} else {
 lean_dec_ref(x_76);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_94 = lean_ctor_get(x_73, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_73, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_96 = x_73;
} else {
 lean_dec_ref(x_73);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_19, 1);
lean_inc(x_98);
lean_dec_ref(x_19);
x_99 = !lean_is_exclusive(x_34);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_34, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_34, 0);
lean_dec(x_101);
x_102 = l_Lean_MessageData_ofSyntax(x_3);
x_103 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_103);
lean_ctor_set(x_34, 0, x_102);
x_104 = l_Lean_MessageData_ofSyntax(x_1);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_104);
lean_ctor_set(x_22, 0, x_34);
x_105 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_22);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_107 = l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(x_4, x_106, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_98);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_108, x_8, x_9, x_10, x_11, x_12, x_13, x_109);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_110;
}
else
{
uint8_t x_111; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
return x_107;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_107, 0);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_107);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_34);
x_115 = l_Lean_MessageData_ofSyntax(x_3);
x_116 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_MessageData_ofSyntax(x_1);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_118);
lean_ctor_set(x_22, 0, x_117);
x_119 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_22);
lean_ctor_set(x_120, 1, x_119);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_121 = l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(x_4, x_120, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_98);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_122, x_8, x_9, x_10, x_11, x_12, x_13, x_123);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_127 = x_121;
} else {
 lean_dec_ref(x_121);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_22, 0);
lean_inc(x_129);
lean_dec(x_22);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_19, 1);
lean_inc(x_130);
lean_dec_ref(x_19);
x_131 = l_Lean_MessageData_ofSyntax(x_3);
x_132 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_MessageData_ofSyntax(x_1);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_137, x_8, x_9, x_10, x_11, x_12, x_13, x_130);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_138;
}
else
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_129, 1);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_19, 1);
lean_inc(x_140);
lean_dec_ref(x_19);
x_141 = lean_ctor_get(x_129, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_142 = x_129;
} else {
 lean_dec_ref(x_129);
 x_142 = lean_box(0);
}
x_143 = l_Lean_MVarId_getType(x_141, x_10, x_11, x_12, x_13, x_140);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_146 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_4, x_144, x_10, x_11, x_12, x_13, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = l_Lean_indentExpr(x_149);
x_152 = l_Lean_MessageData_ofSyntax(x_3);
x_153 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(7, 2, 0);
} else {
 x_154 = x_150;
 lean_ctor_set_tag(x_154, 7);
}
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_MessageData_ofSyntax(x_1);
if (lean_is_scalar(x_142)) {
 x_156 = lean_alloc_ctor(7, 2, 0);
} else {
 x_156 = x_142;
 lean_ctor_set_tag(x_156, 7);
}
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5;
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_151);
x_160 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_159, x_8, x_9, x_10, x_11, x_12, x_13, x_148);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_142);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_161 = lean_ctor_get(x_146, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_146, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_163 = x_146;
} else {
 lean_dec_ref(x_146);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_142);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_165 = lean_ctor_get(x_143, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_143, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_167 = x_143;
} else {
 lean_dec_ref(x_143);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_169 = lean_ctor_get(x_19, 1);
lean_inc(x_169);
lean_dec_ref(x_19);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_170 = x_139;
} else {
 lean_dec_ref(x_139);
 x_170 = lean_box(0);
}
x_171 = l_Lean_MessageData_ofSyntax(x_3);
x_172 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(7, 2, 0);
} else {
 x_173 = x_170;
 lean_ctor_set_tag(x_173, 7);
}
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_MessageData_ofSyntax(x_1);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_178 = l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(x_4, x_177, x_129, x_8, x_9, x_10, x_11, x_12, x_13, x_169);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = l_Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(x_4, x_179, x_8, x_9, x_10, x_11, x_12, x_13, x_180);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_184 = x_178;
} else {
 lean_dec_ref(x_178);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_19);
if (x_186 == 0)
{
return x_19;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_19, 0);
x_188 = lean_ctor_get(x_19, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_19);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkTacticFailure", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_box(0);
x_18 = lean_box(x_6);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed), 14, 6);
lean_closure_set(x_19, 0, x_14);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_16);
lean_closure_set(x_19, 3, x_1);
lean_closure_set(x_19, 4, x_12);
lean_closure_set(x_19, 5, x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Environment_unlockAsync(x_11);
x_22 = l_Lean_withEnv___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__7___redArg(x_21, x_20, x_2, x_3, x_10);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
x_16 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_7);
lean_dec(x_4);
return x_16;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabCheckTacticFailure", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1;
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1;
x_4 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_unsigned_to_nat(73u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkSimp", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#check_tactic", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("~>", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("by", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6;
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1;
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8;
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1;
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_7 = lean_ctor_get(x_2, 5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_7, x_12);
x_14 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3;
x_15 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2;
lean_inc(x_13);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3;
lean_inc(x_13);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4;
lean_inc(x_13);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6;
x_22 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7;
lean_inc(x_13);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9;
x_25 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11;
x_26 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12;
lean_inc(x_13);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
lean_inc_ref(x_27);
lean_inc(x_13);
x_28 = l_Lean_Syntax_node1(x_13, x_24, x_27);
lean_inc_ref_n(x_27, 3);
lean_inc(x_13);
x_29 = l_Lean_Syntax_node6(x_13, x_22, x_23, x_28, x_27, x_27, x_27, x_27);
x_30 = l_Lean_Syntax_node6(x_13, x_14, x_16, x_9, x_18, x_11, x_20, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimp(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandCheckSimp", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1;
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0;
x_3 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1;
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimp___boxed), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(76u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = lean_unsigned_to_nat(78u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(76u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_unsigned_to_nat(76u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5;
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__2;
x_3 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkSimpFailure", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#check_tactic_failure", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_7 = lean_ctor_get(x_2, 5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = 0;
x_11 = l_Lean_SourceInfo_fromRef(x_7, x_10);
x_12 = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1;
x_13 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2;
lean_inc(x_11);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4;
lean_inc(x_11);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6;
x_18 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7;
lean_inc(x_11);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9;
x_21 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11;
x_22 = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12;
lean_inc(x_11);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc_ref(x_23);
lean_inc(x_11);
x_24 = l_Lean_Syntax_node1(x_11, x_20, x_23);
lean_inc_ref_n(x_23, 3);
lean_inc(x_11);
x_25 = l_Lean_Syntax_node6(x_11, x_18, x_19, x_24, x_23, x_23, x_23, x_23);
x_26 = l_Lean_Syntax_node4(x_11, x_12, x_14, x_9, x_16, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandCheckSimpFailure", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0;
x_2 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2;
x_3 = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1;
x_4 = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0;
x_3 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1;
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(81u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = lean_unsigned_to_nat(83u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(81u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = lean_unsigned_to_nat(81u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5;
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1;
x_3 = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CheckTactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_CheckTactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CheckTactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__1);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__0 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__0();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__0);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__1 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__1();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__1);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__2 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__2();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_spec__3___closed__2);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__0 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__0);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__1 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__1);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__2 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__2);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__3 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__3);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__4 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___redArg___closed__4);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10();
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11);
l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__12);
l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0);
l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1);
l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2);
l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__4 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__4();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__4);
if (builtin) {res = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5);
l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6 = _init_l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__8 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__8();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__8);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1);
if (builtin) {res = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5);
l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6 = _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11);
l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__2 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__2);
if (builtin) {res = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5);
l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6 = _init_l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1);
if (builtin) {res = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5);
l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6 = _init_l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
