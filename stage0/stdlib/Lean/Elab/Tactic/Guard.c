// Lean compiler output
// Module: Lean.Elab.Tactic.Guard
// Imports: Init.Guard Lean.Elab.Command Lean.Elab.Tactic.Conv.Basic Lean.Meta.Basic Lean.Meta.Eval
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__3;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__18;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__4;
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__5;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__2;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__7;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__10;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__5;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__7;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__7;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__6;
lean_object* l_Lean_Meta_evalExpr___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__7;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__4;
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__5;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__6;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__6;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__6;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__7;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__6;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__5;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__2;
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__7;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__1;
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__5;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__5;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colon", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonR", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonD", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonS", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonA", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 2;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8;
lean_inc(x_6);
x_10 = l_Lean_Syntax_isOfKind(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10;
lean_inc(x_6);
x_12 = l_Lean_Syntax_isOfKind(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12;
x_14 = l_Lean_Syntax_isOfKind(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_6);
x_17 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14;
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_6);
x_18 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16;
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__18;
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEq", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEqR", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEqD", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEqS", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colonEqA", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6;
lean_inc(x_6);
x_10 = l_Lean_Syntax_isOfKind(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8;
lean_inc(x_6);
x_12 = l_Lean_Syntax_isOfKind(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__10;
x_14 = l_Lean_Syntax_isOfKind(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_6);
x_17 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14;
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_6);
x_18 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16;
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__18;
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equal", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equalR", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equalD", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equalS", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equalA", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6;
lean_inc(x_6);
x_10 = l_Lean_Syntax_isOfKind(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8;
lean_inc(x_6);
x_12 = l_Lean_Syntax_isOfKind(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__10;
x_14 = l_Lean_Syntax_isOfKind(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_6);
x_17 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14;
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_6);
x_18 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16;
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__18;
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_ctor_set_uint8(x_10, 9, x_1);
x_12 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get_uint8(x_10, 0);
x_22 = lean_ctor_get_uint8(x_10, 1);
x_23 = lean_ctor_get_uint8(x_10, 2);
x_24 = lean_ctor_get_uint8(x_10, 3);
x_25 = lean_ctor_get_uint8(x_10, 4);
x_26 = lean_ctor_get_uint8(x_10, 5);
x_27 = lean_ctor_get_uint8(x_10, 6);
x_28 = lean_ctor_get_uint8(x_10, 7);
x_29 = lean_ctor_get_uint8(x_10, 8);
x_30 = lean_ctor_get_uint8(x_10, 10);
x_31 = lean_ctor_get_uint8(x_10, 11);
lean_dec(x_10);
x_32 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_32, 0, x_21);
lean_ctor_set_uint8(x_32, 1, x_22);
lean_ctor_set_uint8(x_32, 2, x_23);
lean_ctor_set_uint8(x_32, 3, x_24);
lean_ctor_set_uint8(x_32, 4, x_25);
lean_ctor_set_uint8(x_32, 5, x_26);
lean_ctor_set_uint8(x_32, 6, x_27);
lean_ctor_set_uint8(x_32, 7, x_28);
lean_ctor_set_uint8(x_32, 8, x_29);
lean_ctor_set_uint8(x_32, 9, x_1);
lean_ctor_set_uint8(x_32, 10, x_30);
lean_ctor_set_uint8(x_32, 11, x_31);
lean_ctor_set(x_4, 0, x_32);
x_33 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
x_44 = lean_ctor_get(x_4, 2);
x_45 = lean_ctor_get(x_4, 3);
x_46 = lean_ctor_get(x_4, 4);
x_47 = lean_ctor_get(x_4, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_48 = lean_ctor_get_uint8(x_42, 0);
x_49 = lean_ctor_get_uint8(x_42, 1);
x_50 = lean_ctor_get_uint8(x_42, 2);
x_51 = lean_ctor_get_uint8(x_42, 3);
x_52 = lean_ctor_get_uint8(x_42, 4);
x_53 = lean_ctor_get_uint8(x_42, 5);
x_54 = lean_ctor_get_uint8(x_42, 6);
x_55 = lean_ctor_get_uint8(x_42, 7);
x_56 = lean_ctor_get_uint8(x_42, 8);
x_57 = lean_ctor_get_uint8(x_42, 10);
x_58 = lean_ctor_get_uint8(x_42, 11);
if (lean_is_exclusive(x_42)) {
 x_59 = x_42;
} else {
 lean_dec_ref(x_42);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 0, 12);
} else {
 x_60 = x_59;
}
lean_ctor_set_uint8(x_60, 0, x_48);
lean_ctor_set_uint8(x_60, 1, x_49);
lean_ctor_set_uint8(x_60, 2, x_50);
lean_ctor_set_uint8(x_60, 3, x_51);
lean_ctor_set_uint8(x_60, 4, x_52);
lean_ctor_set_uint8(x_60, 5, x_53);
lean_ctor_set_uint8(x_60, 6, x_54);
lean_ctor_set_uint8(x_60, 7, x_55);
lean_ctor_set_uint8(x_60, 8, x_56);
lean_ctor_set_uint8(x_60, 9, x_1);
lean_ctor_set_uint8(x_60, 10, x_57);
lean_ctor_set_uint8(x_60, 11, x_58);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_43);
lean_ctor_set(x_61, 2, x_44);
lean_ctor_set(x_61, 3, x_45);
lean_ctor_set(x_61, 4, x_46);
lean_ctor_set(x_61, 5, x_47);
x_62 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_61, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = l_Lean_Expr_consumeMData(x_1);
lean_dec(x_1);
x_10 = l_Lean_Expr_consumeMData(x_2);
lean_dec(x_2);
x_11 = lean_expr_eqv(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
case 1:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get_uint8(x_3, 0);
lean_dec(x_3);
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lambda__1___boxed), 8, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
x_17 = l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___spec__1(x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
default: 
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lambda__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_13 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_12, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_elabTerm(x_3, x_2, x_12, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_19 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_17);
x_22 = lean_infer_type(x_17, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_Meta_isExprDefEqGuarded(x_20, x_23, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_27, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_6);
lean_dec(x_5);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_31, x_34, x_4, x_7, x_8, x_9, x_10, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_22);
if (x_45 == 0)
{
return x_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_22, 0);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_22);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
return x_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_16);
if (x_53 == 0)
{
return x_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
return x_13;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_13, 0);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_13);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lambda__1), 11, 4);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_1);
x_13 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed: ", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not true", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_MessageData_ofSyntax(x_2);
x_19 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_MessageData_ofSyntax(x_4);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofSyntax(x_3);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__8;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_14, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardExpr", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardExprConv", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2;
lean_inc(x_19);
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_1);
lean_inc(x_19);
x_25 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_17);
x_26 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6;
x_27 = l_Lean_Elab_Tactic_withMainContext___rarg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___boxed), 13, 4);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_17);
lean_closure_set(x_29, 2, x_24);
lean_closure_set(x_29, 3, x_19);
x_30 = l_Lean_Elab_Tactic_withMainContext___rarg(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
x_35 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2;
lean_inc(x_34);
x_36 = l_Lean_Syntax_isOfKind(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_unsigned_to_nat(3u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
lean_dec(x_1);
lean_inc(x_34);
x_40 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_32);
x_41 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6;
x_42 = l_Lean_Elab_Tactic_withMainContext___rarg(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___boxed), 13, 4);
lean_closure_set(x_44, 0, x_43);
lean_closure_set(x_44, 1, x_32);
lean_closure_set(x_44, 2, x_39);
lean_closure_set(x_44, 3, x_34);
x_45 = l_Lean_Elab_Tactic_withMainContext___rarg(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("GuardExpr", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGuardExpr", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(75u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(82u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(75u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(75u);
x_2 = lean_unsigned_to_nat(17u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__5;
x_4 = lean_unsigned_to_nat(17u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGuardExprConv", 17);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(86u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(86u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__2;
x_4 = lean_unsigned_to_nat(47u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(86u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(86u);
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__5;
x_4 = lean_unsigned_to_nat(21u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("target of main goal is", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nnot", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Tactic_Conv_getLhs(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_16);
x_18 = lean_infer_type(x_16, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Elab_Tactic_elabTerm(x_1, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_2);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___rarg(x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_16);
lean_inc(x_24);
x_29 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_24, x_16, x_28, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_indentExpr(x_16);
x_34 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__2;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_indentExpr(x_24);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_29);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_29, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_29, 0, x_45);
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_29);
if (x_49 == 0)
{
return x_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_23);
if (x_53 == 0)
{
return x_23;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_23, 0);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_23);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_18);
if (x_57 == 0)
{
return x_18;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_18, 0);
x_59 = lean_ctor_get(x_18, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_18);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
return x_12;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_12);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Tactic_getMainTarget(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_16);
x_18 = lean_infer_type(x_16, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Elab_Tactic_elabTerm(x_1, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_2);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___rarg(x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_16);
lean_inc(x_24);
x_29 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_24, x_16, x_28, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_indentExpr(x_16);
x_34 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__2;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_indentExpr(x_24);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_29);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_29, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_29, 0, x_45);
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_29);
if (x_49 == 0)
{
return x_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_23);
if (x_53 == 0)
{
return x_23;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_23, 0);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_23);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_18);
if (x_57 == 0)
{
return x_18;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_18, 0);
x_59 = lean_ctor_get(x_18, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_18);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
return x_12;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_12);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardTarget", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardTargetConv", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4;
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1), 11, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_17);
x_21 = l_Lean_Elab_Tactic_withMainContext___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__2), 11, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_23);
x_27 = l_Lean_Elab_Tactic_withMainContext___rarg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGuardTarget", 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(89u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(99u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(89u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(89u);
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__5;
x_4 = lean_unsigned_to_nat(19u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGuardTargetConv", 19);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(103u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(103u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__2;
x_4 = lean_unsigned_to_nat(51u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(103u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(103u);
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__5;
x_4 = lean_unsigned_to_nat(23u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
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
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not a let binding", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is a let binding", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hypothesis ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" has value", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_LocalDecl_value_x3f(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_18 = l_Lean_MessageData_ofSyntax(x_3);
x_19 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_23;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_4);
x_24 = l_Lean_MessageData_ofSyntax(x_3);
x_25 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_29;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_30; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_14);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
lean_dec(x_4);
x_34 = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_35 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_14);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = l_Lean_LocalDecl_type(x_1);
lean_ctor_set(x_34, 0, x_38);
x_39 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Lean_Elab_Tactic_elabTerm(x_32, x_34, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_44);
lean_inc(x_41);
x_46 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_41, x_44, x_37, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_MessageData_ofSyntax(x_3);
x_51 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__8;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_indentExpr(x_44);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_indentExpr(x_41);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_49);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_46);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_46, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_46, 0, x_66);
return x_46;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_46, 1);
lean_inc(x_67);
lean_dec(x_46);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_46);
if (x_70 == 0)
{
return x_46;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_46, 0);
x_72 = lean_ctor_get(x_46, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_46);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_40);
if (x_74 == 0)
{
return x_40;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_40, 0);
x_76 = lean_ctor_get(x_40, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_40);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_34, 0);
lean_inc(x_78);
lean_dec(x_34);
x_79 = l_Lean_LocalDecl_type(x_1);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_82 = l_Lean_Elab_Tactic_elabTerm(x_32, x_80, x_81, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_86);
lean_inc(x_83);
x_88 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_83, x_86, x_78, x_10, x_11, x_12, x_13, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = l_Lean_MessageData_ofSyntax(x_3);
x_93 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__8;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_indentExpr(x_86);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_indentExpr(x_83);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_104, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_91);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_106 = lean_ctor_get(x_88, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_107 = x_88;
} else {
 lean_dec_ref(x_88);
 x_107 = lean_box(0);
}
x_108 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_110 = lean_ctor_get(x_88, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_88, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_112 = x_88;
} else {
 lean_dec_ref(x_88);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_78);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_114 = lean_ctor_get(x_82, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_82, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_116 = x_82;
} else {
 lean_dec_ref(x_82);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" has type", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1(x_6, x_1, x_2, x_3, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_17;
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1(x_6, x_1, x_2, x_3, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
lean_dec(x_5);
x_22 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___rarg(x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Elab_Tactic_elabTerm(x_21, x_29, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_LocalDecl_type(x_6);
x_35 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_36);
lean_inc(x_32);
x_38 = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(x_32, x_36, x_28, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_MessageData_ofSyntax(x_2);
x_43 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__2;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_indentExpr(x_36);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_indentExpr(x_32);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_54, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_36);
lean_dec(x_32);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
x_61 = lean_box(0);
x_62 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1(x_6, x_1, x_2, x_3, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_60);
lean_dec(x_6);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
return x_38;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_38, 0);
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_38);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_31);
if (x_67 == 0)
{
return x_31;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_31, 0);
x_69 = lean_ctor_get(x_31, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_31);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" not found", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Elab_Tactic_getFVarId(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
x_19 = lean_local_ctx_find(x_18, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_MessageData_ofSyntax(x_1);
x_21 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___spec__1(x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2(x_2, x_1, x_3, x_4, x_5, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3), 14, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_6);
lean_closure_set(x_16, 2, x_5);
lean_closure_set(x_16, 3, x_2);
lean_closure_set(x_16, 4, x_3);
x_17 = l_Lean_Elab_Tactic_withMainContext___rarg(x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(2u);
lean_inc(x_16);
x_19 = l_Lean_Syntax_matchesNull(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_16, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_16, x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__4(x_2, x_4, x_5, x_27, x_25, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__4(x_2, x_4, x_5, x_30, x_29, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardHyp", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardHypConv", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__4;
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_isNone(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc(x_19);
x_21 = l_Lean_Syntax_matchesNull(x_19, x_18);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_19, x_23);
x_25 = l_Lean_Syntax_getArg(x_19, x_16);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__5(x_1, x_17, x_28, x_26, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__5(x_1, x_17, x_31, x_30, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
x_37 = l_Lean_Syntax_isNone(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc(x_36);
x_38 = l_Lean_Syntax_matchesNull(x_36, x_35);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Syntax_getArg(x_36, x_40);
x_42 = l_Lean_Syntax_getArg(x_36, x_33);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_box(0);
x_46 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__5(x_1, x_34, x_45, x_43, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_36);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__5(x_1, x_34, x_48, x_47, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_16;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGuardHyp", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(106u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(130u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(106u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(106u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__5;
x_4 = lean_unsigned_to_nat(16u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGuardHypConv", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__4;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(133u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(133u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__2;
x_4 = lean_unsigned_to_nat(45u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(133u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(133u);
x_2 = lean_unsigned_to_nat(20u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__5;
x_4 = lean_unsigned_to_nat(20u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2___rarg(x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(x_14, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_MessageData_ofSyntax(x_2);
x_20 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_ofSyntax(x_1);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__6;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofSyntax(x_3);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__8;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_15, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_15, 0, x_35);
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_dec(x_15);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardExprCmd", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1;
x_4 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2;
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lambda__1___boxed), 11, 3);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_9);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_Elab_Command_runTermElabM___rarg(x_17, x_2, x_3, x_4);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGuardExprCmd", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(136u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(143u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(136u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(136u);
x_2 = lean_unsigned_to_nat(20u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__5;
x_4 = lean_unsigned_to_nat(20u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__3;
x_8 = 1;
x_9 = l_Lean_Meta_evalExpr___rarg(x_7, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expression", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\ndid not evaluate to `true`", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_2, x_11, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_15, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
x_21 = l_Lean_Meta_getMVars(x_19, x_6, x_7, x_8, x_9, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Array_isEmpty___rarg(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_19);
x_25 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_22);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
x_36 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(x_19, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_indentExpr(x_19);
x_41 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_36, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_36, 0, x_48);
return x_36;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_dec(x_36);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_16);
if (x_56 == 0)
{
return x_16;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_16, 0);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_16);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_12);
if (x_60 == 0)
{
return x_12;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_12, 0);
x_62 = lean_ctor_get(x_12, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_12);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardCmd", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1;
x_4 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3;
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1), 10, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_10);
x_13 = l_Lean_Elab_Command_liftTermElabM___rarg(x_12, x_2, x_3, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGuardCmd", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3;
x_3 = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(146u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(158u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(146u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(146u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__5;
x_4 = lean_unsigned_to_nat(16u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init_Guard(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Guard(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Guard(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17);
l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__18 = _init_l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__18);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9);
l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__10 = _init_l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__10);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9);
l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__10 = _init_l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__10);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__3);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__4);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__5);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__6);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__7 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__7);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__8 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lambda__1___closed__8);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__6);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__3);
l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lambda__1___closed__4);
l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3);
l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__3);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__4);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__5);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__6);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__7 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__7);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__8 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__1___closed__8);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__2___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lambda__3___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3);
l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___spec__1___rarg___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__3);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__3);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lambda__1___closed__4);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2);
l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3 = _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
