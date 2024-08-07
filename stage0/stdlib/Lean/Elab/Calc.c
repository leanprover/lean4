// Lean compiler output
// Module: Lean.Elab.Calc
// Imports: Lean.Elab.App
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__2;
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcSteps___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__8;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__4;
static lean_object* l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1___closed__1;
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__1;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcFirstStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__8;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
static lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcSteps___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__15;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__12;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__2;
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__1;
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__14;
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcSteps___closed__4;
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__3;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__1;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__12;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__7;
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__9;
static lean_object* l_Lean_Elab_Term_getCalcSteps___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__5;
lean_object* l_Lean_Core_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3(lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__14;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__10;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__11;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__9;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__9;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_decLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__3;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__2;
static lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__5;
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__15;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__7;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__13;
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcFirstStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__3;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_useDiagnosticMsg;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__7;
lean_object* l_Lean_Expr_headBeta(lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcFirstStep___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__2;
static lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__6;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__4;
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__3;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_getCalcSteps___closed__5;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appFn_x21(x_11);
x_13 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_14 = l_Lean_Expr_appArg_x21(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected relation type", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 3)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_Lean_indentExpr(x_1);
x_19 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_decLevel___spec__1(x_22, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___boxed), 8, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = 0;
x_12 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_10, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Calc", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.mkCalcTrans", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__1;
x_2 = l_Lean_Elab_Term_mkCalcTrans___closed__2;
x_3 = lean_unsigned_to_nat(29u);
x_4 = lean_unsigned_to_nat(53u);
x_5 = l_Lean_Elab_Term_mkCalcTrans___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__1;
x_2 = l_Lean_Elab_Term_mkCalcTrans___closed__2;
x_3 = lean_unsigned_to_nat(30u);
x_4 = lean_unsigned_to_nat(72u);
x_5 = l_Lean_Elab_Term_mkCalcTrans___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Trans", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkCalcTrans___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trans", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__6;
x_2 = l_Lean_Elab_Term_mkCalcTrans___closed__11;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_getCalcRelation_x3f(x_2, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_mkCalcTrans___closed__4;
x_14 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(x_13, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
x_24 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_4, x_5, x_6, x_7, x_8, x_17);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_Elab_Term_getCalcRelation_x3f(x_26, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_mkCalcTrans___closed__5;
x_32 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(x_31, x_5, x_6, x_7, x_8, x_30);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_28, 1);
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 1);
x_44 = lean_ctor_get(x_35, 0);
lean_dec(x_44);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_45 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_40);
x_48 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_40, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_51 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_54 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_43);
x_57 = lean_infer_type(x_43, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_52);
x_60 = l_Lean_Meta_getLevel(x_52, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_55);
x_63 = l_Lean_Meta_getLevel(x_55, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_58);
x_66 = l_Lean_Meta_getLevel(x_58, x_5, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_68);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
x_73 = l_Lean_Expr_sort___override(x_71);
lean_inc(x_58);
x_74 = l_Lean_mkArrow(x_58, x_73, x_7, x_8, x_72);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_52);
x_78 = l_Lean_mkArrow(x_52, x_76, x_7, x_8, x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_ctor_set(x_29, 0, x_80);
x_82 = 0;
x_83 = lean_box(0);
lean_inc(x_5);
x_84 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_82, x_83, x_5, x_6, x_7, x_8, x_81);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
x_88 = lean_box(0);
lean_ctor_set_tag(x_84, 1);
lean_ctor_set(x_84, 1, x_88);
lean_ctor_set(x_84, 0, x_67);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_84);
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 1, x_78);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 1, x_74);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_69);
lean_ctor_set(x_35, 0, x_49);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_46);
x_89 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_90 = l_Lean_Expr_const___override(x_89, x_34);
x_91 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_92 = lean_array_push(x_91, x_52);
lean_inc(x_55);
x_93 = lean_array_push(x_92, x_55);
lean_inc(x_58);
x_94 = lean_array_push(x_93, x_58);
lean_inc(x_19);
x_95 = lean_array_push(x_94, x_19);
lean_inc(x_40);
x_96 = lean_array_push(x_95, x_40);
lean_inc(x_86);
x_97 = lean_array_push(x_96, x_86);
x_98 = l_Lean_mkAppN(x_90, x_97);
lean_dec(x_97);
x_99 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_98);
x_100 = l_Lean_Meta_trySynthInstance(x_98, x_99, x_5, x_6, x_7, x_8, x_87);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 1)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_98);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_105 = l_Lean_Expr_const___override(x_104, x_34);
x_106 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_107 = lean_array_push(x_106, x_52);
x_108 = lean_array_push(x_107, x_55);
x_109 = lean_array_push(x_108, x_58);
x_110 = lean_array_push(x_109, x_19);
x_111 = lean_array_push(x_110, x_40);
x_112 = lean_array_push(x_111, x_86);
x_113 = lean_array_push(x_112, x_103);
x_114 = lean_array_push(x_113, x_22);
x_115 = lean_array_push(x_114, x_23);
x_116 = lean_array_push(x_115, x_43);
x_117 = lean_array_push(x_116, x_1);
x_118 = lean_array_push(x_117, x_3);
x_119 = l_Lean_mkAppN(x_105, x_118);
lean_dec(x_118);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_119);
x_120 = lean_infer_type(x_119, x_5, x_6, x_7, x_8, x_102);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_121, x_5, x_6, x_7, x_8, x_122);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
x_127 = l_Lean_Expr_headBeta(x_125);
x_128 = l_Lean_Elab_Term_getCalcRelation_x3f(x_127, x_5, x_6, x_7, x_8, x_126);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
lean_dec(x_119);
x_130 = !lean_is_exclusive(x_128);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_131 = lean_ctor_get(x_128, 1);
x_132 = lean_ctor_get(x_128, 0);
lean_dec(x_132);
x_133 = l_Lean_indentExpr(x_127);
x_134 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_133);
lean_ctor_set(x_128, 0, x_134);
x_135 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_123, 7);
lean_ctor_set(x_123, 1, x_135);
lean_ctor_set(x_123, 0, x_128);
x_136 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_123, x_5, x_6, x_7, x_8, x_131);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
return x_136;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_136);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_141 = lean_ctor_get(x_128, 1);
lean_inc(x_141);
lean_dec(x_128);
x_142 = l_Lean_indentExpr(x_127);
x_143 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_123, 7);
lean_ctor_set(x_123, 1, x_145);
lean_ctor_set(x_123, 0, x_144);
x_146 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_123, x_5, x_6, x_7, x_8, x_141);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_129);
lean_free_object(x_123);
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
lean_dec(x_128);
x_152 = lean_box(0);
x_153 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_119, x_127, x_152, x_5, x_6, x_7, x_8, x_151);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_156 = l_Lean_Expr_headBeta(x_154);
x_157 = l_Lean_Elab_Term_getCalcRelation_x3f(x_156, x_5, x_6, x_7, x_8, x_155);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_119);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = l_Lean_indentExpr(x_156);
x_162 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_160)) {
 x_163 = lean_alloc_ctor(7, 2, 0);
} else {
 x_163 = x_160;
 lean_ctor_set_tag(x_163, 7);
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_165, x_5, x_6, x_7, x_8, x_159);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_158);
x_171 = lean_ctor_get(x_157, 1);
lean_inc(x_171);
lean_dec(x_157);
x_172 = lean_box(0);
x_173 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_119, x_156, x_172, x_5, x_6, x_7, x_8, x_171);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_119);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_174 = !lean_is_exclusive(x_120);
if (x_174 == 0)
{
return x_120;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_120, 0);
x_176 = lean_ctor_get(x_120, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_120);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_101);
lean_dec(x_34);
lean_dec(x_86);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_178 = lean_ctor_get(x_100, 1);
lean_inc(x_178);
lean_dec(x_100);
x_179 = l_Lean_indentExpr(x_98);
x_180 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_179);
lean_ctor_set(x_28, 0, x_180);
x_181 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_181);
lean_ctor_set(x_24, 0, x_28);
x_182 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_182);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_181);
lean_ctor_set(x_15, 0, x_16);
x_183 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_178);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_183;
}
}
else
{
uint8_t x_184; 
lean_dec(x_98);
lean_dec(x_34);
lean_dec(x_86);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_100);
if (x_184 == 0)
{
return x_100;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_100, 0);
x_186 = lean_ctor_get(x_100, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_100);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_188 = lean_ctor_get(x_84, 0);
x_189 = lean_ctor_get(x_84, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_84);
x_190 = lean_box(0);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_67);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_191);
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 1, x_78);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 1, x_74);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_69);
lean_ctor_set(x_35, 0, x_49);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_46);
x_192 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_193 = l_Lean_Expr_const___override(x_192, x_34);
x_194 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_195 = lean_array_push(x_194, x_52);
lean_inc(x_55);
x_196 = lean_array_push(x_195, x_55);
lean_inc(x_58);
x_197 = lean_array_push(x_196, x_58);
lean_inc(x_19);
x_198 = lean_array_push(x_197, x_19);
lean_inc(x_40);
x_199 = lean_array_push(x_198, x_40);
lean_inc(x_188);
x_200 = lean_array_push(x_199, x_188);
x_201 = l_Lean_mkAppN(x_193, x_200);
lean_dec(x_200);
x_202 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_201);
x_203 = l_Lean_Meta_trySynthInstance(x_201, x_202, x_5, x_6, x_7, x_8, x_189);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 1)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_201);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_208 = l_Lean_Expr_const___override(x_207, x_34);
x_209 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_210 = lean_array_push(x_209, x_52);
x_211 = lean_array_push(x_210, x_55);
x_212 = lean_array_push(x_211, x_58);
x_213 = lean_array_push(x_212, x_19);
x_214 = lean_array_push(x_213, x_40);
x_215 = lean_array_push(x_214, x_188);
x_216 = lean_array_push(x_215, x_206);
x_217 = lean_array_push(x_216, x_22);
x_218 = lean_array_push(x_217, x_23);
x_219 = lean_array_push(x_218, x_43);
x_220 = lean_array_push(x_219, x_1);
x_221 = lean_array_push(x_220, x_3);
x_222 = l_Lean_mkAppN(x_208, x_221);
lean_dec(x_221);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_222);
x_223 = lean_infer_type(x_222, x_5, x_6, x_7, x_8, x_205);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_224, x_5, x_6, x_7, x_8, x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = l_Lean_Expr_headBeta(x_227);
x_231 = l_Lean_Elab_Term_getCalcRelation_x3f(x_230, x_5, x_6, x_7, x_8, x_228);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_222);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
x_235 = l_Lean_indentExpr(x_230);
x_236 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_234)) {
 x_237 = lean_alloc_ctor(7, 2, 0);
} else {
 x_237 = x_234;
 lean_ctor_set_tag(x_237, 7);
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
x_238 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_229)) {
 x_239 = lean_alloc_ctor(7, 2, 0);
} else {
 x_239 = x_229;
 lean_ctor_set_tag(x_239, 7);
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_239, x_5, x_6, x_7, x_8, x_233);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_232);
lean_dec(x_229);
x_245 = lean_ctor_get(x_231, 1);
lean_inc(x_245);
lean_dec(x_231);
x_246 = lean_box(0);
x_247 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_222, x_230, x_246, x_5, x_6, x_7, x_8, x_245);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_222);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_248 = lean_ctor_get(x_223, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_223, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_250 = x_223;
} else {
 lean_dec_ref(x_223);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_204);
lean_dec(x_34);
lean_dec(x_188);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_252 = lean_ctor_get(x_203, 1);
lean_inc(x_252);
lean_dec(x_203);
x_253 = l_Lean_indentExpr(x_201);
x_254 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_253);
lean_ctor_set(x_28, 0, x_254);
x_255 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_255);
lean_ctor_set(x_24, 0, x_28);
x_256 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_256);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_255);
lean_ctor_set(x_15, 0, x_16);
x_257 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_252);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_201);
lean_dec(x_34);
lean_dec(x_188);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_258 = lean_ctor_get(x_203, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_203, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_260 = x_203;
} else {
 lean_dec_ref(x_203);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_262 = lean_ctor_get(x_78, 0);
x_263 = lean_ctor_get(x_78, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_78);
lean_ctor_set(x_29, 0, x_262);
x_264 = 0;
x_265 = lean_box(0);
lean_inc(x_5);
x_266 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_264, x_265, x_5, x_6, x_7, x_8, x_263);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_270 = lean_box(0);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_269;
 lean_ctor_set_tag(x_271, 1);
}
lean_ctor_set(x_271, 0, x_67);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_64);
lean_ctor_set(x_272, 1, x_271);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 1, x_272);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 1, x_74);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_69);
lean_ctor_set(x_35, 0, x_49);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_46);
x_273 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_274 = l_Lean_Expr_const___override(x_273, x_34);
x_275 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_276 = lean_array_push(x_275, x_52);
lean_inc(x_55);
x_277 = lean_array_push(x_276, x_55);
lean_inc(x_58);
x_278 = lean_array_push(x_277, x_58);
lean_inc(x_19);
x_279 = lean_array_push(x_278, x_19);
lean_inc(x_40);
x_280 = lean_array_push(x_279, x_40);
lean_inc(x_267);
x_281 = lean_array_push(x_280, x_267);
x_282 = l_Lean_mkAppN(x_274, x_281);
lean_dec(x_281);
x_283 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_282);
x_284 = l_Lean_Meta_trySynthInstance(x_282, x_283, x_5, x_6, x_7, x_8, x_268);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 1)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_282);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_ctor_get(x_285, 0);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_289 = l_Lean_Expr_const___override(x_288, x_34);
x_290 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_291 = lean_array_push(x_290, x_52);
x_292 = lean_array_push(x_291, x_55);
x_293 = lean_array_push(x_292, x_58);
x_294 = lean_array_push(x_293, x_19);
x_295 = lean_array_push(x_294, x_40);
x_296 = lean_array_push(x_295, x_267);
x_297 = lean_array_push(x_296, x_287);
x_298 = lean_array_push(x_297, x_22);
x_299 = lean_array_push(x_298, x_23);
x_300 = lean_array_push(x_299, x_43);
x_301 = lean_array_push(x_300, x_1);
x_302 = lean_array_push(x_301, x_3);
x_303 = l_Lean_mkAppN(x_289, x_302);
lean_dec(x_302);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_303);
x_304 = lean_infer_type(x_303, x_5, x_6, x_7, x_8, x_286);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_305, x_5, x_6, x_7, x_8, x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_310 = x_307;
} else {
 lean_dec_ref(x_307);
 x_310 = lean_box(0);
}
x_311 = l_Lean_Expr_headBeta(x_308);
x_312 = l_Lean_Elab_Term_getCalcRelation_x3f(x_311, x_5, x_6, x_7, x_8, x_309);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_303);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_315 = x_312;
} else {
 lean_dec_ref(x_312);
 x_315 = lean_box(0);
}
x_316 = l_Lean_indentExpr(x_311);
x_317 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_315)) {
 x_318 = lean_alloc_ctor(7, 2, 0);
} else {
 x_318 = x_315;
 lean_ctor_set_tag(x_318, 7);
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_316);
x_319 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_310)) {
 x_320 = lean_alloc_ctor(7, 2, 0);
} else {
 x_320 = x_310;
 lean_ctor_set_tag(x_320, 7);
}
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
x_321 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_320, x_5, x_6, x_7, x_8, x_314);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_324 = x_321;
} else {
 lean_dec_ref(x_321);
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
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_313);
lean_dec(x_310);
x_326 = lean_ctor_get(x_312, 1);
lean_inc(x_326);
lean_dec(x_312);
x_327 = lean_box(0);
x_328 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_303, x_311, x_327, x_5, x_6, x_7, x_8, x_326);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_303);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_329 = lean_ctor_get(x_304, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_304, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_331 = x_304;
} else {
 lean_dec_ref(x_304);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_285);
lean_dec(x_34);
lean_dec(x_267);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_333 = lean_ctor_get(x_284, 1);
lean_inc(x_333);
lean_dec(x_284);
x_334 = l_Lean_indentExpr(x_282);
x_335 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_334);
lean_ctor_set(x_28, 0, x_335);
x_336 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_336);
lean_ctor_set(x_24, 0, x_28);
x_337 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_337);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_336);
lean_ctor_set(x_15, 0, x_16);
x_338 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_333);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_282);
lean_dec(x_34);
lean_dec(x_267);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_339 = lean_ctor_get(x_284, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_284, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_341 = x_284;
} else {
 lean_dec_ref(x_284);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_343 = lean_ctor_get(x_74, 0);
x_344 = lean_ctor_get(x_74, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_74);
lean_inc(x_52);
x_345 = l_Lean_mkArrow(x_52, x_343, x_7, x_8, x_344);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_346);
x_349 = 0;
x_350 = lean_box(0);
lean_inc(x_5);
x_351 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_349, x_350, x_5, x_6, x_7, x_8, x_347);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
x_355 = lean_box(0);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_354;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_67);
lean_ctor_set(x_356, 1, x_355);
if (lean_is_scalar(x_348)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_348;
 lean_ctor_set_tag(x_357, 1);
}
lean_ctor_set(x_357, 0, x_64);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_61);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 1, x_358);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_69);
lean_ctor_set(x_35, 0, x_49);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_46);
x_359 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_360 = l_Lean_Expr_const___override(x_359, x_34);
x_361 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_362 = lean_array_push(x_361, x_52);
lean_inc(x_55);
x_363 = lean_array_push(x_362, x_55);
lean_inc(x_58);
x_364 = lean_array_push(x_363, x_58);
lean_inc(x_19);
x_365 = lean_array_push(x_364, x_19);
lean_inc(x_40);
x_366 = lean_array_push(x_365, x_40);
lean_inc(x_352);
x_367 = lean_array_push(x_366, x_352);
x_368 = l_Lean_mkAppN(x_360, x_367);
lean_dec(x_367);
x_369 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_368);
x_370 = l_Lean_Meta_trySynthInstance(x_368, x_369, x_5, x_6, x_7, x_8, x_353);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
if (lean_obj_tag(x_371) == 1)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_368);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_ctor_get(x_371, 0);
lean_inc(x_373);
lean_dec(x_371);
x_374 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_375 = l_Lean_Expr_const___override(x_374, x_34);
x_376 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_377 = lean_array_push(x_376, x_52);
x_378 = lean_array_push(x_377, x_55);
x_379 = lean_array_push(x_378, x_58);
x_380 = lean_array_push(x_379, x_19);
x_381 = lean_array_push(x_380, x_40);
x_382 = lean_array_push(x_381, x_352);
x_383 = lean_array_push(x_382, x_373);
x_384 = lean_array_push(x_383, x_22);
x_385 = lean_array_push(x_384, x_23);
x_386 = lean_array_push(x_385, x_43);
x_387 = lean_array_push(x_386, x_1);
x_388 = lean_array_push(x_387, x_3);
x_389 = l_Lean_mkAppN(x_375, x_388);
lean_dec(x_388);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_389);
x_390 = lean_infer_type(x_389, x_5, x_6, x_7, x_8, x_372);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_391, x_5, x_6, x_7, x_8, x_392);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_396 = x_393;
} else {
 lean_dec_ref(x_393);
 x_396 = lean_box(0);
}
x_397 = l_Lean_Expr_headBeta(x_394);
x_398 = l_Lean_Elab_Term_getCalcRelation_x3f(x_397, x_5, x_6, x_7, x_8, x_395);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_389);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_401 = x_398;
} else {
 lean_dec_ref(x_398);
 x_401 = lean_box(0);
}
x_402 = l_Lean_indentExpr(x_397);
x_403 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_401)) {
 x_404 = lean_alloc_ctor(7, 2, 0);
} else {
 x_404 = x_401;
 lean_ctor_set_tag(x_404, 7);
}
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_402);
x_405 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_396)) {
 x_406 = lean_alloc_ctor(7, 2, 0);
} else {
 x_406 = x_396;
 lean_ctor_set_tag(x_406, 7);
}
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
x_407 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_406, x_5, x_6, x_7, x_8, x_400);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_410 = x_407;
} else {
 lean_dec_ref(x_407);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_399);
lean_dec(x_396);
x_412 = lean_ctor_get(x_398, 1);
lean_inc(x_412);
lean_dec(x_398);
x_413 = lean_box(0);
x_414 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_389, x_397, x_413, x_5, x_6, x_7, x_8, x_412);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_414;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_389);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_415 = lean_ctor_get(x_390, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_390, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_417 = x_390;
} else {
 lean_dec_ref(x_390);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_371);
lean_dec(x_34);
lean_dec(x_352);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_419 = lean_ctor_get(x_370, 1);
lean_inc(x_419);
lean_dec(x_370);
x_420 = l_Lean_indentExpr(x_368);
x_421 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_420);
lean_ctor_set(x_28, 0, x_421);
x_422 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_422);
lean_ctor_set(x_24, 0, x_28);
x_423 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_423);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_422);
lean_ctor_set(x_15, 0, x_16);
x_424 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_419);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_424;
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_368);
lean_dec(x_34);
lean_dec(x_352);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_425 = lean_ctor_get(x_370, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_370, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_427 = x_370;
} else {
 lean_dec_ref(x_370);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_429 = lean_ctor_get(x_69, 0);
x_430 = lean_ctor_get(x_69, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_69);
lean_inc(x_429);
x_431 = l_Lean_Expr_sort___override(x_429);
lean_inc(x_58);
x_432 = l_Lean_mkArrow(x_58, x_431, x_7, x_8, x_430);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_435 = x_432;
} else {
 lean_dec_ref(x_432);
 x_435 = lean_box(0);
}
lean_inc(x_52);
x_436 = l_Lean_mkArrow(x_52, x_433, x_7, x_8, x_434);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_439 = x_436;
} else {
 lean_dec_ref(x_436);
 x_439 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_437);
x_440 = 0;
x_441 = lean_box(0);
lean_inc(x_5);
x_442 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_440, x_441, x_5, x_6, x_7, x_8, x_438);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_445 = x_442;
} else {
 lean_dec_ref(x_442);
 x_445 = lean_box(0);
}
x_446 = lean_box(0);
if (lean_is_scalar(x_445)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_445;
 lean_ctor_set_tag(x_447, 1);
}
lean_ctor_set(x_447, 0, x_67);
lean_ctor_set(x_447, 1, x_446);
if (lean_is_scalar(x_439)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_439;
 lean_ctor_set_tag(x_448, 1);
}
lean_ctor_set(x_448, 0, x_64);
lean_ctor_set(x_448, 1, x_447);
if (lean_is_scalar(x_435)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_435;
 lean_ctor_set_tag(x_449, 1);
}
lean_ctor_set(x_449, 0, x_61);
lean_ctor_set(x_449, 1, x_448);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_429);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_450);
lean_ctor_set(x_35, 0, x_49);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_46);
x_451 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_452 = l_Lean_Expr_const___override(x_451, x_34);
x_453 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_454 = lean_array_push(x_453, x_52);
lean_inc(x_55);
x_455 = lean_array_push(x_454, x_55);
lean_inc(x_58);
x_456 = lean_array_push(x_455, x_58);
lean_inc(x_19);
x_457 = lean_array_push(x_456, x_19);
lean_inc(x_40);
x_458 = lean_array_push(x_457, x_40);
lean_inc(x_443);
x_459 = lean_array_push(x_458, x_443);
x_460 = l_Lean_mkAppN(x_452, x_459);
lean_dec(x_459);
x_461 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_460);
x_462 = l_Lean_Meta_trySynthInstance(x_460, x_461, x_5, x_6, x_7, x_8, x_444);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
if (lean_obj_tag(x_463) == 1)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_460);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_463, 0);
lean_inc(x_465);
lean_dec(x_463);
x_466 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_467 = l_Lean_Expr_const___override(x_466, x_34);
x_468 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_469 = lean_array_push(x_468, x_52);
x_470 = lean_array_push(x_469, x_55);
x_471 = lean_array_push(x_470, x_58);
x_472 = lean_array_push(x_471, x_19);
x_473 = lean_array_push(x_472, x_40);
x_474 = lean_array_push(x_473, x_443);
x_475 = lean_array_push(x_474, x_465);
x_476 = lean_array_push(x_475, x_22);
x_477 = lean_array_push(x_476, x_23);
x_478 = lean_array_push(x_477, x_43);
x_479 = lean_array_push(x_478, x_1);
x_480 = lean_array_push(x_479, x_3);
x_481 = l_Lean_mkAppN(x_467, x_480);
lean_dec(x_480);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_481);
x_482 = lean_infer_type(x_481, x_5, x_6, x_7, x_8, x_464);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_483, x_5, x_6, x_7, x_8, x_484);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_488 = x_485;
} else {
 lean_dec_ref(x_485);
 x_488 = lean_box(0);
}
x_489 = l_Lean_Expr_headBeta(x_486);
x_490 = l_Lean_Elab_Term_getCalcRelation_x3f(x_489, x_5, x_6, x_7, x_8, x_487);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_481);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_493 = x_490;
} else {
 lean_dec_ref(x_490);
 x_493 = lean_box(0);
}
x_494 = l_Lean_indentExpr(x_489);
x_495 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_493)) {
 x_496 = lean_alloc_ctor(7, 2, 0);
} else {
 x_496 = x_493;
 lean_ctor_set_tag(x_496, 7);
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_494);
x_497 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_488)) {
 x_498 = lean_alloc_ctor(7, 2, 0);
} else {
 x_498 = x_488;
 lean_ctor_set_tag(x_498, 7);
}
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
x_499 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_498, x_5, x_6, x_7, x_8, x_492);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_502 = x_499;
} else {
 lean_dec_ref(x_499);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_491);
lean_dec(x_488);
x_504 = lean_ctor_get(x_490, 1);
lean_inc(x_504);
lean_dec(x_490);
x_505 = lean_box(0);
x_506 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_481, x_489, x_505, x_5, x_6, x_7, x_8, x_504);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_506;
}
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_481);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_507 = lean_ctor_get(x_482, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_482, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_509 = x_482;
} else {
 lean_dec_ref(x_482);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_463);
lean_dec(x_34);
lean_dec(x_443);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_511 = lean_ctor_get(x_462, 1);
lean_inc(x_511);
lean_dec(x_462);
x_512 = l_Lean_indentExpr(x_460);
x_513 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_512);
lean_ctor_set(x_28, 0, x_513);
x_514 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_514);
lean_ctor_set(x_24, 0, x_28);
x_515 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_515);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_514);
lean_ctor_set(x_15, 0, x_16);
x_516 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_511);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_516;
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_460);
lean_dec(x_34);
lean_dec(x_443);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_517 = lean_ctor_get(x_462, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_462, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_519 = x_462;
} else {
 lean_dec_ref(x_462);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_518);
return x_520;
}
}
}
else
{
uint8_t x_521; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_46);
lean_free_object(x_35);
lean_dec(x_43);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_521 = !lean_is_exclusive(x_66);
if (x_521 == 0)
{
return x_66;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_66, 0);
x_523 = lean_ctor_get(x_66, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_66);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
}
else
{
uint8_t x_525; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_46);
lean_free_object(x_35);
lean_dec(x_43);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_525 = !lean_is_exclusive(x_63);
if (x_525 == 0)
{
return x_63;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_63, 0);
x_527 = lean_ctor_get(x_63, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_63);
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
return x_528;
}
}
}
else
{
uint8_t x_529; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_46);
lean_free_object(x_35);
lean_dec(x_43);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_529 = !lean_is_exclusive(x_60);
if (x_529 == 0)
{
return x_60;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_60, 0);
x_531 = lean_ctor_get(x_60, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_60);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
}
else
{
uint8_t x_533; 
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_46);
lean_free_object(x_35);
lean_dec(x_43);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_533 = !lean_is_exclusive(x_57);
if (x_533 == 0)
{
return x_57;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_57, 0);
x_535 = lean_ctor_get(x_57, 1);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_57);
x_536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
return x_536;
}
}
}
else
{
uint8_t x_537; 
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_46);
lean_free_object(x_35);
lean_dec(x_43);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_537 = !lean_is_exclusive(x_54);
if (x_537 == 0)
{
return x_54;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_54, 0);
x_539 = lean_ctor_get(x_54, 1);
lean_inc(x_539);
lean_inc(x_538);
lean_dec(x_54);
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
return x_540;
}
}
}
else
{
uint8_t x_541; 
lean_dec(x_49);
lean_dec(x_46);
lean_free_object(x_35);
lean_dec(x_43);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_541 = !lean_is_exclusive(x_51);
if (x_541 == 0)
{
return x_51;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_51, 0);
x_543 = lean_ctor_get(x_51, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_51);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_46);
lean_free_object(x_35);
lean_dec(x_43);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_545 = !lean_is_exclusive(x_48);
if (x_545 == 0)
{
return x_48;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_48, 0);
x_547 = lean_ctor_get(x_48, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_48);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
else
{
uint8_t x_549; 
lean_free_object(x_35);
lean_dec(x_43);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_549 = !lean_is_exclusive(x_45);
if (x_549 == 0)
{
return x_45;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_45, 0);
x_551 = lean_ctor_get(x_45, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_45);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_ctor_get(x_35, 1);
lean_inc(x_553);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_554 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_40);
x_557 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_40, x_5, x_6, x_7, x_8, x_556);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_560 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_559);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_563 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_562);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_563, 1);
lean_inc(x_565);
lean_dec(x_563);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_553);
x_566 = lean_infer_type(x_553, x_5, x_6, x_7, x_8, x_565);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_561);
x_569 = l_Lean_Meta_getLevel(x_561, x_5, x_6, x_7, x_8, x_568);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_564);
x_572 = l_Lean_Meta_getLevel(x_564, x_5, x_6, x_7, x_8, x_571);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_567);
x_575 = l_Lean_Meta_getLevel(x_567, x_5, x_6, x_7, x_8, x_574);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
lean_dec(x_575);
x_578 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_577);
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_581 = x_578;
} else {
 lean_dec_ref(x_578);
 x_581 = lean_box(0);
}
lean_inc(x_579);
x_582 = l_Lean_Expr_sort___override(x_579);
lean_inc(x_567);
x_583 = l_Lean_mkArrow(x_567, x_582, x_7, x_8, x_580);
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_586 = x_583;
} else {
 lean_dec_ref(x_583);
 x_586 = lean_box(0);
}
lean_inc(x_561);
x_587 = l_Lean_mkArrow(x_561, x_584, x_7, x_8, x_585);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_590 = x_587;
} else {
 lean_dec_ref(x_587);
 x_590 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_588);
x_591 = 0;
x_592 = lean_box(0);
lean_inc(x_5);
x_593 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_591, x_592, x_5, x_6, x_7, x_8, x_589);
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_596 = x_593;
} else {
 lean_dec_ref(x_593);
 x_596 = lean_box(0);
}
x_597 = lean_box(0);
if (lean_is_scalar(x_596)) {
 x_598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_598 = x_596;
 lean_ctor_set_tag(x_598, 1);
}
lean_ctor_set(x_598, 0, x_576);
lean_ctor_set(x_598, 1, x_597);
if (lean_is_scalar(x_590)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_590;
 lean_ctor_set_tag(x_599, 1);
}
lean_ctor_set(x_599, 0, x_573);
lean_ctor_set(x_599, 1, x_598);
if (lean_is_scalar(x_586)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_586;
 lean_ctor_set_tag(x_600, 1);
}
lean_ctor_set(x_600, 0, x_570);
lean_ctor_set(x_600, 1, x_599);
if (lean_is_scalar(x_581)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_581;
 lean_ctor_set_tag(x_601, 1);
}
lean_ctor_set(x_601, 0, x_579);
lean_ctor_set(x_601, 1, x_600);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_558);
lean_ctor_set(x_602, 1, x_601);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_602);
lean_ctor_set(x_34, 0, x_555);
x_603 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_604 = l_Lean_Expr_const___override(x_603, x_34);
x_605 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_561);
x_606 = lean_array_push(x_605, x_561);
lean_inc(x_564);
x_607 = lean_array_push(x_606, x_564);
lean_inc(x_567);
x_608 = lean_array_push(x_607, x_567);
lean_inc(x_19);
x_609 = lean_array_push(x_608, x_19);
lean_inc(x_40);
x_610 = lean_array_push(x_609, x_40);
lean_inc(x_594);
x_611 = lean_array_push(x_610, x_594);
x_612 = l_Lean_mkAppN(x_604, x_611);
lean_dec(x_611);
x_613 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_612);
x_614 = l_Lean_Meta_trySynthInstance(x_612, x_613, x_5, x_6, x_7, x_8, x_595);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
if (lean_obj_tag(x_615) == 1)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_612);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_ctor_get(x_615, 0);
lean_inc(x_617);
lean_dec(x_615);
x_618 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_619 = l_Lean_Expr_const___override(x_618, x_34);
x_620 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_621 = lean_array_push(x_620, x_561);
x_622 = lean_array_push(x_621, x_564);
x_623 = lean_array_push(x_622, x_567);
x_624 = lean_array_push(x_623, x_19);
x_625 = lean_array_push(x_624, x_40);
x_626 = lean_array_push(x_625, x_594);
x_627 = lean_array_push(x_626, x_617);
x_628 = lean_array_push(x_627, x_22);
x_629 = lean_array_push(x_628, x_23);
x_630 = lean_array_push(x_629, x_553);
x_631 = lean_array_push(x_630, x_1);
x_632 = lean_array_push(x_631, x_3);
x_633 = l_Lean_mkAppN(x_619, x_632);
lean_dec(x_632);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_633);
x_634 = lean_infer_type(x_633, x_5, x_6, x_7, x_8, x_616);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
x_637 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_635, x_5, x_6, x_7, x_8, x_636);
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_640 = x_637;
} else {
 lean_dec_ref(x_637);
 x_640 = lean_box(0);
}
x_641 = l_Lean_Expr_headBeta(x_638);
x_642 = l_Lean_Elab_Term_getCalcRelation_x3f(x_641, x_5, x_6, x_7, x_8, x_639);
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_633);
x_644 = lean_ctor_get(x_642, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_645 = x_642;
} else {
 lean_dec_ref(x_642);
 x_645 = lean_box(0);
}
x_646 = l_Lean_indentExpr(x_641);
x_647 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_645)) {
 x_648 = lean_alloc_ctor(7, 2, 0);
} else {
 x_648 = x_645;
 lean_ctor_set_tag(x_648, 7);
}
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_646);
x_649 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_640)) {
 x_650 = lean_alloc_ctor(7, 2, 0);
} else {
 x_650 = x_640;
 lean_ctor_set_tag(x_650, 7);
}
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
x_651 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_650, x_5, x_6, x_7, x_8, x_644);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 lean_ctor_release(x_651, 1);
 x_654 = x_651;
} else {
 lean_dec_ref(x_651);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 2, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_653);
return x_655;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_643);
lean_dec(x_640);
x_656 = lean_ctor_get(x_642, 1);
lean_inc(x_656);
lean_dec(x_642);
x_657 = lean_box(0);
x_658 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_633, x_641, x_657, x_5, x_6, x_7, x_8, x_656);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_633);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_659 = lean_ctor_get(x_634, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_634, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_661 = x_634;
} else {
 lean_dec_ref(x_634);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(1, 2, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_659);
lean_ctor_set(x_662, 1, x_660);
return x_662;
}
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_615);
lean_dec(x_34);
lean_dec(x_594);
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_561);
lean_dec(x_553);
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_663 = lean_ctor_get(x_614, 1);
lean_inc(x_663);
lean_dec(x_614);
x_664 = l_Lean_indentExpr(x_612);
x_665 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_664);
lean_ctor_set(x_28, 0, x_665);
x_666 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_666);
lean_ctor_set(x_24, 0, x_28);
x_667 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_667);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_666);
lean_ctor_set(x_15, 0, x_16);
x_668 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_663);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_668;
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_612);
lean_dec(x_34);
lean_dec(x_594);
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_561);
lean_dec(x_553);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_669 = lean_ctor_get(x_614, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_614, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_671 = x_614;
} else {
 lean_dec_ref(x_614);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_669);
lean_ctor_set(x_672, 1, x_670);
return x_672;
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_573);
lean_dec(x_570);
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_555);
lean_dec(x_553);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_673 = lean_ctor_get(x_575, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_575, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_675 = x_575;
} else {
 lean_dec_ref(x_575);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_570);
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_555);
lean_dec(x_553);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_677 = lean_ctor_get(x_572, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_572, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_679 = x_572;
} else {
 lean_dec_ref(x_572);
 x_679 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_680 = x_679;
}
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_678);
return x_680;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_555);
lean_dec(x_553);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_681 = lean_ctor_get(x_569, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_569, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_683 = x_569;
} else {
 lean_dec_ref(x_569);
 x_683 = lean_box(0);
}
if (lean_is_scalar(x_683)) {
 x_684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_684 = x_683;
}
lean_ctor_set(x_684, 0, x_681);
lean_ctor_set(x_684, 1, x_682);
return x_684;
}
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_564);
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_555);
lean_dec(x_553);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_685 = lean_ctor_get(x_566, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_566, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_687 = x_566;
} else {
 lean_dec_ref(x_566);
 x_687 = lean_box(0);
}
if (lean_is_scalar(x_687)) {
 x_688 = lean_alloc_ctor(1, 2, 0);
} else {
 x_688 = x_687;
}
lean_ctor_set(x_688, 0, x_685);
lean_ctor_set(x_688, 1, x_686);
return x_688;
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_555);
lean_dec(x_553);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_689 = lean_ctor_get(x_563, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_563, 1);
lean_inc(x_690);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_691 = x_563;
} else {
 lean_dec_ref(x_563);
 x_691 = lean_box(0);
}
if (lean_is_scalar(x_691)) {
 x_692 = lean_alloc_ctor(1, 2, 0);
} else {
 x_692 = x_691;
}
lean_ctor_set(x_692, 0, x_689);
lean_ctor_set(x_692, 1, x_690);
return x_692;
}
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_558);
lean_dec(x_555);
lean_dec(x_553);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_693 = lean_ctor_get(x_560, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_560, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_695 = x_560;
} else {
 lean_dec_ref(x_560);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 2, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_693);
lean_ctor_set(x_696, 1, x_694);
return x_696;
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_555);
lean_dec(x_553);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_697 = lean_ctor_get(x_557, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_557, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_699 = x_557;
} else {
 lean_dec_ref(x_557);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(1, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_697);
lean_ctor_set(x_700, 1, x_698);
return x_700;
}
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_553);
lean_free_object(x_34);
lean_dec(x_40);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_701 = lean_ctor_get(x_554, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_554, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_703 = x_554;
} else {
 lean_dec_ref(x_554);
 x_703 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_703;
}
lean_ctor_set(x_704, 0, x_701);
lean_ctor_set(x_704, 1, x_702);
return x_704;
}
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_705 = lean_ctor_get(x_34, 0);
lean_inc(x_705);
lean_dec(x_34);
x_706 = lean_ctor_get(x_35, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_707 = x_35;
} else {
 lean_dec_ref(x_35);
 x_707 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_708 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_708, 1);
lean_inc(x_710);
lean_dec(x_708);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_705);
x_711 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_705, x_5, x_6, x_7, x_8, x_710);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_714 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_713);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
lean_dec(x_714);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_717 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_716);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_706);
x_720 = lean_infer_type(x_706, x_5, x_6, x_7, x_8, x_719);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_715);
x_723 = l_Lean_Meta_getLevel(x_715, x_5, x_6, x_7, x_8, x_722);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_718);
x_726 = l_Lean_Meta_getLevel(x_718, x_5, x_6, x_7, x_8, x_725);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
lean_dec(x_726);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_721);
x_729 = l_Lean_Meta_getLevel(x_721, x_5, x_6, x_7, x_8, x_728);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; uint8_t x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
x_732 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_731);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_732)) {
 lean_ctor_release(x_732, 0);
 lean_ctor_release(x_732, 1);
 x_735 = x_732;
} else {
 lean_dec_ref(x_732);
 x_735 = lean_box(0);
}
lean_inc(x_733);
x_736 = l_Lean_Expr_sort___override(x_733);
lean_inc(x_721);
x_737 = l_Lean_mkArrow(x_721, x_736, x_7, x_8, x_734);
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_737, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_740 = x_737;
} else {
 lean_dec_ref(x_737);
 x_740 = lean_box(0);
}
lean_inc(x_715);
x_741 = l_Lean_mkArrow(x_715, x_738, x_7, x_8, x_739);
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 lean_ctor_release(x_741, 1);
 x_744 = x_741;
} else {
 lean_dec_ref(x_741);
 x_744 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_742);
x_745 = 0;
x_746 = lean_box(0);
lean_inc(x_5);
x_747 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_745, x_746, x_5, x_6, x_7, x_8, x_743);
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_750 = x_747;
} else {
 lean_dec_ref(x_747);
 x_750 = lean_box(0);
}
x_751 = lean_box(0);
if (lean_is_scalar(x_750)) {
 x_752 = lean_alloc_ctor(1, 2, 0);
} else {
 x_752 = x_750;
 lean_ctor_set_tag(x_752, 1);
}
lean_ctor_set(x_752, 0, x_730);
lean_ctor_set(x_752, 1, x_751);
if (lean_is_scalar(x_744)) {
 x_753 = lean_alloc_ctor(1, 2, 0);
} else {
 x_753 = x_744;
 lean_ctor_set_tag(x_753, 1);
}
lean_ctor_set(x_753, 0, x_727);
lean_ctor_set(x_753, 1, x_752);
if (lean_is_scalar(x_740)) {
 x_754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_754 = x_740;
 lean_ctor_set_tag(x_754, 1);
}
lean_ctor_set(x_754, 0, x_724);
lean_ctor_set(x_754, 1, x_753);
if (lean_is_scalar(x_735)) {
 x_755 = lean_alloc_ctor(1, 2, 0);
} else {
 x_755 = x_735;
 lean_ctor_set_tag(x_755, 1);
}
lean_ctor_set(x_755, 0, x_733);
lean_ctor_set(x_755, 1, x_754);
if (lean_is_scalar(x_707)) {
 x_756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_756 = x_707;
 lean_ctor_set_tag(x_756, 1);
}
lean_ctor_set(x_756, 0, x_712);
lean_ctor_set(x_756, 1, x_755);
x_757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_757, 0, x_709);
lean_ctor_set(x_757, 1, x_756);
x_758 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_757);
x_759 = l_Lean_Expr_const___override(x_758, x_757);
x_760 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_715);
x_761 = lean_array_push(x_760, x_715);
lean_inc(x_718);
x_762 = lean_array_push(x_761, x_718);
lean_inc(x_721);
x_763 = lean_array_push(x_762, x_721);
lean_inc(x_19);
x_764 = lean_array_push(x_763, x_19);
lean_inc(x_705);
x_765 = lean_array_push(x_764, x_705);
lean_inc(x_748);
x_766 = lean_array_push(x_765, x_748);
x_767 = l_Lean_mkAppN(x_759, x_766);
lean_dec(x_766);
x_768 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_767);
x_769 = l_Lean_Meta_trySynthInstance(x_767, x_768, x_5, x_6, x_7, x_8, x_749);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; 
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
if (lean_obj_tag(x_770) == 1)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
lean_dec(x_767);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_771 = lean_ctor_get(x_769, 1);
lean_inc(x_771);
lean_dec(x_769);
x_772 = lean_ctor_get(x_770, 0);
lean_inc(x_772);
lean_dec(x_770);
x_773 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_774 = l_Lean_Expr_const___override(x_773, x_757);
x_775 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_776 = lean_array_push(x_775, x_715);
x_777 = lean_array_push(x_776, x_718);
x_778 = lean_array_push(x_777, x_721);
x_779 = lean_array_push(x_778, x_19);
x_780 = lean_array_push(x_779, x_705);
x_781 = lean_array_push(x_780, x_748);
x_782 = lean_array_push(x_781, x_772);
x_783 = lean_array_push(x_782, x_22);
x_784 = lean_array_push(x_783, x_23);
x_785 = lean_array_push(x_784, x_706);
x_786 = lean_array_push(x_785, x_1);
x_787 = lean_array_push(x_786, x_3);
x_788 = l_Lean_mkAppN(x_774, x_787);
lean_dec(x_787);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_788);
x_789 = lean_infer_type(x_788, x_5, x_6, x_7, x_8, x_771);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_792 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_790, x_5, x_6, x_7, x_8, x_791);
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_795 = x_792;
} else {
 lean_dec_ref(x_792);
 x_795 = lean_box(0);
}
x_796 = l_Lean_Expr_headBeta(x_793);
x_797 = l_Lean_Elab_Term_getCalcRelation_x3f(x_796, x_5, x_6, x_7, x_8, x_794);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_788);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_800 = x_797;
} else {
 lean_dec_ref(x_797);
 x_800 = lean_box(0);
}
x_801 = l_Lean_indentExpr(x_796);
x_802 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_800)) {
 x_803 = lean_alloc_ctor(7, 2, 0);
} else {
 x_803 = x_800;
 lean_ctor_set_tag(x_803, 7);
}
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_801);
x_804 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_795)) {
 x_805 = lean_alloc_ctor(7, 2, 0);
} else {
 x_805 = x_795;
 lean_ctor_set_tag(x_805, 7);
}
lean_ctor_set(x_805, 0, x_803);
lean_ctor_set(x_805, 1, x_804);
x_806 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_805, x_5, x_6, x_7, x_8, x_799);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_809 = x_806;
} else {
 lean_dec_ref(x_806);
 x_809 = lean_box(0);
}
if (lean_is_scalar(x_809)) {
 x_810 = lean_alloc_ctor(1, 2, 0);
} else {
 x_810 = x_809;
}
lean_ctor_set(x_810, 0, x_807);
lean_ctor_set(x_810, 1, x_808);
return x_810;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_798);
lean_dec(x_795);
x_811 = lean_ctor_get(x_797, 1);
lean_inc(x_811);
lean_dec(x_797);
x_812 = lean_box(0);
x_813 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_788, x_796, x_812, x_5, x_6, x_7, x_8, x_811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_813;
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_788);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_814 = lean_ctor_get(x_789, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_789, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_816 = x_789;
} else {
 lean_dec_ref(x_789);
 x_816 = lean_box(0);
}
if (lean_is_scalar(x_816)) {
 x_817 = lean_alloc_ctor(1, 2, 0);
} else {
 x_817 = x_816;
}
lean_ctor_set(x_817, 0, x_814);
lean_ctor_set(x_817, 1, x_815);
return x_817;
}
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_770);
lean_dec(x_757);
lean_dec(x_748);
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_706);
lean_dec(x_705);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_818 = lean_ctor_get(x_769, 1);
lean_inc(x_818);
lean_dec(x_769);
x_819 = l_Lean_indentExpr(x_767);
x_820 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_819);
lean_ctor_set(x_28, 0, x_820);
x_821 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_821);
lean_ctor_set(x_24, 0, x_28);
x_822 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_822);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_821);
lean_ctor_set(x_15, 0, x_16);
x_823 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_818);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_823;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_dec(x_767);
lean_dec(x_757);
lean_dec(x_748);
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_824 = lean_ctor_get(x_769, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_769, 1);
lean_inc(x_825);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_826 = x_769;
} else {
 lean_dec_ref(x_769);
 x_826 = lean_box(0);
}
if (lean_is_scalar(x_826)) {
 x_827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_827 = x_826;
}
lean_ctor_set(x_827, 0, x_824);
lean_ctor_set(x_827, 1, x_825);
return x_827;
}
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_727);
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_712);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_828 = lean_ctor_get(x_729, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_729, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_830 = x_729;
} else {
 lean_dec_ref(x_729);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(1, 2, 0);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_828);
lean_ctor_set(x_831, 1, x_829);
return x_831;
}
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_712);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_832 = lean_ctor_get(x_726, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_726, 1);
lean_inc(x_833);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_834 = x_726;
} else {
 lean_dec_ref(x_726);
 x_834 = lean_box(0);
}
if (lean_is_scalar(x_834)) {
 x_835 = lean_alloc_ctor(1, 2, 0);
} else {
 x_835 = x_834;
}
lean_ctor_set(x_835, 0, x_832);
lean_ctor_set(x_835, 1, x_833);
return x_835;
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_712);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_836 = lean_ctor_get(x_723, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_723, 1);
lean_inc(x_837);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_838 = x_723;
} else {
 lean_dec_ref(x_723);
 x_838 = lean_box(0);
}
if (lean_is_scalar(x_838)) {
 x_839 = lean_alloc_ctor(1, 2, 0);
} else {
 x_839 = x_838;
}
lean_ctor_set(x_839, 0, x_836);
lean_ctor_set(x_839, 1, x_837);
return x_839;
}
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_712);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_840 = lean_ctor_get(x_720, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_720, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_842 = x_720;
} else {
 lean_dec_ref(x_720);
 x_842 = lean_box(0);
}
if (lean_is_scalar(x_842)) {
 x_843 = lean_alloc_ctor(1, 2, 0);
} else {
 x_843 = x_842;
}
lean_ctor_set(x_843, 0, x_840);
lean_ctor_set(x_843, 1, x_841);
return x_843;
}
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_715);
lean_dec(x_712);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_844 = lean_ctor_get(x_717, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_717, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_846 = x_717;
} else {
 lean_dec_ref(x_717);
 x_846 = lean_box(0);
}
if (lean_is_scalar(x_846)) {
 x_847 = lean_alloc_ctor(1, 2, 0);
} else {
 x_847 = x_846;
}
lean_ctor_set(x_847, 0, x_844);
lean_ctor_set(x_847, 1, x_845);
return x_847;
}
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_712);
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_848 = lean_ctor_get(x_714, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_714, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_850 = x_714;
} else {
 lean_dec_ref(x_714);
 x_850 = lean_box(0);
}
if (lean_is_scalar(x_850)) {
 x_851 = lean_alloc_ctor(1, 2, 0);
} else {
 x_851 = x_850;
}
lean_ctor_set(x_851, 0, x_848);
lean_ctor_set(x_851, 1, x_849);
return x_851;
}
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_709);
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_852 = lean_ctor_get(x_711, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_711, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_854 = x_711;
} else {
 lean_dec_ref(x_711);
 x_854 = lean_box(0);
}
if (lean_is_scalar(x_854)) {
 x_855 = lean_alloc_ctor(1, 2, 0);
} else {
 x_855 = x_854;
}
lean_ctor_set(x_855, 0, x_852);
lean_ctor_set(x_855, 1, x_853);
return x_855;
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_free_object(x_28);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_856 = lean_ctor_get(x_708, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_708, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 lean_ctor_release(x_708, 1);
 x_858 = x_708;
} else {
 lean_dec_ref(x_708);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(1, 2, 0);
} else {
 x_859 = x_858;
}
lean_ctor_set(x_859, 0, x_856);
lean_ctor_set(x_859, 1, x_857);
return x_859;
}
}
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_860 = lean_ctor_get(x_28, 1);
lean_inc(x_860);
lean_dec(x_28);
x_861 = lean_ctor_get(x_34, 0);
lean_inc(x_861);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_862 = x_34;
} else {
 lean_dec_ref(x_34);
 x_862 = lean_box(0);
}
x_863 = lean_ctor_get(x_35, 1);
lean_inc(x_863);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_864 = x_35;
} else {
 lean_dec_ref(x_35);
 x_864 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_865 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_860);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_861);
x_868 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_861, x_5, x_6, x_7, x_8, x_867);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_871 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_870);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_871, 1);
lean_inc(x_873);
lean_dec(x_871);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_874 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_873);
if (lean_obj_tag(x_874) == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_875 = lean_ctor_get(x_874, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
lean_dec(x_874);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_863);
x_877 = lean_infer_type(x_863, x_5, x_6, x_7, x_8, x_876);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_872);
x_880 = l_Lean_Meta_getLevel(x_872, x_5, x_6, x_7, x_8, x_879);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec(x_880);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_875);
x_883 = l_Lean_Meta_getLevel(x_875, x_5, x_6, x_7, x_8, x_882);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_883, 1);
lean_inc(x_885);
lean_dec(x_883);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_878);
x_886 = l_Lean_Meta_getLevel(x_878, x_5, x_6, x_7, x_8, x_885);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; uint8_t x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
lean_dec(x_886);
x_889 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_888);
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_892 = x_889;
} else {
 lean_dec_ref(x_889);
 x_892 = lean_box(0);
}
lean_inc(x_890);
x_893 = l_Lean_Expr_sort___override(x_890);
lean_inc(x_878);
x_894 = l_Lean_mkArrow(x_878, x_893, x_7, x_8, x_891);
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_897 = x_894;
} else {
 lean_dec_ref(x_894);
 x_897 = lean_box(0);
}
lean_inc(x_872);
x_898 = l_Lean_mkArrow(x_872, x_895, x_7, x_8, x_896);
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_901 = x_898;
} else {
 lean_dec_ref(x_898);
 x_901 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_899);
x_902 = 0;
x_903 = lean_box(0);
lean_inc(x_5);
x_904 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_902, x_903, x_5, x_6, x_7, x_8, x_900);
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_907 = x_904;
} else {
 lean_dec_ref(x_904);
 x_907 = lean_box(0);
}
x_908 = lean_box(0);
if (lean_is_scalar(x_907)) {
 x_909 = lean_alloc_ctor(1, 2, 0);
} else {
 x_909 = x_907;
 lean_ctor_set_tag(x_909, 1);
}
lean_ctor_set(x_909, 0, x_887);
lean_ctor_set(x_909, 1, x_908);
if (lean_is_scalar(x_901)) {
 x_910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_910 = x_901;
 lean_ctor_set_tag(x_910, 1);
}
lean_ctor_set(x_910, 0, x_884);
lean_ctor_set(x_910, 1, x_909);
if (lean_is_scalar(x_897)) {
 x_911 = lean_alloc_ctor(1, 2, 0);
} else {
 x_911 = x_897;
 lean_ctor_set_tag(x_911, 1);
}
lean_ctor_set(x_911, 0, x_881);
lean_ctor_set(x_911, 1, x_910);
if (lean_is_scalar(x_892)) {
 x_912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_912 = x_892;
 lean_ctor_set_tag(x_912, 1);
}
lean_ctor_set(x_912, 0, x_890);
lean_ctor_set(x_912, 1, x_911);
if (lean_is_scalar(x_864)) {
 x_913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_913 = x_864;
 lean_ctor_set_tag(x_913, 1);
}
lean_ctor_set(x_913, 0, x_869);
lean_ctor_set(x_913, 1, x_912);
if (lean_is_scalar(x_862)) {
 x_914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_914 = x_862;
 lean_ctor_set_tag(x_914, 1);
}
lean_ctor_set(x_914, 0, x_866);
lean_ctor_set(x_914, 1, x_913);
x_915 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_914);
x_916 = l_Lean_Expr_const___override(x_915, x_914);
x_917 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_872);
x_918 = lean_array_push(x_917, x_872);
lean_inc(x_875);
x_919 = lean_array_push(x_918, x_875);
lean_inc(x_878);
x_920 = lean_array_push(x_919, x_878);
lean_inc(x_19);
x_921 = lean_array_push(x_920, x_19);
lean_inc(x_861);
x_922 = lean_array_push(x_921, x_861);
lean_inc(x_905);
x_923 = lean_array_push(x_922, x_905);
x_924 = l_Lean_mkAppN(x_916, x_923);
lean_dec(x_923);
x_925 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_924);
x_926 = l_Lean_Meta_trySynthInstance(x_924, x_925, x_5, x_6, x_7, x_8, x_906);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; 
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
if (lean_obj_tag(x_927) == 1)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
lean_dec(x_924);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_928 = lean_ctor_get(x_926, 1);
lean_inc(x_928);
lean_dec(x_926);
x_929 = lean_ctor_get(x_927, 0);
lean_inc(x_929);
lean_dec(x_927);
x_930 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_931 = l_Lean_Expr_const___override(x_930, x_914);
x_932 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_933 = lean_array_push(x_932, x_872);
x_934 = lean_array_push(x_933, x_875);
x_935 = lean_array_push(x_934, x_878);
x_936 = lean_array_push(x_935, x_19);
x_937 = lean_array_push(x_936, x_861);
x_938 = lean_array_push(x_937, x_905);
x_939 = lean_array_push(x_938, x_929);
x_940 = lean_array_push(x_939, x_22);
x_941 = lean_array_push(x_940, x_23);
x_942 = lean_array_push(x_941, x_863);
x_943 = lean_array_push(x_942, x_1);
x_944 = lean_array_push(x_943, x_3);
x_945 = l_Lean_mkAppN(x_931, x_944);
lean_dec(x_944);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_945);
x_946 = lean_infer_type(x_945, x_5, x_6, x_7, x_8, x_928);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_946, 1);
lean_inc(x_948);
lean_dec(x_946);
x_949 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_947, x_5, x_6, x_7, x_8, x_948);
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_949, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 lean_ctor_release(x_949, 1);
 x_952 = x_949;
} else {
 lean_dec_ref(x_949);
 x_952 = lean_box(0);
}
x_953 = l_Lean_Expr_headBeta(x_950);
x_954 = l_Lean_Elab_Term_getCalcRelation_x3f(x_953, x_5, x_6, x_7, x_8, x_951);
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
if (lean_obj_tag(x_955) == 0)
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
lean_dec(x_945);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_957 = x_954;
} else {
 lean_dec_ref(x_954);
 x_957 = lean_box(0);
}
x_958 = l_Lean_indentExpr(x_953);
x_959 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_957)) {
 x_960 = lean_alloc_ctor(7, 2, 0);
} else {
 x_960 = x_957;
 lean_ctor_set_tag(x_960, 7);
}
lean_ctor_set(x_960, 0, x_959);
lean_ctor_set(x_960, 1, x_958);
x_961 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_952)) {
 x_962 = lean_alloc_ctor(7, 2, 0);
} else {
 x_962 = x_952;
 lean_ctor_set_tag(x_962, 7);
}
lean_ctor_set(x_962, 0, x_960);
lean_ctor_set(x_962, 1, x_961);
x_963 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_962, x_5, x_6, x_7, x_8, x_956);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_966 = x_963;
} else {
 lean_dec_ref(x_963);
 x_966 = lean_box(0);
}
if (lean_is_scalar(x_966)) {
 x_967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_967 = x_966;
}
lean_ctor_set(x_967, 0, x_964);
lean_ctor_set(x_967, 1, x_965);
return x_967;
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_955);
lean_dec(x_952);
x_968 = lean_ctor_get(x_954, 1);
lean_inc(x_968);
lean_dec(x_954);
x_969 = lean_box(0);
x_970 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_945, x_953, x_969, x_5, x_6, x_7, x_8, x_968);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_970;
}
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_dec(x_945);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_971 = lean_ctor_get(x_946, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_946, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_946)) {
 lean_ctor_release(x_946, 0);
 lean_ctor_release(x_946, 1);
 x_973 = x_946;
} else {
 lean_dec_ref(x_946);
 x_973 = lean_box(0);
}
if (lean_is_scalar(x_973)) {
 x_974 = lean_alloc_ctor(1, 2, 0);
} else {
 x_974 = x_973;
}
lean_ctor_set(x_974, 0, x_971);
lean_ctor_set(x_974, 1, x_972);
return x_974;
}
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
lean_dec(x_927);
lean_dec(x_914);
lean_dec(x_905);
lean_dec(x_878);
lean_dec(x_875);
lean_dec(x_872);
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_975 = lean_ctor_get(x_926, 1);
lean_inc(x_975);
lean_dec(x_926);
x_976 = l_Lean_indentExpr(x_924);
x_977 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
x_978 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_978, 0, x_977);
lean_ctor_set(x_978, 1, x_976);
x_979 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_979);
lean_ctor_set(x_24, 0, x_978);
x_980 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_980);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_979);
lean_ctor_set(x_15, 0, x_16);
x_981 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_975);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_981;
}
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
lean_dec(x_924);
lean_dec(x_914);
lean_dec(x_905);
lean_dec(x_878);
lean_dec(x_875);
lean_dec(x_872);
lean_dec(x_863);
lean_dec(x_861);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_982 = lean_ctor_get(x_926, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_926, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_984 = x_926;
} else {
 lean_dec_ref(x_926);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_982);
lean_ctor_set(x_985, 1, x_983);
return x_985;
}
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_884);
lean_dec(x_881);
lean_dec(x_878);
lean_dec(x_875);
lean_dec(x_872);
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_986 = lean_ctor_get(x_886, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_886, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_988 = x_886;
} else {
 lean_dec_ref(x_886);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_986);
lean_ctor_set(x_989, 1, x_987);
return x_989;
}
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_881);
lean_dec(x_878);
lean_dec(x_875);
lean_dec(x_872);
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_990 = lean_ctor_get(x_883, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_883, 1);
lean_inc(x_991);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 lean_ctor_release(x_883, 1);
 x_992 = x_883;
} else {
 lean_dec_ref(x_883);
 x_992 = lean_box(0);
}
if (lean_is_scalar(x_992)) {
 x_993 = lean_alloc_ctor(1, 2, 0);
} else {
 x_993 = x_992;
}
lean_ctor_set(x_993, 0, x_990);
lean_ctor_set(x_993, 1, x_991);
return x_993;
}
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
lean_dec(x_878);
lean_dec(x_875);
lean_dec(x_872);
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_994 = lean_ctor_get(x_880, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_880, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_996 = x_880;
} else {
 lean_dec_ref(x_880);
 x_996 = lean_box(0);
}
if (lean_is_scalar(x_996)) {
 x_997 = lean_alloc_ctor(1, 2, 0);
} else {
 x_997 = x_996;
}
lean_ctor_set(x_997, 0, x_994);
lean_ctor_set(x_997, 1, x_995);
return x_997;
}
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_875);
lean_dec(x_872);
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_998 = lean_ctor_get(x_877, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_877, 1);
lean_inc(x_999);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 lean_ctor_release(x_877, 1);
 x_1000 = x_877;
} else {
 lean_dec_ref(x_877);
 x_1000 = lean_box(0);
}
if (lean_is_scalar(x_1000)) {
 x_1001 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1001 = x_1000;
}
lean_ctor_set(x_1001, 0, x_998);
lean_ctor_set(x_1001, 1, x_999);
return x_1001;
}
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
lean_dec(x_872);
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1002 = lean_ctor_get(x_874, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_874, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 lean_ctor_release(x_874, 1);
 x_1004 = x_874;
} else {
 lean_dec_ref(x_874);
 x_1004 = lean_box(0);
}
if (lean_is_scalar(x_1004)) {
 x_1005 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1005 = x_1004;
}
lean_ctor_set(x_1005, 0, x_1002);
lean_ctor_set(x_1005, 1, x_1003);
return x_1005;
}
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1006 = lean_ctor_get(x_871, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_871, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 x_1008 = x_871;
} else {
 lean_dec_ref(x_871);
 x_1008 = lean_box(0);
}
if (lean_is_scalar(x_1008)) {
 x_1009 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1009 = x_1008;
}
lean_ctor_set(x_1009, 0, x_1006);
lean_ctor_set(x_1009, 1, x_1007);
return x_1009;
}
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1010 = lean_ctor_get(x_868, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_868, 1);
lean_inc(x_1011);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_1012 = x_868;
} else {
 lean_dec_ref(x_868);
 x_1012 = lean_box(0);
}
if (lean_is_scalar(x_1012)) {
 x_1013 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1013 = x_1012;
}
lean_ctor_set(x_1013, 0, x_1010);
lean_ctor_set(x_1013, 1, x_1011);
return x_1013;
}
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1014 = lean_ctor_get(x_865, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_865, 1);
lean_inc(x_1015);
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 lean_ctor_release(x_865, 1);
 x_1016 = x_865;
} else {
 lean_dec_ref(x_865);
 x_1016 = lean_box(0);
}
if (lean_is_scalar(x_1016)) {
 x_1017 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1017 = x_1016;
}
lean_ctor_set(x_1017, 0, x_1014);
lean_ctor_set(x_1017, 1, x_1015);
return x_1017;
}
}
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1018 = lean_ctor_get(x_29, 0);
lean_inc(x_1018);
lean_dec(x_29);
x_1019 = lean_ctor_get(x_1018, 1);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_28, 1);
lean_inc(x_1020);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_1021 = x_28;
} else {
 lean_dec_ref(x_28);
 x_1021 = lean_box(0);
}
x_1022 = lean_ctor_get(x_1018, 0);
lean_inc(x_1022);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 x_1023 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1023 = lean_box(0);
}
x_1024 = lean_ctor_get(x_1019, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1019)) {
 lean_ctor_release(x_1019, 0);
 lean_ctor_release(x_1019, 1);
 x_1025 = x_1019;
} else {
 lean_dec_ref(x_1019);
 x_1025 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_1026 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_1020);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1027 = lean_ctor_get(x_1026, 0);
lean_inc(x_1027);
x_1028 = lean_ctor_get(x_1026, 1);
lean_inc(x_1028);
lean_dec(x_1026);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1022);
x_1029 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1022, x_5, x_6, x_7, x_8, x_1028);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_1032 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_1031);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_1035 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_1034);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1035, 1);
lean_inc(x_1037);
lean_dec(x_1035);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1024);
x_1038 = lean_infer_type(x_1024, x_5, x_6, x_7, x_8, x_1037);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
lean_dec(x_1038);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1033);
x_1041 = l_Lean_Meta_getLevel(x_1033, x_5, x_6, x_7, x_8, x_1040);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
lean_dec(x_1041);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1036);
x_1044 = l_Lean_Meta_getLevel(x_1036, x_5, x_6, x_7, x_8, x_1043);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1045 = lean_ctor_get(x_1044, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1044, 1);
lean_inc(x_1046);
lean_dec(x_1044);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1039);
x_1047 = l_Lean_Meta_getLevel(x_1039, x_5, x_6, x_7, x_8, x_1046);
if (lean_obj_tag(x_1047) == 0)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; uint8_t x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
lean_dec(x_1047);
x_1050 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1049);
x_1051 = lean_ctor_get(x_1050, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1050, 1);
lean_inc(x_1052);
if (lean_is_exclusive(x_1050)) {
 lean_ctor_release(x_1050, 0);
 lean_ctor_release(x_1050, 1);
 x_1053 = x_1050;
} else {
 lean_dec_ref(x_1050);
 x_1053 = lean_box(0);
}
lean_inc(x_1051);
x_1054 = l_Lean_Expr_sort___override(x_1051);
lean_inc(x_1039);
x_1055 = l_Lean_mkArrow(x_1039, x_1054, x_7, x_8, x_1052);
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1055, 1);
lean_inc(x_1057);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 lean_ctor_release(x_1055, 1);
 x_1058 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1058 = lean_box(0);
}
lean_inc(x_1033);
x_1059 = l_Lean_mkArrow(x_1033, x_1056, x_7, x_8, x_1057);
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1059, 1);
lean_inc(x_1061);
if (lean_is_exclusive(x_1059)) {
 lean_ctor_release(x_1059, 0);
 lean_ctor_release(x_1059, 1);
 x_1062 = x_1059;
} else {
 lean_dec_ref(x_1059);
 x_1062 = lean_box(0);
}
x_1063 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1063, 0, x_1060);
x_1064 = 0;
x_1065 = lean_box(0);
lean_inc(x_5);
x_1066 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1063, x_1064, x_1065, x_5, x_6, x_7, x_8, x_1061);
x_1067 = lean_ctor_get(x_1066, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1066, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1069 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1069 = lean_box(0);
}
x_1070 = lean_box(0);
if (lean_is_scalar(x_1069)) {
 x_1071 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1071 = x_1069;
 lean_ctor_set_tag(x_1071, 1);
}
lean_ctor_set(x_1071, 0, x_1048);
lean_ctor_set(x_1071, 1, x_1070);
if (lean_is_scalar(x_1062)) {
 x_1072 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1072 = x_1062;
 lean_ctor_set_tag(x_1072, 1);
}
lean_ctor_set(x_1072, 0, x_1045);
lean_ctor_set(x_1072, 1, x_1071);
if (lean_is_scalar(x_1058)) {
 x_1073 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1073 = x_1058;
 lean_ctor_set_tag(x_1073, 1);
}
lean_ctor_set(x_1073, 0, x_1042);
lean_ctor_set(x_1073, 1, x_1072);
if (lean_is_scalar(x_1053)) {
 x_1074 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1074 = x_1053;
 lean_ctor_set_tag(x_1074, 1);
}
lean_ctor_set(x_1074, 0, x_1051);
lean_ctor_set(x_1074, 1, x_1073);
if (lean_is_scalar(x_1025)) {
 x_1075 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1075 = x_1025;
 lean_ctor_set_tag(x_1075, 1);
}
lean_ctor_set(x_1075, 0, x_1030);
lean_ctor_set(x_1075, 1, x_1074);
if (lean_is_scalar(x_1023)) {
 x_1076 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1076 = x_1023;
 lean_ctor_set_tag(x_1076, 1);
}
lean_ctor_set(x_1076, 0, x_1027);
lean_ctor_set(x_1076, 1, x_1075);
x_1077 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_1076);
x_1078 = l_Lean_Expr_const___override(x_1077, x_1076);
x_1079 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_1033);
x_1080 = lean_array_push(x_1079, x_1033);
lean_inc(x_1036);
x_1081 = lean_array_push(x_1080, x_1036);
lean_inc(x_1039);
x_1082 = lean_array_push(x_1081, x_1039);
lean_inc(x_19);
x_1083 = lean_array_push(x_1082, x_19);
lean_inc(x_1022);
x_1084 = lean_array_push(x_1083, x_1022);
lean_inc(x_1067);
x_1085 = lean_array_push(x_1084, x_1067);
x_1086 = l_Lean_mkAppN(x_1078, x_1085);
lean_dec(x_1085);
x_1087 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1086);
x_1088 = l_Lean_Meta_trySynthInstance(x_1086, x_1087, x_5, x_6, x_7, x_8, x_1068);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; 
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
if (lean_obj_tag(x_1089) == 1)
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_1086);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
lean_dec(x_1088);
x_1091 = lean_ctor_get(x_1089, 0);
lean_inc(x_1091);
lean_dec(x_1089);
x_1092 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_1093 = l_Lean_Expr_const___override(x_1092, x_1076);
x_1094 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_1095 = lean_array_push(x_1094, x_1033);
x_1096 = lean_array_push(x_1095, x_1036);
x_1097 = lean_array_push(x_1096, x_1039);
x_1098 = lean_array_push(x_1097, x_19);
x_1099 = lean_array_push(x_1098, x_1022);
x_1100 = lean_array_push(x_1099, x_1067);
x_1101 = lean_array_push(x_1100, x_1091);
x_1102 = lean_array_push(x_1101, x_22);
x_1103 = lean_array_push(x_1102, x_23);
x_1104 = lean_array_push(x_1103, x_1024);
x_1105 = lean_array_push(x_1104, x_1);
x_1106 = lean_array_push(x_1105, x_3);
x_1107 = l_Lean_mkAppN(x_1093, x_1106);
lean_dec(x_1106);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1107);
x_1108 = lean_infer_type(x_1107, x_5, x_6, x_7, x_8, x_1090);
if (lean_obj_tag(x_1108) == 0)
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
lean_dec(x_1108);
x_1111 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1109, x_5, x_6, x_7, x_8, x_1110);
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1111, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1111)) {
 lean_ctor_release(x_1111, 0);
 lean_ctor_release(x_1111, 1);
 x_1114 = x_1111;
} else {
 lean_dec_ref(x_1111);
 x_1114 = lean_box(0);
}
x_1115 = l_Lean_Expr_headBeta(x_1112);
x_1116 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1115, x_5, x_6, x_7, x_8, x_1113);
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
if (lean_obj_tag(x_1117) == 0)
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
lean_dec(x_1107);
x_1118 = lean_ctor_get(x_1116, 1);
lean_inc(x_1118);
if (lean_is_exclusive(x_1116)) {
 lean_ctor_release(x_1116, 0);
 lean_ctor_release(x_1116, 1);
 x_1119 = x_1116;
} else {
 lean_dec_ref(x_1116);
 x_1119 = lean_box(0);
}
x_1120 = l_Lean_indentExpr(x_1115);
x_1121 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_1119)) {
 x_1122 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1122 = x_1119;
 lean_ctor_set_tag(x_1122, 7);
}
lean_ctor_set(x_1122, 0, x_1121);
lean_ctor_set(x_1122, 1, x_1120);
x_1123 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1114)) {
 x_1124 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1124 = x_1114;
 lean_ctor_set_tag(x_1124, 7);
}
lean_ctor_set(x_1124, 0, x_1122);
lean_ctor_set(x_1124, 1, x_1123);
x_1125 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1124, x_5, x_6, x_7, x_8, x_1118);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
x_1127 = lean_ctor_get(x_1125, 1);
lean_inc(x_1127);
if (lean_is_exclusive(x_1125)) {
 lean_ctor_release(x_1125, 0);
 lean_ctor_release(x_1125, 1);
 x_1128 = x_1125;
} else {
 lean_dec_ref(x_1125);
 x_1128 = lean_box(0);
}
if (lean_is_scalar(x_1128)) {
 x_1129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1129 = x_1128;
}
lean_ctor_set(x_1129, 0, x_1126);
lean_ctor_set(x_1129, 1, x_1127);
return x_1129;
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
lean_dec(x_1117);
lean_dec(x_1114);
x_1130 = lean_ctor_get(x_1116, 1);
lean_inc(x_1130);
lean_dec(x_1116);
x_1131 = lean_box(0);
x_1132 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1107, x_1115, x_1131, x_5, x_6, x_7, x_8, x_1130);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1132;
}
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
lean_dec(x_1107);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1133 = lean_ctor_get(x_1108, 0);
lean_inc(x_1133);
x_1134 = lean_ctor_get(x_1108, 1);
lean_inc(x_1134);
if (lean_is_exclusive(x_1108)) {
 lean_ctor_release(x_1108, 0);
 lean_ctor_release(x_1108, 1);
 x_1135 = x_1108;
} else {
 lean_dec_ref(x_1108);
 x_1135 = lean_box(0);
}
if (lean_is_scalar(x_1135)) {
 x_1136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1136 = x_1135;
}
lean_ctor_set(x_1136, 0, x_1133);
lean_ctor_set(x_1136, 1, x_1134);
return x_1136;
}
}
else
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
lean_dec(x_1089);
lean_dec(x_1076);
lean_dec(x_1067);
lean_dec(x_1039);
lean_dec(x_1036);
lean_dec(x_1033);
lean_dec(x_1024);
lean_dec(x_1022);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1137 = lean_ctor_get(x_1088, 1);
lean_inc(x_1137);
lean_dec(x_1088);
x_1138 = l_Lean_indentExpr(x_1086);
x_1139 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
if (lean_is_scalar(x_1021)) {
 x_1140 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1140 = x_1021;
 lean_ctor_set_tag(x_1140, 7);
}
lean_ctor_set(x_1140, 0, x_1139);
lean_ctor_set(x_1140, 1, x_1138);
x_1141 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_1141);
lean_ctor_set(x_24, 0, x_1140);
x_1142 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_1142);
lean_ctor_set(x_16, 0, x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_1141);
lean_ctor_set(x_15, 0, x_16);
x_1143 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_1137);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1143;
}
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
lean_dec(x_1086);
lean_dec(x_1076);
lean_dec(x_1067);
lean_dec(x_1039);
lean_dec(x_1036);
lean_dec(x_1033);
lean_dec(x_1024);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1144 = lean_ctor_get(x_1088, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1088, 1);
lean_inc(x_1145);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1146 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1146 = lean_box(0);
}
if (lean_is_scalar(x_1146)) {
 x_1147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1147 = x_1146;
}
lean_ctor_set(x_1147, 0, x_1144);
lean_ctor_set(x_1147, 1, x_1145);
return x_1147;
}
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
lean_dec(x_1045);
lean_dec(x_1042);
lean_dec(x_1039);
lean_dec(x_1036);
lean_dec(x_1033);
lean_dec(x_1030);
lean_dec(x_1027);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1148 = lean_ctor_get(x_1047, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1047, 1);
lean_inc(x_1149);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1150 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1150 = lean_box(0);
}
if (lean_is_scalar(x_1150)) {
 x_1151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1151 = x_1150;
}
lean_ctor_set(x_1151, 0, x_1148);
lean_ctor_set(x_1151, 1, x_1149);
return x_1151;
}
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_1042);
lean_dec(x_1039);
lean_dec(x_1036);
lean_dec(x_1033);
lean_dec(x_1030);
lean_dec(x_1027);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1152 = lean_ctor_get(x_1044, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1044, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_1044)) {
 lean_ctor_release(x_1044, 0);
 lean_ctor_release(x_1044, 1);
 x_1154 = x_1044;
} else {
 lean_dec_ref(x_1044);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_1152);
lean_ctor_set(x_1155, 1, x_1153);
return x_1155;
}
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_1039);
lean_dec(x_1036);
lean_dec(x_1033);
lean_dec(x_1030);
lean_dec(x_1027);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1156 = lean_ctor_get(x_1041, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1041, 1);
lean_inc(x_1157);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1158 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1158 = lean_box(0);
}
if (lean_is_scalar(x_1158)) {
 x_1159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1159 = x_1158;
}
lean_ctor_set(x_1159, 0, x_1156);
lean_ctor_set(x_1159, 1, x_1157);
return x_1159;
}
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
lean_dec(x_1036);
lean_dec(x_1033);
lean_dec(x_1030);
lean_dec(x_1027);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1160 = lean_ctor_get(x_1038, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1038, 1);
lean_inc(x_1161);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1162 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1162 = lean_box(0);
}
if (lean_is_scalar(x_1162)) {
 x_1163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1163 = x_1162;
}
lean_ctor_set(x_1163, 0, x_1160);
lean_ctor_set(x_1163, 1, x_1161);
return x_1163;
}
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
lean_dec(x_1033);
lean_dec(x_1030);
lean_dec(x_1027);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1164 = lean_ctor_get(x_1035, 0);
lean_inc(x_1164);
x_1165 = lean_ctor_get(x_1035, 1);
lean_inc(x_1165);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1166 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1166 = lean_box(0);
}
if (lean_is_scalar(x_1166)) {
 x_1167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1167 = x_1166;
}
lean_ctor_set(x_1167, 0, x_1164);
lean_ctor_set(x_1167, 1, x_1165);
return x_1167;
}
}
else
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
lean_dec(x_1030);
lean_dec(x_1027);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1168 = lean_ctor_get(x_1032, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1032, 1);
lean_inc(x_1169);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 lean_ctor_release(x_1032, 1);
 x_1170 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1170 = lean_box(0);
}
if (lean_is_scalar(x_1170)) {
 x_1171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1171 = x_1170;
}
lean_ctor_set(x_1171, 0, x_1168);
lean_ctor_set(x_1171, 1, x_1169);
return x_1171;
}
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
lean_dec(x_1027);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1172 = lean_ctor_get(x_1029, 0);
lean_inc(x_1172);
x_1173 = lean_ctor_get(x_1029, 1);
lean_inc(x_1173);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1174 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1174 = lean_box(0);
}
if (lean_is_scalar(x_1174)) {
 x_1175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1175 = x_1174;
}
lean_ctor_set(x_1175, 0, x_1172);
lean_ctor_set(x_1175, 1, x_1173);
return x_1175;
}
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_free_object(x_24);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1176 = lean_ctor_get(x_1026, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1026, 1);
lean_inc(x_1177);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1178 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1178 = lean_box(0);
}
if (lean_is_scalar(x_1178)) {
 x_1179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1179 = x_1178;
}
lean_ctor_set(x_1179, 0, x_1176);
lean_ctor_set(x_1179, 1, x_1177);
return x_1179;
}
}
}
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1180 = lean_ctor_get(x_24, 0);
x_1181 = lean_ctor_get(x_24, 1);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_24);
x_1182 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1180, x_5, x_6, x_7, x_8, x_1181);
lean_dec(x_1180);
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
if (lean_obj_tag(x_1183) == 0)
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1184 = lean_ctor_get(x_1182, 1);
lean_inc(x_1184);
lean_dec(x_1182);
x_1185 = l_Lean_Elab_Term_mkCalcTrans___closed__5;
x_1186 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(x_1185, x_5, x_6, x_7, x_8, x_1184);
return x_1186;
}
else
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1187 = lean_ctor_get(x_1183, 0);
lean_inc(x_1187);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 x_1188 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1188 = lean_box(0);
}
x_1189 = lean_ctor_get(x_1187, 1);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1182, 1);
lean_inc(x_1190);
if (lean_is_exclusive(x_1182)) {
 lean_ctor_release(x_1182, 0);
 lean_ctor_release(x_1182, 1);
 x_1191 = x_1182;
} else {
 lean_dec_ref(x_1182);
 x_1191 = lean_box(0);
}
x_1192 = lean_ctor_get(x_1187, 0);
lean_inc(x_1192);
if (lean_is_exclusive(x_1187)) {
 lean_ctor_release(x_1187, 0);
 lean_ctor_release(x_1187, 1);
 x_1193 = x_1187;
} else {
 lean_dec_ref(x_1187);
 x_1193 = lean_box(0);
}
x_1194 = lean_ctor_get(x_1189, 1);
lean_inc(x_1194);
if (lean_is_exclusive(x_1189)) {
 lean_ctor_release(x_1189, 0);
 lean_ctor_release(x_1189, 1);
 x_1195 = x_1189;
} else {
 lean_dec_ref(x_1189);
 x_1195 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_1196 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_1190);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_1196, 1);
lean_inc(x_1198);
lean_dec(x_1196);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1192);
x_1199 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1192, x_5, x_6, x_7, x_8, x_1198);
if (lean_obj_tag(x_1199) == 0)
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1199, 1);
lean_inc(x_1201);
lean_dec(x_1199);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_1202 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_1201);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1203 = lean_ctor_get(x_1202, 0);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1202, 1);
lean_inc(x_1204);
lean_dec(x_1202);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_1205 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_1204);
if (lean_obj_tag(x_1205) == 0)
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1206 = lean_ctor_get(x_1205, 0);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_1205, 1);
lean_inc(x_1207);
lean_dec(x_1205);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1194);
x_1208 = lean_infer_type(x_1194, x_5, x_6, x_7, x_8, x_1207);
if (lean_obj_tag(x_1208) == 0)
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1209 = lean_ctor_get(x_1208, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1208, 1);
lean_inc(x_1210);
lean_dec(x_1208);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1203);
x_1211 = l_Lean_Meta_getLevel(x_1203, x_5, x_6, x_7, x_8, x_1210);
if (lean_obj_tag(x_1211) == 0)
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
x_1212 = lean_ctor_get(x_1211, 0);
lean_inc(x_1212);
x_1213 = lean_ctor_get(x_1211, 1);
lean_inc(x_1213);
lean_dec(x_1211);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1206);
x_1214 = l_Lean_Meta_getLevel(x_1206, x_5, x_6, x_7, x_8, x_1213);
if (lean_obj_tag(x_1214) == 0)
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
x_1215 = lean_ctor_get(x_1214, 0);
lean_inc(x_1215);
x_1216 = lean_ctor_get(x_1214, 1);
lean_inc(x_1216);
lean_dec(x_1214);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1209);
x_1217 = l_Lean_Meta_getLevel(x_1209, x_5, x_6, x_7, x_8, x_1216);
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; uint8_t x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; 
x_1218 = lean_ctor_get(x_1217, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1217, 1);
lean_inc(x_1219);
lean_dec(x_1217);
x_1220 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1219);
x_1221 = lean_ctor_get(x_1220, 0);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1220, 1);
lean_inc(x_1222);
if (lean_is_exclusive(x_1220)) {
 lean_ctor_release(x_1220, 0);
 lean_ctor_release(x_1220, 1);
 x_1223 = x_1220;
} else {
 lean_dec_ref(x_1220);
 x_1223 = lean_box(0);
}
lean_inc(x_1221);
x_1224 = l_Lean_Expr_sort___override(x_1221);
lean_inc(x_1209);
x_1225 = l_Lean_mkArrow(x_1209, x_1224, x_7, x_8, x_1222);
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
x_1227 = lean_ctor_get(x_1225, 1);
lean_inc(x_1227);
if (lean_is_exclusive(x_1225)) {
 lean_ctor_release(x_1225, 0);
 lean_ctor_release(x_1225, 1);
 x_1228 = x_1225;
} else {
 lean_dec_ref(x_1225);
 x_1228 = lean_box(0);
}
lean_inc(x_1203);
x_1229 = l_Lean_mkArrow(x_1203, x_1226, x_7, x_8, x_1227);
x_1230 = lean_ctor_get(x_1229, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1229, 1);
lean_inc(x_1231);
if (lean_is_exclusive(x_1229)) {
 lean_ctor_release(x_1229, 0);
 lean_ctor_release(x_1229, 1);
 x_1232 = x_1229;
} else {
 lean_dec_ref(x_1229);
 x_1232 = lean_box(0);
}
if (lean_is_scalar(x_1188)) {
 x_1233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1233 = x_1188;
}
lean_ctor_set(x_1233, 0, x_1230);
x_1234 = 0;
x_1235 = lean_box(0);
lean_inc(x_5);
x_1236 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1233, x_1234, x_1235, x_5, x_6, x_7, x_8, x_1231);
x_1237 = lean_ctor_get(x_1236, 0);
lean_inc(x_1237);
x_1238 = lean_ctor_get(x_1236, 1);
lean_inc(x_1238);
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 lean_ctor_release(x_1236, 1);
 x_1239 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1239 = lean_box(0);
}
x_1240 = lean_box(0);
if (lean_is_scalar(x_1239)) {
 x_1241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1241 = x_1239;
 lean_ctor_set_tag(x_1241, 1);
}
lean_ctor_set(x_1241, 0, x_1218);
lean_ctor_set(x_1241, 1, x_1240);
if (lean_is_scalar(x_1232)) {
 x_1242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1242 = x_1232;
 lean_ctor_set_tag(x_1242, 1);
}
lean_ctor_set(x_1242, 0, x_1215);
lean_ctor_set(x_1242, 1, x_1241);
if (lean_is_scalar(x_1228)) {
 x_1243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1243 = x_1228;
 lean_ctor_set_tag(x_1243, 1);
}
lean_ctor_set(x_1243, 0, x_1212);
lean_ctor_set(x_1243, 1, x_1242);
if (lean_is_scalar(x_1223)) {
 x_1244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1244 = x_1223;
 lean_ctor_set_tag(x_1244, 1);
}
lean_ctor_set(x_1244, 0, x_1221);
lean_ctor_set(x_1244, 1, x_1243);
if (lean_is_scalar(x_1195)) {
 x_1245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1245 = x_1195;
 lean_ctor_set_tag(x_1245, 1);
}
lean_ctor_set(x_1245, 0, x_1200);
lean_ctor_set(x_1245, 1, x_1244);
if (lean_is_scalar(x_1193)) {
 x_1246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1246 = x_1193;
 lean_ctor_set_tag(x_1246, 1);
}
lean_ctor_set(x_1246, 0, x_1197);
lean_ctor_set(x_1246, 1, x_1245);
x_1247 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_1246);
x_1248 = l_Lean_Expr_const___override(x_1247, x_1246);
x_1249 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_1203);
x_1250 = lean_array_push(x_1249, x_1203);
lean_inc(x_1206);
x_1251 = lean_array_push(x_1250, x_1206);
lean_inc(x_1209);
x_1252 = lean_array_push(x_1251, x_1209);
lean_inc(x_19);
x_1253 = lean_array_push(x_1252, x_19);
lean_inc(x_1192);
x_1254 = lean_array_push(x_1253, x_1192);
lean_inc(x_1237);
x_1255 = lean_array_push(x_1254, x_1237);
x_1256 = l_Lean_mkAppN(x_1248, x_1255);
lean_dec(x_1255);
x_1257 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1256);
x_1258 = l_Lean_Meta_trySynthInstance(x_1256, x_1257, x_5, x_6, x_7, x_8, x_1238);
if (lean_obj_tag(x_1258) == 0)
{
lean_object* x_1259; 
x_1259 = lean_ctor_get(x_1258, 0);
lean_inc(x_1259);
if (lean_obj_tag(x_1259) == 1)
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
lean_dec(x_1256);
lean_dec(x_1191);
lean_free_object(x_16);
lean_free_object(x_15);
x_1260 = lean_ctor_get(x_1258, 1);
lean_inc(x_1260);
lean_dec(x_1258);
x_1261 = lean_ctor_get(x_1259, 0);
lean_inc(x_1261);
lean_dec(x_1259);
x_1262 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_1263 = l_Lean_Expr_const___override(x_1262, x_1246);
x_1264 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_1265 = lean_array_push(x_1264, x_1203);
x_1266 = lean_array_push(x_1265, x_1206);
x_1267 = lean_array_push(x_1266, x_1209);
x_1268 = lean_array_push(x_1267, x_19);
x_1269 = lean_array_push(x_1268, x_1192);
x_1270 = lean_array_push(x_1269, x_1237);
x_1271 = lean_array_push(x_1270, x_1261);
x_1272 = lean_array_push(x_1271, x_22);
x_1273 = lean_array_push(x_1272, x_23);
x_1274 = lean_array_push(x_1273, x_1194);
x_1275 = lean_array_push(x_1274, x_1);
x_1276 = lean_array_push(x_1275, x_3);
x_1277 = l_Lean_mkAppN(x_1263, x_1276);
lean_dec(x_1276);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1277);
x_1278 = lean_infer_type(x_1277, x_5, x_6, x_7, x_8, x_1260);
if (lean_obj_tag(x_1278) == 0)
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1279 = lean_ctor_get(x_1278, 0);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_1278, 1);
lean_inc(x_1280);
lean_dec(x_1278);
x_1281 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1279, x_5, x_6, x_7, x_8, x_1280);
x_1282 = lean_ctor_get(x_1281, 0);
lean_inc(x_1282);
x_1283 = lean_ctor_get(x_1281, 1);
lean_inc(x_1283);
if (lean_is_exclusive(x_1281)) {
 lean_ctor_release(x_1281, 0);
 lean_ctor_release(x_1281, 1);
 x_1284 = x_1281;
} else {
 lean_dec_ref(x_1281);
 x_1284 = lean_box(0);
}
x_1285 = l_Lean_Expr_headBeta(x_1282);
x_1286 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1285, x_5, x_6, x_7, x_8, x_1283);
x_1287 = lean_ctor_get(x_1286, 0);
lean_inc(x_1287);
if (lean_obj_tag(x_1287) == 0)
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
lean_dec(x_1277);
x_1288 = lean_ctor_get(x_1286, 1);
lean_inc(x_1288);
if (lean_is_exclusive(x_1286)) {
 lean_ctor_release(x_1286, 0);
 lean_ctor_release(x_1286, 1);
 x_1289 = x_1286;
} else {
 lean_dec_ref(x_1286);
 x_1289 = lean_box(0);
}
x_1290 = l_Lean_indentExpr(x_1285);
x_1291 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_1289)) {
 x_1292 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1292 = x_1289;
 lean_ctor_set_tag(x_1292, 7);
}
lean_ctor_set(x_1292, 0, x_1291);
lean_ctor_set(x_1292, 1, x_1290);
x_1293 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1284)) {
 x_1294 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1294 = x_1284;
 lean_ctor_set_tag(x_1294, 7);
}
lean_ctor_set(x_1294, 0, x_1292);
lean_ctor_set(x_1294, 1, x_1293);
x_1295 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1294, x_5, x_6, x_7, x_8, x_1288);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1295, 1);
lean_inc(x_1297);
if (lean_is_exclusive(x_1295)) {
 lean_ctor_release(x_1295, 0);
 lean_ctor_release(x_1295, 1);
 x_1298 = x_1295;
} else {
 lean_dec_ref(x_1295);
 x_1298 = lean_box(0);
}
if (lean_is_scalar(x_1298)) {
 x_1299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1299 = x_1298;
}
lean_ctor_set(x_1299, 0, x_1296);
lean_ctor_set(x_1299, 1, x_1297);
return x_1299;
}
else
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
lean_dec(x_1287);
lean_dec(x_1284);
x_1300 = lean_ctor_get(x_1286, 1);
lean_inc(x_1300);
lean_dec(x_1286);
x_1301 = lean_box(0);
x_1302 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1277, x_1285, x_1301, x_5, x_6, x_7, x_8, x_1300);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1302;
}
}
else
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
lean_dec(x_1277);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1303 = lean_ctor_get(x_1278, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1278, 1);
lean_inc(x_1304);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 lean_ctor_release(x_1278, 1);
 x_1305 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1305 = lean_box(0);
}
if (lean_is_scalar(x_1305)) {
 x_1306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1306 = x_1305;
}
lean_ctor_set(x_1306, 0, x_1303);
lean_ctor_set(x_1306, 1, x_1304);
return x_1306;
}
}
else
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1259);
lean_dec(x_1246);
lean_dec(x_1237);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1203);
lean_dec(x_1194);
lean_dec(x_1192);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1307 = lean_ctor_get(x_1258, 1);
lean_inc(x_1307);
lean_dec(x_1258);
x_1308 = l_Lean_indentExpr(x_1256);
x_1309 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
if (lean_is_scalar(x_1191)) {
 x_1310 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1310 = x_1191;
 lean_ctor_set_tag(x_1310, 7);
}
lean_ctor_set(x_1310, 0, x_1309);
lean_ctor_set(x_1310, 1, x_1308);
x_1311 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
x_1312 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1312, 0, x_1310);
lean_ctor_set(x_1312, 1, x_1311);
x_1313 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_1313);
lean_ctor_set(x_16, 0, x_1312);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_1311);
lean_ctor_set(x_15, 0, x_16);
x_1314 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_1307);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1314;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_1256);
lean_dec(x_1246);
lean_dec(x_1237);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1203);
lean_dec(x_1194);
lean_dec(x_1192);
lean_dec(x_1191);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1315 = lean_ctor_get(x_1258, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1258, 1);
lean_inc(x_1316);
if (lean_is_exclusive(x_1258)) {
 lean_ctor_release(x_1258, 0);
 lean_ctor_release(x_1258, 1);
 x_1317 = x_1258;
} else {
 lean_dec_ref(x_1258);
 x_1317 = lean_box(0);
}
if (lean_is_scalar(x_1317)) {
 x_1318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1318 = x_1317;
}
lean_ctor_set(x_1318, 0, x_1315);
lean_ctor_set(x_1318, 1, x_1316);
return x_1318;
}
}
else
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
lean_dec(x_1215);
lean_dec(x_1212);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1203);
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1188);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1319 = lean_ctor_get(x_1217, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1217, 1);
lean_inc(x_1320);
if (lean_is_exclusive(x_1217)) {
 lean_ctor_release(x_1217, 0);
 lean_ctor_release(x_1217, 1);
 x_1321 = x_1217;
} else {
 lean_dec_ref(x_1217);
 x_1321 = lean_box(0);
}
if (lean_is_scalar(x_1321)) {
 x_1322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1322 = x_1321;
}
lean_ctor_set(x_1322, 0, x_1319);
lean_ctor_set(x_1322, 1, x_1320);
return x_1322;
}
}
else
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_1212);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1203);
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1188);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1323 = lean_ctor_get(x_1214, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1214, 1);
lean_inc(x_1324);
if (lean_is_exclusive(x_1214)) {
 lean_ctor_release(x_1214, 0);
 lean_ctor_release(x_1214, 1);
 x_1325 = x_1214;
} else {
 lean_dec_ref(x_1214);
 x_1325 = lean_box(0);
}
if (lean_is_scalar(x_1325)) {
 x_1326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1326 = x_1325;
}
lean_ctor_set(x_1326, 0, x_1323);
lean_ctor_set(x_1326, 1, x_1324);
return x_1326;
}
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1203);
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1188);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1327 = lean_ctor_get(x_1211, 0);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1211, 1);
lean_inc(x_1328);
if (lean_is_exclusive(x_1211)) {
 lean_ctor_release(x_1211, 0);
 lean_ctor_release(x_1211, 1);
 x_1329 = x_1211;
} else {
 lean_dec_ref(x_1211);
 x_1329 = lean_box(0);
}
if (lean_is_scalar(x_1329)) {
 x_1330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1330 = x_1329;
}
lean_ctor_set(x_1330, 0, x_1327);
lean_ctor_set(x_1330, 1, x_1328);
return x_1330;
}
}
else
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
lean_dec(x_1206);
lean_dec(x_1203);
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1188);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1331 = lean_ctor_get(x_1208, 0);
lean_inc(x_1331);
x_1332 = lean_ctor_get(x_1208, 1);
lean_inc(x_1332);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1333 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1333 = lean_box(0);
}
if (lean_is_scalar(x_1333)) {
 x_1334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1334 = x_1333;
}
lean_ctor_set(x_1334, 0, x_1331);
lean_ctor_set(x_1334, 1, x_1332);
return x_1334;
}
}
else
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
lean_dec(x_1203);
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1188);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1335 = lean_ctor_get(x_1205, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1205, 1);
lean_inc(x_1336);
if (lean_is_exclusive(x_1205)) {
 lean_ctor_release(x_1205, 0);
 lean_ctor_release(x_1205, 1);
 x_1337 = x_1205;
} else {
 lean_dec_ref(x_1205);
 x_1337 = lean_box(0);
}
if (lean_is_scalar(x_1337)) {
 x_1338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1338 = x_1337;
}
lean_ctor_set(x_1338, 0, x_1335);
lean_ctor_set(x_1338, 1, x_1336);
return x_1338;
}
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; 
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1188);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1339 = lean_ctor_get(x_1202, 0);
lean_inc(x_1339);
x_1340 = lean_ctor_get(x_1202, 1);
lean_inc(x_1340);
if (lean_is_exclusive(x_1202)) {
 lean_ctor_release(x_1202, 0);
 lean_ctor_release(x_1202, 1);
 x_1341 = x_1202;
} else {
 lean_dec_ref(x_1202);
 x_1341 = lean_box(0);
}
if (lean_is_scalar(x_1341)) {
 x_1342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1342 = x_1341;
}
lean_ctor_set(x_1342, 0, x_1339);
lean_ctor_set(x_1342, 1, x_1340);
return x_1342;
}
}
else
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; 
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1188);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1343 = lean_ctor_get(x_1199, 0);
lean_inc(x_1343);
x_1344 = lean_ctor_get(x_1199, 1);
lean_inc(x_1344);
if (lean_is_exclusive(x_1199)) {
 lean_ctor_release(x_1199, 0);
 lean_ctor_release(x_1199, 1);
 x_1345 = x_1199;
} else {
 lean_dec_ref(x_1199);
 x_1345 = lean_box(0);
}
if (lean_is_scalar(x_1345)) {
 x_1346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1346 = x_1345;
}
lean_ctor_set(x_1346, 0, x_1343);
lean_ctor_set(x_1346, 1, x_1344);
return x_1346;
}
}
else
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1188);
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1347 = lean_ctor_get(x_1196, 0);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1196, 1);
lean_inc(x_1348);
if (lean_is_exclusive(x_1196)) {
 lean_ctor_release(x_1196, 0);
 lean_ctor_release(x_1196, 1);
 x_1349 = x_1196;
} else {
 lean_dec_ref(x_1196);
 x_1349 = lean_box(0);
}
if (lean_is_scalar(x_1349)) {
 x_1350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1350 = x_1349;
}
lean_ctor_set(x_1350, 0, x_1347);
lean_ctor_set(x_1350, 1, x_1348);
return x_1350;
}
}
}
}
else
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
x_1351 = lean_ctor_get(x_16, 0);
x_1352 = lean_ctor_get(x_16, 1);
lean_inc(x_1352);
lean_inc(x_1351);
lean_dec(x_16);
x_1353 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_4, x_5, x_6, x_7, x_8, x_17);
x_1354 = lean_ctor_get(x_1353, 0);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1353, 1);
lean_inc(x_1355);
if (lean_is_exclusive(x_1353)) {
 lean_ctor_release(x_1353, 0);
 lean_ctor_release(x_1353, 1);
 x_1356 = x_1353;
} else {
 lean_dec_ref(x_1353);
 x_1356 = lean_box(0);
}
x_1357 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1354, x_5, x_6, x_7, x_8, x_1355);
lean_dec(x_1354);
x_1358 = lean_ctor_get(x_1357, 0);
lean_inc(x_1358);
if (lean_obj_tag(x_1358) == 0)
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1359 = lean_ctor_get(x_1357, 1);
lean_inc(x_1359);
lean_dec(x_1357);
x_1360 = l_Lean_Elab_Term_mkCalcTrans___closed__5;
x_1361 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(x_1360, x_5, x_6, x_7, x_8, x_1359);
return x_1361;
}
else
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1362 = lean_ctor_get(x_1358, 0);
lean_inc(x_1362);
if (lean_is_exclusive(x_1358)) {
 lean_ctor_release(x_1358, 0);
 x_1363 = x_1358;
} else {
 lean_dec_ref(x_1358);
 x_1363 = lean_box(0);
}
x_1364 = lean_ctor_get(x_1362, 1);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1357, 1);
lean_inc(x_1365);
if (lean_is_exclusive(x_1357)) {
 lean_ctor_release(x_1357, 0);
 lean_ctor_release(x_1357, 1);
 x_1366 = x_1357;
} else {
 lean_dec_ref(x_1357);
 x_1366 = lean_box(0);
}
x_1367 = lean_ctor_get(x_1362, 0);
lean_inc(x_1367);
if (lean_is_exclusive(x_1362)) {
 lean_ctor_release(x_1362, 0);
 lean_ctor_release(x_1362, 1);
 x_1368 = x_1362;
} else {
 lean_dec_ref(x_1362);
 x_1368 = lean_box(0);
}
x_1369 = lean_ctor_get(x_1364, 1);
lean_inc(x_1369);
if (lean_is_exclusive(x_1364)) {
 lean_ctor_release(x_1364, 0);
 lean_ctor_release(x_1364, 1);
 x_1370 = x_1364;
} else {
 lean_dec_ref(x_1364);
 x_1370 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_1371 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_1365);
if (lean_obj_tag(x_1371) == 0)
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1372 = lean_ctor_get(x_1371, 0);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_1371, 1);
lean_inc(x_1373);
lean_dec(x_1371);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1367);
x_1374 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1367, x_5, x_6, x_7, x_8, x_1373);
if (lean_obj_tag(x_1374) == 0)
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1375 = lean_ctor_get(x_1374, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1374, 1);
lean_inc(x_1376);
lean_dec(x_1374);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1351);
x_1377 = lean_infer_type(x_1351, x_5, x_6, x_7, x_8, x_1376);
if (lean_obj_tag(x_1377) == 0)
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; 
x_1378 = lean_ctor_get(x_1377, 0);
lean_inc(x_1378);
x_1379 = lean_ctor_get(x_1377, 1);
lean_inc(x_1379);
lean_dec(x_1377);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1352);
x_1380 = lean_infer_type(x_1352, x_5, x_6, x_7, x_8, x_1379);
if (lean_obj_tag(x_1380) == 0)
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
x_1381 = lean_ctor_get(x_1380, 0);
lean_inc(x_1381);
x_1382 = lean_ctor_get(x_1380, 1);
lean_inc(x_1382);
lean_dec(x_1380);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1369);
x_1383 = lean_infer_type(x_1369, x_5, x_6, x_7, x_8, x_1382);
if (lean_obj_tag(x_1383) == 0)
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1384 = lean_ctor_get(x_1383, 0);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_1383, 1);
lean_inc(x_1385);
lean_dec(x_1383);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1378);
x_1386 = l_Lean_Meta_getLevel(x_1378, x_5, x_6, x_7, x_8, x_1385);
if (lean_obj_tag(x_1386) == 0)
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
x_1387 = lean_ctor_get(x_1386, 0);
lean_inc(x_1387);
x_1388 = lean_ctor_get(x_1386, 1);
lean_inc(x_1388);
lean_dec(x_1386);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1381);
x_1389 = l_Lean_Meta_getLevel(x_1381, x_5, x_6, x_7, x_8, x_1388);
if (lean_obj_tag(x_1389) == 0)
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
x_1390 = lean_ctor_get(x_1389, 0);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1389, 1);
lean_inc(x_1391);
lean_dec(x_1389);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1384);
x_1392 = l_Lean_Meta_getLevel(x_1384, x_5, x_6, x_7, x_8, x_1391);
if (lean_obj_tag(x_1392) == 0)
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; uint8_t x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; 
x_1393 = lean_ctor_get(x_1392, 0);
lean_inc(x_1393);
x_1394 = lean_ctor_get(x_1392, 1);
lean_inc(x_1394);
lean_dec(x_1392);
x_1395 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1394);
x_1396 = lean_ctor_get(x_1395, 0);
lean_inc(x_1396);
x_1397 = lean_ctor_get(x_1395, 1);
lean_inc(x_1397);
if (lean_is_exclusive(x_1395)) {
 lean_ctor_release(x_1395, 0);
 lean_ctor_release(x_1395, 1);
 x_1398 = x_1395;
} else {
 lean_dec_ref(x_1395);
 x_1398 = lean_box(0);
}
lean_inc(x_1396);
x_1399 = l_Lean_Expr_sort___override(x_1396);
lean_inc(x_1384);
x_1400 = l_Lean_mkArrow(x_1384, x_1399, x_7, x_8, x_1397);
x_1401 = lean_ctor_get(x_1400, 0);
lean_inc(x_1401);
x_1402 = lean_ctor_get(x_1400, 1);
lean_inc(x_1402);
if (lean_is_exclusive(x_1400)) {
 lean_ctor_release(x_1400, 0);
 lean_ctor_release(x_1400, 1);
 x_1403 = x_1400;
} else {
 lean_dec_ref(x_1400);
 x_1403 = lean_box(0);
}
lean_inc(x_1378);
x_1404 = l_Lean_mkArrow(x_1378, x_1401, x_7, x_8, x_1402);
x_1405 = lean_ctor_get(x_1404, 0);
lean_inc(x_1405);
x_1406 = lean_ctor_get(x_1404, 1);
lean_inc(x_1406);
if (lean_is_exclusive(x_1404)) {
 lean_ctor_release(x_1404, 0);
 lean_ctor_release(x_1404, 1);
 x_1407 = x_1404;
} else {
 lean_dec_ref(x_1404);
 x_1407 = lean_box(0);
}
if (lean_is_scalar(x_1363)) {
 x_1408 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1408 = x_1363;
}
lean_ctor_set(x_1408, 0, x_1405);
x_1409 = 0;
x_1410 = lean_box(0);
lean_inc(x_5);
x_1411 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1408, x_1409, x_1410, x_5, x_6, x_7, x_8, x_1406);
x_1412 = lean_ctor_get(x_1411, 0);
lean_inc(x_1412);
x_1413 = lean_ctor_get(x_1411, 1);
lean_inc(x_1413);
if (lean_is_exclusive(x_1411)) {
 lean_ctor_release(x_1411, 0);
 lean_ctor_release(x_1411, 1);
 x_1414 = x_1411;
} else {
 lean_dec_ref(x_1411);
 x_1414 = lean_box(0);
}
x_1415 = lean_box(0);
if (lean_is_scalar(x_1414)) {
 x_1416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1416 = x_1414;
 lean_ctor_set_tag(x_1416, 1);
}
lean_ctor_set(x_1416, 0, x_1393);
lean_ctor_set(x_1416, 1, x_1415);
if (lean_is_scalar(x_1407)) {
 x_1417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1417 = x_1407;
 lean_ctor_set_tag(x_1417, 1);
}
lean_ctor_set(x_1417, 0, x_1390);
lean_ctor_set(x_1417, 1, x_1416);
if (lean_is_scalar(x_1403)) {
 x_1418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1418 = x_1403;
 lean_ctor_set_tag(x_1418, 1);
}
lean_ctor_set(x_1418, 0, x_1387);
lean_ctor_set(x_1418, 1, x_1417);
if (lean_is_scalar(x_1398)) {
 x_1419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1419 = x_1398;
 lean_ctor_set_tag(x_1419, 1);
}
lean_ctor_set(x_1419, 0, x_1396);
lean_ctor_set(x_1419, 1, x_1418);
if (lean_is_scalar(x_1370)) {
 x_1420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1420 = x_1370;
 lean_ctor_set_tag(x_1420, 1);
}
lean_ctor_set(x_1420, 0, x_1375);
lean_ctor_set(x_1420, 1, x_1419);
if (lean_is_scalar(x_1368)) {
 x_1421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1421 = x_1368;
 lean_ctor_set_tag(x_1421, 1);
}
lean_ctor_set(x_1421, 0, x_1372);
lean_ctor_set(x_1421, 1, x_1420);
x_1422 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_1421);
x_1423 = l_Lean_Expr_const___override(x_1422, x_1421);
x_1424 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_1378);
x_1425 = lean_array_push(x_1424, x_1378);
lean_inc(x_1381);
x_1426 = lean_array_push(x_1425, x_1381);
lean_inc(x_1384);
x_1427 = lean_array_push(x_1426, x_1384);
lean_inc(x_19);
x_1428 = lean_array_push(x_1427, x_19);
lean_inc(x_1367);
x_1429 = lean_array_push(x_1428, x_1367);
lean_inc(x_1412);
x_1430 = lean_array_push(x_1429, x_1412);
x_1431 = l_Lean_mkAppN(x_1423, x_1430);
lean_dec(x_1430);
x_1432 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1431);
x_1433 = l_Lean_Meta_trySynthInstance(x_1431, x_1432, x_5, x_6, x_7, x_8, x_1413);
if (lean_obj_tag(x_1433) == 0)
{
lean_object* x_1434; 
x_1434 = lean_ctor_get(x_1433, 0);
lean_inc(x_1434);
if (lean_obj_tag(x_1434) == 1)
{
lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
lean_dec(x_1431);
lean_dec(x_1366);
lean_dec(x_1356);
lean_free_object(x_15);
x_1435 = lean_ctor_get(x_1433, 1);
lean_inc(x_1435);
lean_dec(x_1433);
x_1436 = lean_ctor_get(x_1434, 0);
lean_inc(x_1436);
lean_dec(x_1434);
x_1437 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_1438 = l_Lean_Expr_const___override(x_1437, x_1421);
x_1439 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_1440 = lean_array_push(x_1439, x_1378);
x_1441 = lean_array_push(x_1440, x_1381);
x_1442 = lean_array_push(x_1441, x_1384);
x_1443 = lean_array_push(x_1442, x_19);
x_1444 = lean_array_push(x_1443, x_1367);
x_1445 = lean_array_push(x_1444, x_1412);
x_1446 = lean_array_push(x_1445, x_1436);
x_1447 = lean_array_push(x_1446, x_1351);
x_1448 = lean_array_push(x_1447, x_1352);
x_1449 = lean_array_push(x_1448, x_1369);
x_1450 = lean_array_push(x_1449, x_1);
x_1451 = lean_array_push(x_1450, x_3);
x_1452 = l_Lean_mkAppN(x_1438, x_1451);
lean_dec(x_1451);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1452);
x_1453 = lean_infer_type(x_1452, x_5, x_6, x_7, x_8, x_1435);
if (lean_obj_tag(x_1453) == 0)
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
x_1454 = lean_ctor_get(x_1453, 0);
lean_inc(x_1454);
x_1455 = lean_ctor_get(x_1453, 1);
lean_inc(x_1455);
lean_dec(x_1453);
x_1456 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1454, x_5, x_6, x_7, x_8, x_1455);
x_1457 = lean_ctor_get(x_1456, 0);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1456, 1);
lean_inc(x_1458);
if (lean_is_exclusive(x_1456)) {
 lean_ctor_release(x_1456, 0);
 lean_ctor_release(x_1456, 1);
 x_1459 = x_1456;
} else {
 lean_dec_ref(x_1456);
 x_1459 = lean_box(0);
}
x_1460 = l_Lean_Expr_headBeta(x_1457);
x_1461 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1460, x_5, x_6, x_7, x_8, x_1458);
x_1462 = lean_ctor_get(x_1461, 0);
lean_inc(x_1462);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
lean_dec(x_1452);
x_1463 = lean_ctor_get(x_1461, 1);
lean_inc(x_1463);
if (lean_is_exclusive(x_1461)) {
 lean_ctor_release(x_1461, 0);
 lean_ctor_release(x_1461, 1);
 x_1464 = x_1461;
} else {
 lean_dec_ref(x_1461);
 x_1464 = lean_box(0);
}
x_1465 = l_Lean_indentExpr(x_1460);
x_1466 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_1464)) {
 x_1467 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1467 = x_1464;
 lean_ctor_set_tag(x_1467, 7);
}
lean_ctor_set(x_1467, 0, x_1466);
lean_ctor_set(x_1467, 1, x_1465);
x_1468 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1459)) {
 x_1469 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1469 = x_1459;
 lean_ctor_set_tag(x_1469, 7);
}
lean_ctor_set(x_1469, 0, x_1467);
lean_ctor_set(x_1469, 1, x_1468);
x_1470 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1469, x_5, x_6, x_7, x_8, x_1463);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1471 = lean_ctor_get(x_1470, 0);
lean_inc(x_1471);
x_1472 = lean_ctor_get(x_1470, 1);
lean_inc(x_1472);
if (lean_is_exclusive(x_1470)) {
 lean_ctor_release(x_1470, 0);
 lean_ctor_release(x_1470, 1);
 x_1473 = x_1470;
} else {
 lean_dec_ref(x_1470);
 x_1473 = lean_box(0);
}
if (lean_is_scalar(x_1473)) {
 x_1474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1474 = x_1473;
}
lean_ctor_set(x_1474, 0, x_1471);
lean_ctor_set(x_1474, 1, x_1472);
return x_1474;
}
else
{
lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; 
lean_dec(x_1462);
lean_dec(x_1459);
x_1475 = lean_ctor_get(x_1461, 1);
lean_inc(x_1475);
lean_dec(x_1461);
x_1476 = lean_box(0);
x_1477 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1452, x_1460, x_1476, x_5, x_6, x_7, x_8, x_1475);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1477;
}
}
else
{
lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; 
lean_dec(x_1452);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1478 = lean_ctor_get(x_1453, 0);
lean_inc(x_1478);
x_1479 = lean_ctor_get(x_1453, 1);
lean_inc(x_1479);
if (lean_is_exclusive(x_1453)) {
 lean_ctor_release(x_1453, 0);
 lean_ctor_release(x_1453, 1);
 x_1480 = x_1453;
} else {
 lean_dec_ref(x_1453);
 x_1480 = lean_box(0);
}
if (lean_is_scalar(x_1480)) {
 x_1481 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1481 = x_1480;
}
lean_ctor_set(x_1481, 0, x_1478);
lean_ctor_set(x_1481, 1, x_1479);
return x_1481;
}
}
else
{
lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; 
lean_dec(x_1434);
lean_dec(x_1421);
lean_dec(x_1412);
lean_dec(x_1384);
lean_dec(x_1381);
lean_dec(x_1378);
lean_dec(x_1369);
lean_dec(x_1367);
lean_dec(x_1352);
lean_dec(x_1351);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1482 = lean_ctor_get(x_1433, 1);
lean_inc(x_1482);
lean_dec(x_1433);
x_1483 = l_Lean_indentExpr(x_1431);
x_1484 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
if (lean_is_scalar(x_1366)) {
 x_1485 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1485 = x_1366;
 lean_ctor_set_tag(x_1485, 7);
}
lean_ctor_set(x_1485, 0, x_1484);
lean_ctor_set(x_1485, 1, x_1483);
x_1486 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1356)) {
 x_1487 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1487 = x_1356;
 lean_ctor_set_tag(x_1487, 7);
}
lean_ctor_set(x_1487, 0, x_1485);
lean_ctor_set(x_1487, 1, x_1486);
x_1488 = l_Lean_useDiagnosticMsg;
x_1489 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1489, 0, x_1487);
lean_ctor_set(x_1489, 1, x_1488);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_1486);
lean_ctor_set(x_15, 0, x_1489);
x_1490 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_1482);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1490;
}
}
else
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
lean_dec(x_1431);
lean_dec(x_1421);
lean_dec(x_1412);
lean_dec(x_1384);
lean_dec(x_1381);
lean_dec(x_1378);
lean_dec(x_1369);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1491 = lean_ctor_get(x_1433, 0);
lean_inc(x_1491);
x_1492 = lean_ctor_get(x_1433, 1);
lean_inc(x_1492);
if (lean_is_exclusive(x_1433)) {
 lean_ctor_release(x_1433, 0);
 lean_ctor_release(x_1433, 1);
 x_1493 = x_1433;
} else {
 lean_dec_ref(x_1433);
 x_1493 = lean_box(0);
}
if (lean_is_scalar(x_1493)) {
 x_1494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1494 = x_1493;
}
lean_ctor_set(x_1494, 0, x_1491);
lean_ctor_set(x_1494, 1, x_1492);
return x_1494;
}
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
lean_dec(x_1390);
lean_dec(x_1387);
lean_dec(x_1384);
lean_dec(x_1381);
lean_dec(x_1378);
lean_dec(x_1375);
lean_dec(x_1372);
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1363);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1495 = lean_ctor_get(x_1392, 0);
lean_inc(x_1495);
x_1496 = lean_ctor_get(x_1392, 1);
lean_inc(x_1496);
if (lean_is_exclusive(x_1392)) {
 lean_ctor_release(x_1392, 0);
 lean_ctor_release(x_1392, 1);
 x_1497 = x_1392;
} else {
 lean_dec_ref(x_1392);
 x_1497 = lean_box(0);
}
if (lean_is_scalar(x_1497)) {
 x_1498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1498 = x_1497;
}
lean_ctor_set(x_1498, 0, x_1495);
lean_ctor_set(x_1498, 1, x_1496);
return x_1498;
}
}
else
{
lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; 
lean_dec(x_1387);
lean_dec(x_1384);
lean_dec(x_1381);
lean_dec(x_1378);
lean_dec(x_1375);
lean_dec(x_1372);
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1363);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1499 = lean_ctor_get(x_1389, 0);
lean_inc(x_1499);
x_1500 = lean_ctor_get(x_1389, 1);
lean_inc(x_1500);
if (lean_is_exclusive(x_1389)) {
 lean_ctor_release(x_1389, 0);
 lean_ctor_release(x_1389, 1);
 x_1501 = x_1389;
} else {
 lean_dec_ref(x_1389);
 x_1501 = lean_box(0);
}
if (lean_is_scalar(x_1501)) {
 x_1502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1502 = x_1501;
}
lean_ctor_set(x_1502, 0, x_1499);
lean_ctor_set(x_1502, 1, x_1500);
return x_1502;
}
}
else
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; 
lean_dec(x_1384);
lean_dec(x_1381);
lean_dec(x_1378);
lean_dec(x_1375);
lean_dec(x_1372);
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1363);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1503 = lean_ctor_get(x_1386, 0);
lean_inc(x_1503);
x_1504 = lean_ctor_get(x_1386, 1);
lean_inc(x_1504);
if (lean_is_exclusive(x_1386)) {
 lean_ctor_release(x_1386, 0);
 lean_ctor_release(x_1386, 1);
 x_1505 = x_1386;
} else {
 lean_dec_ref(x_1386);
 x_1505 = lean_box(0);
}
if (lean_is_scalar(x_1505)) {
 x_1506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1506 = x_1505;
}
lean_ctor_set(x_1506, 0, x_1503);
lean_ctor_set(x_1506, 1, x_1504);
return x_1506;
}
}
else
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; 
lean_dec(x_1381);
lean_dec(x_1378);
lean_dec(x_1375);
lean_dec(x_1372);
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1363);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1507 = lean_ctor_get(x_1383, 0);
lean_inc(x_1507);
x_1508 = lean_ctor_get(x_1383, 1);
lean_inc(x_1508);
if (lean_is_exclusive(x_1383)) {
 lean_ctor_release(x_1383, 0);
 lean_ctor_release(x_1383, 1);
 x_1509 = x_1383;
} else {
 lean_dec_ref(x_1383);
 x_1509 = lean_box(0);
}
if (lean_is_scalar(x_1509)) {
 x_1510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1510 = x_1509;
}
lean_ctor_set(x_1510, 0, x_1507);
lean_ctor_set(x_1510, 1, x_1508);
return x_1510;
}
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
lean_dec(x_1378);
lean_dec(x_1375);
lean_dec(x_1372);
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1363);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1511 = lean_ctor_get(x_1380, 0);
lean_inc(x_1511);
x_1512 = lean_ctor_get(x_1380, 1);
lean_inc(x_1512);
if (lean_is_exclusive(x_1380)) {
 lean_ctor_release(x_1380, 0);
 lean_ctor_release(x_1380, 1);
 x_1513 = x_1380;
} else {
 lean_dec_ref(x_1380);
 x_1513 = lean_box(0);
}
if (lean_is_scalar(x_1513)) {
 x_1514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1514 = x_1513;
}
lean_ctor_set(x_1514, 0, x_1511);
lean_ctor_set(x_1514, 1, x_1512);
return x_1514;
}
}
else
{
lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
lean_dec(x_1375);
lean_dec(x_1372);
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1363);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1515 = lean_ctor_get(x_1377, 0);
lean_inc(x_1515);
x_1516 = lean_ctor_get(x_1377, 1);
lean_inc(x_1516);
if (lean_is_exclusive(x_1377)) {
 lean_ctor_release(x_1377, 0);
 lean_ctor_release(x_1377, 1);
 x_1517 = x_1377;
} else {
 lean_dec_ref(x_1377);
 x_1517 = lean_box(0);
}
if (lean_is_scalar(x_1517)) {
 x_1518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1518 = x_1517;
}
lean_ctor_set(x_1518, 0, x_1515);
lean_ctor_set(x_1518, 1, x_1516);
return x_1518;
}
}
else
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; 
lean_dec(x_1372);
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1363);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1519 = lean_ctor_get(x_1374, 0);
lean_inc(x_1519);
x_1520 = lean_ctor_get(x_1374, 1);
lean_inc(x_1520);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1521 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1521 = lean_box(0);
}
if (lean_is_scalar(x_1521)) {
 x_1522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1522 = x_1521;
}
lean_ctor_set(x_1522, 0, x_1519);
lean_ctor_set(x_1522, 1, x_1520);
return x_1522;
}
}
else
{
lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; 
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1367);
lean_dec(x_1366);
lean_dec(x_1363);
lean_dec(x_1356);
lean_dec(x_1352);
lean_dec(x_1351);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1523 = lean_ctor_get(x_1371, 0);
lean_inc(x_1523);
x_1524 = lean_ctor_get(x_1371, 1);
lean_inc(x_1524);
if (lean_is_exclusive(x_1371)) {
 lean_ctor_release(x_1371, 0);
 lean_ctor_release(x_1371, 1);
 x_1525 = x_1371;
} else {
 lean_dec_ref(x_1371);
 x_1525 = lean_box(0);
}
if (lean_is_scalar(x_1525)) {
 x_1526 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1526 = x_1525;
}
lean_ctor_set(x_1526, 0, x_1523);
lean_ctor_set(x_1526, 1, x_1524);
return x_1526;
}
}
}
}
else
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; 
x_1527 = lean_ctor_get(x_15, 0);
lean_inc(x_1527);
lean_dec(x_15);
x_1528 = lean_ctor_get(x_16, 0);
lean_inc(x_1528);
x_1529 = lean_ctor_get(x_16, 1);
lean_inc(x_1529);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_1530 = x_16;
} else {
 lean_dec_ref(x_16);
 x_1530 = lean_box(0);
}
x_1531 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_4, x_5, x_6, x_7, x_8, x_17);
x_1532 = lean_ctor_get(x_1531, 0);
lean_inc(x_1532);
x_1533 = lean_ctor_get(x_1531, 1);
lean_inc(x_1533);
if (lean_is_exclusive(x_1531)) {
 lean_ctor_release(x_1531, 0);
 lean_ctor_release(x_1531, 1);
 x_1534 = x_1531;
} else {
 lean_dec_ref(x_1531);
 x_1534 = lean_box(0);
}
x_1535 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1532, x_5, x_6, x_7, x_8, x_1533);
lean_dec(x_1532);
x_1536 = lean_ctor_get(x_1535, 0);
lean_inc(x_1536);
if (lean_obj_tag(x_1536) == 0)
{
lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; 
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_3);
lean_dec(x_1);
x_1537 = lean_ctor_get(x_1535, 1);
lean_inc(x_1537);
lean_dec(x_1535);
x_1538 = l_Lean_Elab_Term_mkCalcTrans___closed__5;
x_1539 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(x_1538, x_5, x_6, x_7, x_8, x_1537);
return x_1539;
}
else
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; 
x_1540 = lean_ctor_get(x_1536, 0);
lean_inc(x_1540);
if (lean_is_exclusive(x_1536)) {
 lean_ctor_release(x_1536, 0);
 x_1541 = x_1536;
} else {
 lean_dec_ref(x_1536);
 x_1541 = lean_box(0);
}
x_1542 = lean_ctor_get(x_1540, 1);
lean_inc(x_1542);
x_1543 = lean_ctor_get(x_1535, 1);
lean_inc(x_1543);
if (lean_is_exclusive(x_1535)) {
 lean_ctor_release(x_1535, 0);
 lean_ctor_release(x_1535, 1);
 x_1544 = x_1535;
} else {
 lean_dec_ref(x_1535);
 x_1544 = lean_box(0);
}
x_1545 = lean_ctor_get(x_1540, 0);
lean_inc(x_1545);
if (lean_is_exclusive(x_1540)) {
 lean_ctor_release(x_1540, 0);
 lean_ctor_release(x_1540, 1);
 x_1546 = x_1540;
} else {
 lean_dec_ref(x_1540);
 x_1546 = lean_box(0);
}
x_1547 = lean_ctor_get(x_1542, 1);
lean_inc(x_1547);
if (lean_is_exclusive(x_1542)) {
 lean_ctor_release(x_1542, 0);
 lean_ctor_release(x_1542, 1);
 x_1548 = x_1542;
} else {
 lean_dec_ref(x_1542);
 x_1548 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1527);
x_1549 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1527, x_5, x_6, x_7, x_8, x_1543);
if (lean_obj_tag(x_1549) == 0)
{
lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; 
x_1550 = lean_ctor_get(x_1549, 0);
lean_inc(x_1550);
x_1551 = lean_ctor_get(x_1549, 1);
lean_inc(x_1551);
lean_dec(x_1549);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1545);
x_1552 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1545, x_5, x_6, x_7, x_8, x_1551);
if (lean_obj_tag(x_1552) == 0)
{
lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; 
x_1553 = lean_ctor_get(x_1552, 0);
lean_inc(x_1553);
x_1554 = lean_ctor_get(x_1552, 1);
lean_inc(x_1554);
lean_dec(x_1552);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1528);
x_1555 = lean_infer_type(x_1528, x_5, x_6, x_7, x_8, x_1554);
if (lean_obj_tag(x_1555) == 0)
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
x_1556 = lean_ctor_get(x_1555, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1555, 1);
lean_inc(x_1557);
lean_dec(x_1555);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1529);
x_1558 = lean_infer_type(x_1529, x_5, x_6, x_7, x_8, x_1557);
if (lean_obj_tag(x_1558) == 0)
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
x_1559 = lean_ctor_get(x_1558, 0);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_1558, 1);
lean_inc(x_1560);
lean_dec(x_1558);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1547);
x_1561 = lean_infer_type(x_1547, x_5, x_6, x_7, x_8, x_1560);
if (lean_obj_tag(x_1561) == 0)
{
lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; 
x_1562 = lean_ctor_get(x_1561, 0);
lean_inc(x_1562);
x_1563 = lean_ctor_get(x_1561, 1);
lean_inc(x_1563);
lean_dec(x_1561);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1556);
x_1564 = l_Lean_Meta_getLevel(x_1556, x_5, x_6, x_7, x_8, x_1563);
if (lean_obj_tag(x_1564) == 0)
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; 
x_1565 = lean_ctor_get(x_1564, 0);
lean_inc(x_1565);
x_1566 = lean_ctor_get(x_1564, 1);
lean_inc(x_1566);
lean_dec(x_1564);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1559);
x_1567 = l_Lean_Meta_getLevel(x_1559, x_5, x_6, x_7, x_8, x_1566);
if (lean_obj_tag(x_1567) == 0)
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
x_1568 = lean_ctor_get(x_1567, 0);
lean_inc(x_1568);
x_1569 = lean_ctor_get(x_1567, 1);
lean_inc(x_1569);
lean_dec(x_1567);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1562);
x_1570 = l_Lean_Meta_getLevel(x_1562, x_5, x_6, x_7, x_8, x_1569);
if (lean_obj_tag(x_1570) == 0)
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; uint8_t x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; 
x_1571 = lean_ctor_get(x_1570, 0);
lean_inc(x_1571);
x_1572 = lean_ctor_get(x_1570, 1);
lean_inc(x_1572);
lean_dec(x_1570);
x_1573 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1572);
x_1574 = lean_ctor_get(x_1573, 0);
lean_inc(x_1574);
x_1575 = lean_ctor_get(x_1573, 1);
lean_inc(x_1575);
if (lean_is_exclusive(x_1573)) {
 lean_ctor_release(x_1573, 0);
 lean_ctor_release(x_1573, 1);
 x_1576 = x_1573;
} else {
 lean_dec_ref(x_1573);
 x_1576 = lean_box(0);
}
lean_inc(x_1574);
x_1577 = l_Lean_Expr_sort___override(x_1574);
lean_inc(x_1562);
x_1578 = l_Lean_mkArrow(x_1562, x_1577, x_7, x_8, x_1575);
x_1579 = lean_ctor_get(x_1578, 0);
lean_inc(x_1579);
x_1580 = lean_ctor_get(x_1578, 1);
lean_inc(x_1580);
if (lean_is_exclusive(x_1578)) {
 lean_ctor_release(x_1578, 0);
 lean_ctor_release(x_1578, 1);
 x_1581 = x_1578;
} else {
 lean_dec_ref(x_1578);
 x_1581 = lean_box(0);
}
lean_inc(x_1556);
x_1582 = l_Lean_mkArrow(x_1556, x_1579, x_7, x_8, x_1580);
x_1583 = lean_ctor_get(x_1582, 0);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_1582, 1);
lean_inc(x_1584);
if (lean_is_exclusive(x_1582)) {
 lean_ctor_release(x_1582, 0);
 lean_ctor_release(x_1582, 1);
 x_1585 = x_1582;
} else {
 lean_dec_ref(x_1582);
 x_1585 = lean_box(0);
}
if (lean_is_scalar(x_1541)) {
 x_1586 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1586 = x_1541;
}
lean_ctor_set(x_1586, 0, x_1583);
x_1587 = 0;
x_1588 = lean_box(0);
lean_inc(x_5);
x_1589 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1586, x_1587, x_1588, x_5, x_6, x_7, x_8, x_1584);
x_1590 = lean_ctor_get(x_1589, 0);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1589, 1);
lean_inc(x_1591);
if (lean_is_exclusive(x_1589)) {
 lean_ctor_release(x_1589, 0);
 lean_ctor_release(x_1589, 1);
 x_1592 = x_1589;
} else {
 lean_dec_ref(x_1589);
 x_1592 = lean_box(0);
}
x_1593 = lean_box(0);
if (lean_is_scalar(x_1592)) {
 x_1594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1594 = x_1592;
 lean_ctor_set_tag(x_1594, 1);
}
lean_ctor_set(x_1594, 0, x_1571);
lean_ctor_set(x_1594, 1, x_1593);
if (lean_is_scalar(x_1585)) {
 x_1595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1595 = x_1585;
 lean_ctor_set_tag(x_1595, 1);
}
lean_ctor_set(x_1595, 0, x_1568);
lean_ctor_set(x_1595, 1, x_1594);
if (lean_is_scalar(x_1581)) {
 x_1596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1596 = x_1581;
 lean_ctor_set_tag(x_1596, 1);
}
lean_ctor_set(x_1596, 0, x_1565);
lean_ctor_set(x_1596, 1, x_1595);
if (lean_is_scalar(x_1576)) {
 x_1597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1597 = x_1576;
 lean_ctor_set_tag(x_1597, 1);
}
lean_ctor_set(x_1597, 0, x_1574);
lean_ctor_set(x_1597, 1, x_1596);
if (lean_is_scalar(x_1548)) {
 x_1598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1598 = x_1548;
 lean_ctor_set_tag(x_1598, 1);
}
lean_ctor_set(x_1598, 0, x_1553);
lean_ctor_set(x_1598, 1, x_1597);
if (lean_is_scalar(x_1546)) {
 x_1599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1599 = x_1546;
 lean_ctor_set_tag(x_1599, 1);
}
lean_ctor_set(x_1599, 0, x_1550);
lean_ctor_set(x_1599, 1, x_1598);
x_1600 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_1599);
x_1601 = l_Lean_Expr_const___override(x_1600, x_1599);
x_1602 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_1556);
x_1603 = lean_array_push(x_1602, x_1556);
lean_inc(x_1559);
x_1604 = lean_array_push(x_1603, x_1559);
lean_inc(x_1562);
x_1605 = lean_array_push(x_1604, x_1562);
lean_inc(x_1527);
x_1606 = lean_array_push(x_1605, x_1527);
lean_inc(x_1545);
x_1607 = lean_array_push(x_1606, x_1545);
lean_inc(x_1590);
x_1608 = lean_array_push(x_1607, x_1590);
x_1609 = l_Lean_mkAppN(x_1601, x_1608);
lean_dec(x_1608);
x_1610 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1609);
x_1611 = l_Lean_Meta_trySynthInstance(x_1609, x_1610, x_5, x_6, x_7, x_8, x_1591);
if (lean_obj_tag(x_1611) == 0)
{
lean_object* x_1612; 
x_1612 = lean_ctor_get(x_1611, 0);
lean_inc(x_1612);
if (lean_obj_tag(x_1612) == 1)
{
lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
lean_dec(x_1609);
lean_dec(x_1544);
lean_dec(x_1534);
lean_dec(x_1530);
x_1613 = lean_ctor_get(x_1611, 1);
lean_inc(x_1613);
lean_dec(x_1611);
x_1614 = lean_ctor_get(x_1612, 0);
lean_inc(x_1614);
lean_dec(x_1612);
x_1615 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_1616 = l_Lean_Expr_const___override(x_1615, x_1599);
x_1617 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_1618 = lean_array_push(x_1617, x_1556);
x_1619 = lean_array_push(x_1618, x_1559);
x_1620 = lean_array_push(x_1619, x_1562);
x_1621 = lean_array_push(x_1620, x_1527);
x_1622 = lean_array_push(x_1621, x_1545);
x_1623 = lean_array_push(x_1622, x_1590);
x_1624 = lean_array_push(x_1623, x_1614);
x_1625 = lean_array_push(x_1624, x_1528);
x_1626 = lean_array_push(x_1625, x_1529);
x_1627 = lean_array_push(x_1626, x_1547);
x_1628 = lean_array_push(x_1627, x_1);
x_1629 = lean_array_push(x_1628, x_3);
x_1630 = l_Lean_mkAppN(x_1616, x_1629);
lean_dec(x_1629);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1630);
x_1631 = lean_infer_type(x_1630, x_5, x_6, x_7, x_8, x_1613);
if (lean_obj_tag(x_1631) == 0)
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; 
x_1632 = lean_ctor_get(x_1631, 0);
lean_inc(x_1632);
x_1633 = lean_ctor_get(x_1631, 1);
lean_inc(x_1633);
lean_dec(x_1631);
x_1634 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1632, x_5, x_6, x_7, x_8, x_1633);
x_1635 = lean_ctor_get(x_1634, 0);
lean_inc(x_1635);
x_1636 = lean_ctor_get(x_1634, 1);
lean_inc(x_1636);
if (lean_is_exclusive(x_1634)) {
 lean_ctor_release(x_1634, 0);
 lean_ctor_release(x_1634, 1);
 x_1637 = x_1634;
} else {
 lean_dec_ref(x_1634);
 x_1637 = lean_box(0);
}
x_1638 = l_Lean_Expr_headBeta(x_1635);
x_1639 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1638, x_5, x_6, x_7, x_8, x_1636);
x_1640 = lean_ctor_get(x_1639, 0);
lean_inc(x_1640);
if (lean_obj_tag(x_1640) == 0)
{
lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; 
lean_dec(x_1630);
x_1641 = lean_ctor_get(x_1639, 1);
lean_inc(x_1641);
if (lean_is_exclusive(x_1639)) {
 lean_ctor_release(x_1639, 0);
 lean_ctor_release(x_1639, 1);
 x_1642 = x_1639;
} else {
 lean_dec_ref(x_1639);
 x_1642 = lean_box(0);
}
x_1643 = l_Lean_indentExpr(x_1638);
x_1644 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
if (lean_is_scalar(x_1642)) {
 x_1645 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1645 = x_1642;
 lean_ctor_set_tag(x_1645, 7);
}
lean_ctor_set(x_1645, 0, x_1644);
lean_ctor_set(x_1645, 1, x_1643);
x_1646 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1637)) {
 x_1647 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1647 = x_1637;
 lean_ctor_set_tag(x_1647, 7);
}
lean_ctor_set(x_1647, 0, x_1645);
lean_ctor_set(x_1647, 1, x_1646);
x_1648 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1647, x_5, x_6, x_7, x_8, x_1641);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1649 = lean_ctor_get(x_1648, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1648, 1);
lean_inc(x_1650);
if (lean_is_exclusive(x_1648)) {
 lean_ctor_release(x_1648, 0);
 lean_ctor_release(x_1648, 1);
 x_1651 = x_1648;
} else {
 lean_dec_ref(x_1648);
 x_1651 = lean_box(0);
}
if (lean_is_scalar(x_1651)) {
 x_1652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1652 = x_1651;
}
lean_ctor_set(x_1652, 0, x_1649);
lean_ctor_set(x_1652, 1, x_1650);
return x_1652;
}
else
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; 
lean_dec(x_1640);
lean_dec(x_1637);
x_1653 = lean_ctor_get(x_1639, 1);
lean_inc(x_1653);
lean_dec(x_1639);
x_1654 = lean_box(0);
x_1655 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1630, x_1638, x_1654, x_5, x_6, x_7, x_8, x_1653);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1655;
}
}
else
{
lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; 
lean_dec(x_1630);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1656 = lean_ctor_get(x_1631, 0);
lean_inc(x_1656);
x_1657 = lean_ctor_get(x_1631, 1);
lean_inc(x_1657);
if (lean_is_exclusive(x_1631)) {
 lean_ctor_release(x_1631, 0);
 lean_ctor_release(x_1631, 1);
 x_1658 = x_1631;
} else {
 lean_dec_ref(x_1631);
 x_1658 = lean_box(0);
}
if (lean_is_scalar(x_1658)) {
 x_1659 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1659 = x_1658;
}
lean_ctor_set(x_1659, 0, x_1656);
lean_ctor_set(x_1659, 1, x_1657);
return x_1659;
}
}
else
{
lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; 
lean_dec(x_1612);
lean_dec(x_1599);
lean_dec(x_1590);
lean_dec(x_1562);
lean_dec(x_1559);
lean_dec(x_1556);
lean_dec(x_1547);
lean_dec(x_1545);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_3);
lean_dec(x_1);
x_1660 = lean_ctor_get(x_1611, 1);
lean_inc(x_1660);
lean_dec(x_1611);
x_1661 = l_Lean_indentExpr(x_1609);
x_1662 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
if (lean_is_scalar(x_1544)) {
 x_1663 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1663 = x_1544;
 lean_ctor_set_tag(x_1663, 7);
}
lean_ctor_set(x_1663, 0, x_1662);
lean_ctor_set(x_1663, 1, x_1661);
x_1664 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1534)) {
 x_1665 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1665 = x_1534;
 lean_ctor_set_tag(x_1665, 7);
}
lean_ctor_set(x_1665, 0, x_1663);
lean_ctor_set(x_1665, 1, x_1664);
x_1666 = l_Lean_useDiagnosticMsg;
if (lean_is_scalar(x_1530)) {
 x_1667 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1667 = x_1530;
 lean_ctor_set_tag(x_1667, 7);
}
lean_ctor_set(x_1667, 0, x_1665);
lean_ctor_set(x_1667, 1, x_1666);
x_1668 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1668, 0, x_1667);
lean_ctor_set(x_1668, 1, x_1664);
x_1669 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_1668, x_5, x_6, x_7, x_8, x_1660);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1669;
}
}
else
{
lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
lean_dec(x_1609);
lean_dec(x_1599);
lean_dec(x_1590);
lean_dec(x_1562);
lean_dec(x_1559);
lean_dec(x_1556);
lean_dec(x_1547);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1670 = lean_ctor_get(x_1611, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1611, 1);
lean_inc(x_1671);
if (lean_is_exclusive(x_1611)) {
 lean_ctor_release(x_1611, 0);
 lean_ctor_release(x_1611, 1);
 x_1672 = x_1611;
} else {
 lean_dec_ref(x_1611);
 x_1672 = lean_box(0);
}
if (lean_is_scalar(x_1672)) {
 x_1673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1673 = x_1672;
}
lean_ctor_set(x_1673, 0, x_1670);
lean_ctor_set(x_1673, 1, x_1671);
return x_1673;
}
}
else
{
lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; 
lean_dec(x_1568);
lean_dec(x_1565);
lean_dec(x_1562);
lean_dec(x_1559);
lean_dec(x_1556);
lean_dec(x_1553);
lean_dec(x_1550);
lean_dec(x_1548);
lean_dec(x_1547);
lean_dec(x_1546);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1541);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1674 = lean_ctor_get(x_1570, 0);
lean_inc(x_1674);
x_1675 = lean_ctor_get(x_1570, 1);
lean_inc(x_1675);
if (lean_is_exclusive(x_1570)) {
 lean_ctor_release(x_1570, 0);
 lean_ctor_release(x_1570, 1);
 x_1676 = x_1570;
} else {
 lean_dec_ref(x_1570);
 x_1676 = lean_box(0);
}
if (lean_is_scalar(x_1676)) {
 x_1677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1677 = x_1676;
}
lean_ctor_set(x_1677, 0, x_1674);
lean_ctor_set(x_1677, 1, x_1675);
return x_1677;
}
}
else
{
lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
lean_dec(x_1565);
lean_dec(x_1562);
lean_dec(x_1559);
lean_dec(x_1556);
lean_dec(x_1553);
lean_dec(x_1550);
lean_dec(x_1548);
lean_dec(x_1547);
lean_dec(x_1546);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1541);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1678 = lean_ctor_get(x_1567, 0);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_1567, 1);
lean_inc(x_1679);
if (lean_is_exclusive(x_1567)) {
 lean_ctor_release(x_1567, 0);
 lean_ctor_release(x_1567, 1);
 x_1680 = x_1567;
} else {
 lean_dec_ref(x_1567);
 x_1680 = lean_box(0);
}
if (lean_is_scalar(x_1680)) {
 x_1681 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1681 = x_1680;
}
lean_ctor_set(x_1681, 0, x_1678);
lean_ctor_set(x_1681, 1, x_1679);
return x_1681;
}
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
lean_dec(x_1562);
lean_dec(x_1559);
lean_dec(x_1556);
lean_dec(x_1553);
lean_dec(x_1550);
lean_dec(x_1548);
lean_dec(x_1547);
lean_dec(x_1546);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1541);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1682 = lean_ctor_get(x_1564, 0);
lean_inc(x_1682);
x_1683 = lean_ctor_get(x_1564, 1);
lean_inc(x_1683);
if (lean_is_exclusive(x_1564)) {
 lean_ctor_release(x_1564, 0);
 lean_ctor_release(x_1564, 1);
 x_1684 = x_1564;
} else {
 lean_dec_ref(x_1564);
 x_1684 = lean_box(0);
}
if (lean_is_scalar(x_1684)) {
 x_1685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1685 = x_1684;
}
lean_ctor_set(x_1685, 0, x_1682);
lean_ctor_set(x_1685, 1, x_1683);
return x_1685;
}
}
else
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
lean_dec(x_1559);
lean_dec(x_1556);
lean_dec(x_1553);
lean_dec(x_1550);
lean_dec(x_1548);
lean_dec(x_1547);
lean_dec(x_1546);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1541);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1686 = lean_ctor_get(x_1561, 0);
lean_inc(x_1686);
x_1687 = lean_ctor_get(x_1561, 1);
lean_inc(x_1687);
if (lean_is_exclusive(x_1561)) {
 lean_ctor_release(x_1561, 0);
 lean_ctor_release(x_1561, 1);
 x_1688 = x_1561;
} else {
 lean_dec_ref(x_1561);
 x_1688 = lean_box(0);
}
if (lean_is_scalar(x_1688)) {
 x_1689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1689 = x_1688;
}
lean_ctor_set(x_1689, 0, x_1686);
lean_ctor_set(x_1689, 1, x_1687);
return x_1689;
}
}
else
{
lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; 
lean_dec(x_1556);
lean_dec(x_1553);
lean_dec(x_1550);
lean_dec(x_1548);
lean_dec(x_1547);
lean_dec(x_1546);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1541);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1690 = lean_ctor_get(x_1558, 0);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1558, 1);
lean_inc(x_1691);
if (lean_is_exclusive(x_1558)) {
 lean_ctor_release(x_1558, 0);
 lean_ctor_release(x_1558, 1);
 x_1692 = x_1558;
} else {
 lean_dec_ref(x_1558);
 x_1692 = lean_box(0);
}
if (lean_is_scalar(x_1692)) {
 x_1693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1693 = x_1692;
}
lean_ctor_set(x_1693, 0, x_1690);
lean_ctor_set(x_1693, 1, x_1691);
return x_1693;
}
}
else
{
lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; 
lean_dec(x_1553);
lean_dec(x_1550);
lean_dec(x_1548);
lean_dec(x_1547);
lean_dec(x_1546);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1541);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1694 = lean_ctor_get(x_1555, 0);
lean_inc(x_1694);
x_1695 = lean_ctor_get(x_1555, 1);
lean_inc(x_1695);
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 lean_ctor_release(x_1555, 1);
 x_1696 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1696 = lean_box(0);
}
if (lean_is_scalar(x_1696)) {
 x_1697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1697 = x_1696;
}
lean_ctor_set(x_1697, 0, x_1694);
lean_ctor_set(x_1697, 1, x_1695);
return x_1697;
}
}
else
{
lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; 
lean_dec(x_1550);
lean_dec(x_1548);
lean_dec(x_1547);
lean_dec(x_1546);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1541);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1698 = lean_ctor_get(x_1552, 0);
lean_inc(x_1698);
x_1699 = lean_ctor_get(x_1552, 1);
lean_inc(x_1699);
if (lean_is_exclusive(x_1552)) {
 lean_ctor_release(x_1552, 0);
 lean_ctor_release(x_1552, 1);
 x_1700 = x_1552;
} else {
 lean_dec_ref(x_1552);
 x_1700 = lean_box(0);
}
if (lean_is_scalar(x_1700)) {
 x_1701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1701 = x_1700;
}
lean_ctor_set(x_1701, 0, x_1698);
lean_ctor_set(x_1701, 1, x_1699);
return x_1701;
}
}
else
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; 
lean_dec(x_1548);
lean_dec(x_1547);
lean_dec(x_1546);
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1541);
lean_dec(x_1534);
lean_dec(x_1530);
lean_dec(x_1529);
lean_dec(x_1528);
lean_dec(x_1527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1702 = lean_ctor_get(x_1549, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1549, 1);
lean_inc(x_1703);
if (lean_is_exclusive(x_1549)) {
 lean_ctor_release(x_1549, 0);
 lean_ctor_release(x_1549, 1);
 x_1704 = x_1549;
} else {
 lean_dec_ref(x_1549);
 x_1704 = lean_box(0);
}
if (lean_is_scalar(x_1704)) {
 x_1705 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1705 = x_1704;
}
lean_ctor_set(x_1705, 0, x_1702);
lean_ctor_set(x_1705, 1, x_1703);
return x_1705;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_mkCalcTrans(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_28 = lean_unbox(x_24);
lean_dec(x_24);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeAscription", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_2 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2;
x_3 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3;
x_4 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
switch (lean_obj_tag(x_12)) {
case 0:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_array_size(x_15);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1(x_2, x_17, x_18, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_21, 0, x_1);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_1, 2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_29);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_1);
lean_dec(x_14);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_40 = lean_array_size(x_39);
x_41 = 0;
x_42 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1(x_2, x_40, x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_48 = x_43;
} else {
 lean_dec_ref(x_43);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_12);
lean_ctor_set(x_49, 2, x_46);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_38);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
case 1:
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_12, 0);
lean_inc(x_56);
switch (lean_obj_tag(x_56)) {
case 0:
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_1, 0);
x_59 = lean_ctor_get(x_1, 2);
x_60 = lean_ctor_get(x_1, 1);
lean_dec(x_60);
x_61 = lean_array_size(x_59);
x_62 = 0;
x_63 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2(x_2, x_61, x_62, x_59, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_ctor_set(x_1, 2, x_67);
lean_ctor_set(x_65, 0, x_1);
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_65);
lean_ctor_set(x_1, 2, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_63, 0, x_70);
return x_63;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_63, 0);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_63);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_73);
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_free_object(x_1);
lean_dec(x_58);
lean_dec(x_12);
x_78 = !lean_is_exclusive(x_63);
if (x_78 == 0)
{
return x_63;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_63, 0);
x_80 = lean_ctor_get(x_63, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_63);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = lean_ctor_get(x_1, 2);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_1);
x_84 = lean_array_size(x_83);
x_85 = 0;
x_86 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2(x_2, x_84, x_85, x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_12);
lean_ctor_set(x_93, 2, x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_89;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_88);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_82);
lean_dec(x_12);
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_98 = x_86;
} else {
 lean_dec_ref(x_86);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
case 1:
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_56, 0);
lean_inc(x_100);
switch (lean_obj_tag(x_100)) {
case 0:
{
uint8_t x_101; 
lean_dec(x_56);
x_101 = !lean_is_exclusive(x_1);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_1, 0);
x_103 = lean_ctor_get(x_1, 2);
x_104 = lean_ctor_get(x_1, 1);
lean_dec(x_104);
x_105 = lean_array_size(x_103);
x_106 = 0;
x_107 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3(x_2, x_105, x_106, x_103, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_109, 0);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_109, 0, x_1);
return x_107;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_109, 0);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_109);
lean_ctor_set(x_1, 2, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_107, 0, x_114);
return x_107;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_107, 0);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_107);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_119 = x_115;
} else {
 lean_dec_ref(x_115);
 x_119 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_117);
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_116);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_free_object(x_1);
lean_dec(x_102);
lean_dec(x_12);
x_122 = !lean_is_exclusive(x_107);
if (x_122 == 0)
{
return x_107;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_107, 0);
x_124 = lean_ctor_get(x_107, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_107);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; size_t x_128; size_t x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_1, 0);
x_127 = lean_ctor_get(x_1, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_1);
x_128 = lean_array_size(x_127);
x_129 = 0;
x_130 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3(x_2, x_128, x_129, x_127, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_136 = x_131;
} else {
 lean_dec_ref(x_131);
 x_136 = lean_box(0);
}
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_126);
lean_ctor_set(x_137, 1, x_12);
lean_ctor_set(x_137, 2, x_134);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
if (lean_is_scalar(x_133)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_133;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_132);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_126);
lean_dec(x_12);
x_140 = lean_ctor_get(x_130, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_130, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_142 = x_130;
} else {
 lean_dec_ref(x_130);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
case 1:
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_100, 0);
lean_inc(x_144);
switch (lean_obj_tag(x_144)) {
case 0:
{
uint8_t x_145; 
lean_dec(x_100);
lean_dec(x_56);
x_145 = !lean_is_exclusive(x_1);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; size_t x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_1, 0);
x_147 = lean_ctor_get(x_1, 2);
x_148 = lean_ctor_get(x_1, 1);
lean_dec(x_148);
x_149 = lean_array_size(x_147);
x_150 = 0;
x_151 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4(x_2, x_149, x_150, x_147, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_151) == 0)
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
lean_ctor_set(x_1, 2, x_155);
lean_ctor_set(x_153, 0, x_1);
return x_151;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_153, 0);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_153);
lean_ctor_set(x_1, 2, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_151, 0, x_158);
return x_151;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_151, 0);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_151);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_163 = x_159;
} else {
 lean_dec_ref(x_159);
 x_163 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_160);
return x_165;
}
}
else
{
uint8_t x_166; 
lean_free_object(x_1);
lean_dec(x_146);
lean_dec(x_12);
x_166 = !lean_is_exclusive(x_151);
if (x_166 == 0)
{
return x_151;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_151, 0);
x_168 = lean_ctor_get(x_151, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_151);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; size_t x_172; size_t x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_1, 0);
x_171 = lean_ctor_get(x_1, 2);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_1);
x_172 = lean_array_size(x_171);
x_173 = 0;
x_174 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4(x_2, x_172, x_173, x_171, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_170);
lean_ctor_set(x_181, 1, x_12);
lean_ctor_set(x_181, 2, x_178);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
if (lean_is_scalar(x_177)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_177;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_176);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_170);
lean_dec(x_12);
x_184 = lean_ctor_get(x_174, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_174, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_186 = x_174;
} else {
 lean_dec_ref(x_174);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
case 1:
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_144, 0);
lean_inc(x_188);
switch (lean_obj_tag(x_188)) {
case 0:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_189 = lean_ctor_get(x_1, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_1, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_12, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_56, 1);
lean_inc(x_192);
lean_dec(x_56);
x_193 = lean_ctor_get(x_100, 1);
lean_inc(x_193);
lean_dec(x_100);
x_194 = lean_ctor_get(x_144, 1);
lean_inc(x_194);
lean_dec(x_144);
x_195 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_196 = lean_string_dec_eq(x_194, x_195);
lean_dec(x_194);
if (x_196 == 0)
{
uint8_t x_197; 
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
x_197 = !lean_is_exclusive(x_1);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; size_t x_201; size_t x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_1, 2);
lean_dec(x_198);
x_199 = lean_ctor_get(x_1, 1);
lean_dec(x_199);
x_200 = lean_ctor_get(x_1, 0);
lean_dec(x_200);
x_201 = lean_array_size(x_190);
x_202 = 0;
x_203 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5(x_2, x_201, x_202, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_203) == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_205, 0);
lean_ctor_set(x_1, 2, x_207);
lean_ctor_set(x_205, 0, x_1);
return x_203;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_205, 0);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_205);
lean_ctor_set(x_1, 2, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_1);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_203, 0, x_210);
return x_203;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_203, 0);
x_212 = lean_ctor_get(x_203, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_203);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_215 = x_211;
} else {
 lean_dec_ref(x_211);
 x_215 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_213);
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_1);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_212);
return x_217;
}
}
else
{
uint8_t x_218; 
lean_free_object(x_1);
lean_dec(x_189);
lean_dec(x_12);
x_218 = !lean_is_exclusive(x_203);
if (x_218 == 0)
{
return x_203;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_203, 0);
x_220 = lean_ctor_get(x_203, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_203);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
size_t x_222; size_t x_223; lean_object* x_224; 
lean_dec(x_1);
x_222 = lean_array_size(x_190);
x_223 = 0;
x_224 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5(x_2, x_222, x_223, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_225, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_225, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_230 = x_225;
} else {
 lean_dec_ref(x_225);
 x_230 = lean_box(0);
}
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_189);
lean_ctor_set(x_231, 1, x_12);
lean_ctor_set(x_231, 2, x_228);
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_229);
if (lean_is_scalar(x_227)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_227;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_226);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_189);
lean_dec(x_12);
x_234 = lean_ctor_get(x_224, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_224, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_236 = x_224;
} else {
 lean_dec_ref(x_224);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
else
{
lean_object* x_238; uint8_t x_239; 
lean_dec(x_12);
x_238 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2;
x_239 = lean_string_dec_eq(x_193, x_238);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_1);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; size_t x_248; size_t x_249; lean_object* x_250; 
x_241 = lean_ctor_get(x_1, 2);
lean_dec(x_241);
x_242 = lean_ctor_get(x_1, 1);
lean_dec(x_242);
x_243 = lean_ctor_get(x_1, 0);
lean_dec(x_243);
x_244 = l_Lean_Name_str___override(x_188, x_195);
x_245 = l_Lean_Name_str___override(x_244, x_193);
x_246 = l_Lean_Name_str___override(x_245, x_192);
x_247 = l_Lean_Name_str___override(x_246, x_191);
x_248 = lean_array_size(x_190);
x_249 = 0;
x_250 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6(x_2, x_248, x_249, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_250, 0);
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_252, 0);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_252, 0, x_1);
return x_250;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_252, 0);
x_256 = lean_ctor_get(x_252, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_252);
lean_ctor_set(x_1, 2, x_255);
lean_ctor_set(x_1, 1, x_247);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_1);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set(x_250, 0, x_257);
return x_250;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_258 = lean_ctor_get(x_250, 0);
x_259 = lean_ctor_get(x_250, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_250);
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_262 = x_258;
} else {
 lean_dec_ref(x_258);
 x_262 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_260);
lean_ctor_set(x_1, 1, x_247);
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_1);
lean_ctor_set(x_263, 1, x_261);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_259);
return x_264;
}
}
else
{
uint8_t x_265; 
lean_dec(x_247);
lean_free_object(x_1);
lean_dec(x_189);
x_265 = !lean_is_exclusive(x_250);
if (x_265 == 0)
{
return x_250;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_250, 0);
x_267 = lean_ctor_get(x_250, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_250);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; size_t x_273; size_t x_274; lean_object* x_275; 
lean_dec(x_1);
x_269 = l_Lean_Name_str___override(x_188, x_195);
x_270 = l_Lean_Name_str___override(x_269, x_193);
x_271 = l_Lean_Name_str___override(x_270, x_192);
x_272 = l_Lean_Name_str___override(x_271, x_191);
x_273 = lean_array_size(x_190);
x_274 = 0;
x_275 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6(x_2, x_273, x_274, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_276, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_281 = x_276;
} else {
 lean_dec_ref(x_276);
 x_281 = lean_box(0);
}
x_282 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_282, 0, x_189);
lean_ctor_set(x_282, 1, x_272);
lean_ctor_set(x_282, 2, x_279);
if (lean_is_scalar(x_281)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_281;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_280);
if (lean_is_scalar(x_278)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_278;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_277);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_272);
lean_dec(x_189);
x_285 = lean_ctor_get(x_275, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_275, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_287 = x_275;
} else {
 lean_dec_ref(x_275);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
else
{
lean_object* x_289; uint8_t x_290; 
lean_dec(x_193);
x_289 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3;
x_290 = lean_string_dec_eq(x_192, x_289);
if (x_290 == 0)
{
uint8_t x_291; 
x_291 = !lean_is_exclusive(x_1);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; size_t x_299; size_t x_300; lean_object* x_301; 
x_292 = lean_ctor_get(x_1, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_1, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_1, 0);
lean_dec(x_294);
x_295 = l_Lean_Name_str___override(x_188, x_195);
x_296 = l_Lean_Name_str___override(x_295, x_238);
x_297 = l_Lean_Name_str___override(x_296, x_192);
x_298 = l_Lean_Name_str___override(x_297, x_191);
x_299 = lean_array_size(x_190);
x_300 = 0;
x_301 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7(x_2, x_299, x_300, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_301) == 0)
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_303, 0);
lean_ctor_set(x_1, 2, x_305);
lean_ctor_set(x_1, 1, x_298);
lean_ctor_set(x_303, 0, x_1);
return x_301;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_303, 0);
x_307 = lean_ctor_get(x_303, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_303);
lean_ctor_set(x_1, 2, x_306);
lean_ctor_set(x_1, 1, x_298);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_1);
lean_ctor_set(x_308, 1, x_307);
lean_ctor_set(x_301, 0, x_308);
return x_301;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_309 = lean_ctor_get(x_301, 0);
x_310 = lean_ctor_get(x_301, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_301);
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_313 = x_309;
} else {
 lean_dec_ref(x_309);
 x_313 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_311);
lean_ctor_set(x_1, 1, x_298);
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_1);
lean_ctor_set(x_314, 1, x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_310);
return x_315;
}
}
else
{
uint8_t x_316; 
lean_dec(x_298);
lean_free_object(x_1);
lean_dec(x_189);
x_316 = !lean_is_exclusive(x_301);
if (x_316 == 0)
{
return x_301;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_301, 0);
x_318 = lean_ctor_get(x_301, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_301);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; size_t x_324; size_t x_325; lean_object* x_326; 
lean_dec(x_1);
x_320 = l_Lean_Name_str___override(x_188, x_195);
x_321 = l_Lean_Name_str___override(x_320, x_238);
x_322 = l_Lean_Name_str___override(x_321, x_192);
x_323 = l_Lean_Name_str___override(x_322, x_191);
x_324 = lean_array_size(x_190);
x_325 = 0;
x_326 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7(x_2, x_324, x_325, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_329 = x_326;
} else {
 lean_dec_ref(x_326);
 x_329 = lean_box(0);
}
x_330 = lean_ctor_get(x_327, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_327, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_332 = x_327;
} else {
 lean_dec_ref(x_327);
 x_332 = lean_box(0);
}
x_333 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_333, 0, x_189);
lean_ctor_set(x_333, 1, x_323);
lean_ctor_set(x_333, 2, x_330);
if (lean_is_scalar(x_332)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_332;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_331);
if (lean_is_scalar(x_329)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_329;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_328);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_323);
lean_dec(x_189);
x_336 = lean_ctor_get(x_326, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_326, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_338 = x_326;
} else {
 lean_dec_ref(x_326);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
}
else
{
lean_object* x_340; uint8_t x_341; 
lean_dec(x_192);
x_340 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__4;
x_341 = lean_string_dec_eq(x_191, x_340);
if (x_341 == 0)
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_1);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; size_t x_350; size_t x_351; lean_object* x_352; 
x_343 = lean_ctor_get(x_1, 2);
lean_dec(x_343);
x_344 = lean_ctor_get(x_1, 1);
lean_dec(x_344);
x_345 = lean_ctor_get(x_1, 0);
lean_dec(x_345);
x_346 = l_Lean_Name_str___override(x_188, x_195);
x_347 = l_Lean_Name_str___override(x_346, x_238);
x_348 = l_Lean_Name_str___override(x_347, x_289);
x_349 = l_Lean_Name_str___override(x_348, x_191);
x_350 = lean_array_size(x_190);
x_351 = 0;
x_352 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8(x_2, x_350, x_351, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_352) == 0)
{
uint8_t x_353; 
x_353 = !lean_is_exclusive(x_352);
if (x_353 == 0)
{
lean_object* x_354; uint8_t x_355; 
x_354 = lean_ctor_get(x_352, 0);
x_355 = !lean_is_exclusive(x_354);
if (x_355 == 0)
{
lean_object* x_356; 
x_356 = lean_ctor_get(x_354, 0);
lean_ctor_set(x_1, 2, x_356);
lean_ctor_set(x_1, 1, x_349);
lean_ctor_set(x_354, 0, x_1);
return x_352;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_354, 0);
x_358 = lean_ctor_get(x_354, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_354);
lean_ctor_set(x_1, 2, x_357);
lean_ctor_set(x_1, 1, x_349);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_1);
lean_ctor_set(x_359, 1, x_358);
lean_ctor_set(x_352, 0, x_359);
return x_352;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_360 = lean_ctor_get(x_352, 0);
x_361 = lean_ctor_get(x_352, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_352);
x_362 = lean_ctor_get(x_360, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_364 = x_360;
} else {
 lean_dec_ref(x_360);
 x_364 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_362);
lean_ctor_set(x_1, 1, x_349);
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_1);
lean_ctor_set(x_365, 1, x_363);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_361);
return x_366;
}
}
else
{
uint8_t x_367; 
lean_dec(x_349);
lean_free_object(x_1);
lean_dec(x_189);
x_367 = !lean_is_exclusive(x_352);
if (x_367 == 0)
{
return x_352;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_352, 0);
x_369 = lean_ctor_get(x_352, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_352);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; size_t x_375; size_t x_376; lean_object* x_377; 
lean_dec(x_1);
x_371 = l_Lean_Name_str___override(x_188, x_195);
x_372 = l_Lean_Name_str___override(x_371, x_238);
x_373 = l_Lean_Name_str___override(x_372, x_289);
x_374 = l_Lean_Name_str___override(x_373, x_191);
x_375 = lean_array_size(x_190);
x_376 = 0;
x_377 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8(x_2, x_375, x_376, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_380 = x_377;
} else {
 lean_dec_ref(x_377);
 x_380 = lean_box(0);
}
x_381 = lean_ctor_get(x_378, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_378, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_383 = x_378;
} else {
 lean_dec_ref(x_378);
 x_383 = lean_box(0);
}
x_384 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_384, 0, x_189);
lean_ctor_set(x_384, 1, x_374);
lean_ctor_set(x_384, 2, x_381);
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_382);
if (lean_is_scalar(x_380)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_380;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_379);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_374);
lean_dec(x_189);
x_387 = lean_ctor_get(x_377, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_389 = x_377;
} else {
 lean_dec_ref(x_377);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
}
else
{
lean_object* x_391; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_inc(x_10);
lean_inc(x_9);
x_391 = l_Lean_Elab_Term_exprToSyntax(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_ctor_get(x_9, 5);
lean_inc(x_394);
lean_dec(x_9);
x_395 = 0;
x_396 = l_Lean_SourceInfo_fromRef(x_394, x_395);
lean_dec(x_394);
x_397 = lean_st_ref_get(x_10, x_393);
lean_dec(x_10);
x_398 = !lean_is_exclusive(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_399 = lean_ctor_get(x_397, 0);
lean_dec(x_399);
x_400 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7;
lean_inc(x_396);
x_401 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_401, 0, x_396);
lean_ctor_set(x_401, 1, x_400);
x_402 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8;
lean_inc(x_396);
x_403 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_403, 0, x_396);
lean_ctor_set(x_403, 1, x_402);
x_404 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10;
lean_inc(x_396);
x_405 = l_Lean_Syntax_node1(x_396, x_404, x_392);
x_406 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11;
lean_inc(x_396);
x_407 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_407, 0, x_396);
lean_ctor_set(x_407, 1, x_406);
x_408 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6;
x_409 = l_Lean_Syntax_node5(x_396, x_408, x_401, x_1, x_403, x_405, x_407);
x_410 = lean_box(x_395);
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_397, 0, x_411);
return x_397;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_412 = lean_ctor_get(x_397, 1);
lean_inc(x_412);
lean_dec(x_397);
x_413 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7;
lean_inc(x_396);
x_414 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_414, 0, x_396);
lean_ctor_set(x_414, 1, x_413);
x_415 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8;
lean_inc(x_396);
x_416 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_416, 0, x_396);
lean_ctor_set(x_416, 1, x_415);
x_417 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10;
lean_inc(x_396);
x_418 = l_Lean_Syntax_node1(x_396, x_417, x_392);
x_419 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11;
lean_inc(x_396);
x_420 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_420, 0, x_396);
lean_ctor_set(x_420, 1, x_419);
x_421 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6;
x_422 = l_Lean_Syntax_node5(x_396, x_421, x_414, x_1, x_416, x_418, x_420);
x_423 = lean_box(x_395);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_412);
return x_425;
}
}
else
{
uint8_t x_426; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_426 = !lean_is_exclusive(x_391);
if (x_426 == 0)
{
return x_391;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_391, 0);
x_428 = lean_ctor_get(x_391, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_391);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_430; 
lean_dec(x_188);
lean_dec(x_144);
lean_dec(x_100);
lean_dec(x_56);
x_430 = !lean_is_exclusive(x_1);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; size_t x_434; size_t x_435; lean_object* x_436; 
x_431 = lean_ctor_get(x_1, 0);
x_432 = lean_ctor_get(x_1, 2);
x_433 = lean_ctor_get(x_1, 1);
lean_dec(x_433);
x_434 = lean_array_size(x_432);
x_435 = 0;
x_436 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9(x_2, x_434, x_435, x_432, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_436) == 0)
{
uint8_t x_437; 
x_437 = !lean_is_exclusive(x_436);
if (x_437 == 0)
{
lean_object* x_438; uint8_t x_439; 
x_438 = lean_ctor_get(x_436, 0);
x_439 = !lean_is_exclusive(x_438);
if (x_439 == 0)
{
lean_object* x_440; 
x_440 = lean_ctor_get(x_438, 0);
lean_ctor_set(x_1, 2, x_440);
lean_ctor_set(x_438, 0, x_1);
return x_436;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_438, 0);
x_442 = lean_ctor_get(x_438, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_438);
lean_ctor_set(x_1, 2, x_441);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_1);
lean_ctor_set(x_443, 1, x_442);
lean_ctor_set(x_436, 0, x_443);
return x_436;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_444 = lean_ctor_get(x_436, 0);
x_445 = lean_ctor_get(x_436, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_436);
x_446 = lean_ctor_get(x_444, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_444, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_448 = x_444;
} else {
 lean_dec_ref(x_444);
 x_448 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_446);
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_1);
lean_ctor_set(x_449, 1, x_447);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_445);
return x_450;
}
}
else
{
uint8_t x_451; 
lean_free_object(x_1);
lean_dec(x_431);
lean_dec(x_12);
x_451 = !lean_is_exclusive(x_436);
if (x_451 == 0)
{
return x_436;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_436, 0);
x_453 = lean_ctor_get(x_436, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_436);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; size_t x_457; size_t x_458; lean_object* x_459; 
x_455 = lean_ctor_get(x_1, 0);
x_456 = lean_ctor_get(x_1, 2);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_1);
x_457 = lean_array_size(x_456);
x_458 = 0;
x_459 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9(x_2, x_457, x_458, x_456, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_462 = x_459;
} else {
 lean_dec_ref(x_459);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_460, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_460, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_465 = x_460;
} else {
 lean_dec_ref(x_460);
 x_465 = lean_box(0);
}
x_466 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_466, 0, x_455);
lean_ctor_set(x_466, 1, x_12);
lean_ctor_set(x_466, 2, x_463);
if (lean_is_scalar(x_465)) {
 x_467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_467 = x_465;
}
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_464);
if (lean_is_scalar(x_462)) {
 x_468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_468 = x_462;
}
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_461);
return x_468;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_455);
lean_dec(x_12);
x_469 = lean_ctor_get(x_459, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_471 = x_459;
} else {
 lean_dec_ref(x_459);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
return x_472;
}
}
}
default: 
{
uint8_t x_473; 
lean_dec(x_188);
lean_dec(x_144);
lean_dec(x_100);
lean_dec(x_56);
x_473 = !lean_is_exclusive(x_1);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; size_t x_477; size_t x_478; lean_object* x_479; 
x_474 = lean_ctor_get(x_1, 0);
x_475 = lean_ctor_get(x_1, 2);
x_476 = lean_ctor_get(x_1, 1);
lean_dec(x_476);
x_477 = lean_array_size(x_475);
x_478 = 0;
x_479 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10(x_2, x_477, x_478, x_475, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_479) == 0)
{
uint8_t x_480; 
x_480 = !lean_is_exclusive(x_479);
if (x_480 == 0)
{
lean_object* x_481; uint8_t x_482; 
x_481 = lean_ctor_get(x_479, 0);
x_482 = !lean_is_exclusive(x_481);
if (x_482 == 0)
{
lean_object* x_483; 
x_483 = lean_ctor_get(x_481, 0);
lean_ctor_set(x_1, 2, x_483);
lean_ctor_set(x_481, 0, x_1);
return x_479;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_481, 0);
x_485 = lean_ctor_get(x_481, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_481);
lean_ctor_set(x_1, 2, x_484);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_1);
lean_ctor_set(x_486, 1, x_485);
lean_ctor_set(x_479, 0, x_486);
return x_479;
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_479, 0);
x_488 = lean_ctor_get(x_479, 1);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_479);
x_489 = lean_ctor_get(x_487, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_491 = x_487;
} else {
 lean_dec_ref(x_487);
 x_491 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_489);
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_1);
lean_ctor_set(x_492, 1, x_490);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_488);
return x_493;
}
}
else
{
uint8_t x_494; 
lean_free_object(x_1);
lean_dec(x_474);
lean_dec(x_12);
x_494 = !lean_is_exclusive(x_479);
if (x_494 == 0)
{
return x_479;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_479, 0);
x_496 = lean_ctor_get(x_479, 1);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_479);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set(x_497, 1, x_496);
return x_497;
}
}
}
else
{
lean_object* x_498; lean_object* x_499; size_t x_500; size_t x_501; lean_object* x_502; 
x_498 = lean_ctor_get(x_1, 0);
x_499 = lean_ctor_get(x_1, 2);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_1);
x_500 = lean_array_size(x_499);
x_501 = 0;
x_502 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10(x_2, x_500, x_501, x_499, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_505 = x_502;
} else {
 lean_dec_ref(x_502);
 x_505 = lean_box(0);
}
x_506 = lean_ctor_get(x_503, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_503, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_508 = x_503;
} else {
 lean_dec_ref(x_503);
 x_508 = lean_box(0);
}
x_509 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_509, 0, x_498);
lean_ctor_set(x_509, 1, x_12);
lean_ctor_set(x_509, 2, x_506);
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(0, 2, 0);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_507);
if (lean_is_scalar(x_505)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_505;
}
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_504);
return x_511;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_498);
lean_dec(x_12);
x_512 = lean_ctor_get(x_502, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_502, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_514 = x_502;
} else {
 lean_dec_ref(x_502);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
}
}
}
default: 
{
uint8_t x_516; 
lean_dec(x_144);
lean_dec(x_100);
lean_dec(x_56);
x_516 = !lean_is_exclusive(x_1);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; size_t x_520; size_t x_521; lean_object* x_522; 
x_517 = lean_ctor_get(x_1, 0);
x_518 = lean_ctor_get(x_1, 2);
x_519 = lean_ctor_get(x_1, 1);
lean_dec(x_519);
x_520 = lean_array_size(x_518);
x_521 = 0;
x_522 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11(x_2, x_520, x_521, x_518, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_522) == 0)
{
uint8_t x_523; 
x_523 = !lean_is_exclusive(x_522);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; 
x_524 = lean_ctor_get(x_522, 0);
x_525 = !lean_is_exclusive(x_524);
if (x_525 == 0)
{
lean_object* x_526; 
x_526 = lean_ctor_get(x_524, 0);
lean_ctor_set(x_1, 2, x_526);
lean_ctor_set(x_524, 0, x_1);
return x_522;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_524, 0);
x_528 = lean_ctor_get(x_524, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_524);
lean_ctor_set(x_1, 2, x_527);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_1);
lean_ctor_set(x_529, 1, x_528);
lean_ctor_set(x_522, 0, x_529);
return x_522;
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_530 = lean_ctor_get(x_522, 0);
x_531 = lean_ctor_get(x_522, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_522);
x_532 = lean_ctor_get(x_530, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_530, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_534 = x_530;
} else {
 lean_dec_ref(x_530);
 x_534 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_532);
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_1);
lean_ctor_set(x_535, 1, x_533);
x_536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_531);
return x_536;
}
}
else
{
uint8_t x_537; 
lean_free_object(x_1);
lean_dec(x_517);
lean_dec(x_12);
x_537 = !lean_is_exclusive(x_522);
if (x_537 == 0)
{
return x_522;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_522, 0);
x_539 = lean_ctor_get(x_522, 1);
lean_inc(x_539);
lean_inc(x_538);
lean_dec(x_522);
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
return x_540;
}
}
}
else
{
lean_object* x_541; lean_object* x_542; size_t x_543; size_t x_544; lean_object* x_545; 
x_541 = lean_ctor_get(x_1, 0);
x_542 = lean_ctor_get(x_1, 2);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_1);
x_543 = lean_array_size(x_542);
x_544 = 0;
x_545 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11(x_2, x_543, x_544, x_542, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_548 = x_545;
} else {
 lean_dec_ref(x_545);
 x_548 = lean_box(0);
}
x_549 = lean_ctor_get(x_546, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_546, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_551 = x_546;
} else {
 lean_dec_ref(x_546);
 x_551 = lean_box(0);
}
x_552 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_552, 0, x_541);
lean_ctor_set(x_552, 1, x_12);
lean_ctor_set(x_552, 2, x_549);
if (lean_is_scalar(x_551)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_551;
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_550);
if (lean_is_scalar(x_548)) {
 x_554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_554 = x_548;
}
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_547);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_541);
lean_dec(x_12);
x_555 = lean_ctor_get(x_545, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_545, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_557 = x_545;
} else {
 lean_dec_ref(x_545);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(1, 2, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_556);
return x_558;
}
}
}
}
}
default: 
{
uint8_t x_559; 
lean_dec(x_100);
lean_dec(x_56);
x_559 = !lean_is_exclusive(x_1);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; size_t x_563; size_t x_564; lean_object* x_565; 
x_560 = lean_ctor_get(x_1, 0);
x_561 = lean_ctor_get(x_1, 2);
x_562 = lean_ctor_get(x_1, 1);
lean_dec(x_562);
x_563 = lean_array_size(x_561);
x_564 = 0;
x_565 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12(x_2, x_563, x_564, x_561, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_565) == 0)
{
uint8_t x_566; 
x_566 = !lean_is_exclusive(x_565);
if (x_566 == 0)
{
lean_object* x_567; uint8_t x_568; 
x_567 = lean_ctor_get(x_565, 0);
x_568 = !lean_is_exclusive(x_567);
if (x_568 == 0)
{
lean_object* x_569; 
x_569 = lean_ctor_get(x_567, 0);
lean_ctor_set(x_1, 2, x_569);
lean_ctor_set(x_567, 0, x_1);
return x_565;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_567, 0);
x_571 = lean_ctor_get(x_567, 1);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_567);
lean_ctor_set(x_1, 2, x_570);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_1);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set(x_565, 0, x_572);
return x_565;
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_573 = lean_ctor_get(x_565, 0);
x_574 = lean_ctor_get(x_565, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_565);
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_573, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_577 = x_573;
} else {
 lean_dec_ref(x_573);
 x_577 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_575);
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_1);
lean_ctor_set(x_578, 1, x_576);
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_574);
return x_579;
}
}
else
{
uint8_t x_580; 
lean_free_object(x_1);
lean_dec(x_560);
lean_dec(x_12);
x_580 = !lean_is_exclusive(x_565);
if (x_580 == 0)
{
return x_565;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_565, 0);
x_582 = lean_ctor_get(x_565, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_565);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
else
{
lean_object* x_584; lean_object* x_585; size_t x_586; size_t x_587; lean_object* x_588; 
x_584 = lean_ctor_get(x_1, 0);
x_585 = lean_ctor_get(x_1, 2);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_1);
x_586 = lean_array_size(x_585);
x_587 = 0;
x_588 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12(x_2, x_586, x_587, x_585, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_591 = x_588;
} else {
 lean_dec_ref(x_588);
 x_591 = lean_box(0);
}
x_592 = lean_ctor_get(x_589, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_589, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_594 = x_589;
} else {
 lean_dec_ref(x_589);
 x_594 = lean_box(0);
}
x_595 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_595, 0, x_584);
lean_ctor_set(x_595, 1, x_12);
lean_ctor_set(x_595, 2, x_592);
if (lean_is_scalar(x_594)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_594;
}
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_593);
if (lean_is_scalar(x_591)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_591;
}
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_590);
return x_597;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_dec(x_584);
lean_dec(x_12);
x_598 = lean_ctor_get(x_588, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_588, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_600 = x_588;
} else {
 lean_dec_ref(x_588);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_598);
lean_ctor_set(x_601, 1, x_599);
return x_601;
}
}
}
}
}
default: 
{
uint8_t x_602; 
lean_dec(x_56);
x_602 = !lean_is_exclusive(x_1);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; size_t x_606; size_t x_607; lean_object* x_608; 
x_603 = lean_ctor_get(x_1, 0);
x_604 = lean_ctor_get(x_1, 2);
x_605 = lean_ctor_get(x_1, 1);
lean_dec(x_605);
x_606 = lean_array_size(x_604);
x_607 = 0;
x_608 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13(x_2, x_606, x_607, x_604, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_608) == 0)
{
uint8_t x_609; 
x_609 = !lean_is_exclusive(x_608);
if (x_609 == 0)
{
lean_object* x_610; uint8_t x_611; 
x_610 = lean_ctor_get(x_608, 0);
x_611 = !lean_is_exclusive(x_610);
if (x_611 == 0)
{
lean_object* x_612; 
x_612 = lean_ctor_get(x_610, 0);
lean_ctor_set(x_1, 2, x_612);
lean_ctor_set(x_610, 0, x_1);
return x_608;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_610, 0);
x_614 = lean_ctor_get(x_610, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_610);
lean_ctor_set(x_1, 2, x_613);
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_1);
lean_ctor_set(x_615, 1, x_614);
lean_ctor_set(x_608, 0, x_615);
return x_608;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_616 = lean_ctor_get(x_608, 0);
x_617 = lean_ctor_get(x_608, 1);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_608);
x_618 = lean_ctor_get(x_616, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_616, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_620 = x_616;
} else {
 lean_dec_ref(x_616);
 x_620 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_618);
if (lean_is_scalar(x_620)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_620;
}
lean_ctor_set(x_621, 0, x_1);
lean_ctor_set(x_621, 1, x_619);
x_622 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_617);
return x_622;
}
}
else
{
uint8_t x_623; 
lean_free_object(x_1);
lean_dec(x_603);
lean_dec(x_12);
x_623 = !lean_is_exclusive(x_608);
if (x_623 == 0)
{
return x_608;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_608, 0);
x_625 = lean_ctor_get(x_608, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_608);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set(x_626, 1, x_625);
return x_626;
}
}
}
else
{
lean_object* x_627; lean_object* x_628; size_t x_629; size_t x_630; lean_object* x_631; 
x_627 = lean_ctor_get(x_1, 0);
x_628 = lean_ctor_get(x_1, 2);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_1);
x_629 = lean_array_size(x_628);
x_630 = 0;
x_631 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13(x_2, x_629, x_630, x_628, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_634 = x_631;
} else {
 lean_dec_ref(x_631);
 x_634 = lean_box(0);
}
x_635 = lean_ctor_get(x_632, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_632, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_637 = x_632;
} else {
 lean_dec_ref(x_632);
 x_637 = lean_box(0);
}
x_638 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_638, 0, x_627);
lean_ctor_set(x_638, 1, x_12);
lean_ctor_set(x_638, 2, x_635);
if (lean_is_scalar(x_637)) {
 x_639 = lean_alloc_ctor(0, 2, 0);
} else {
 x_639 = x_637;
}
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_636);
if (lean_is_scalar(x_634)) {
 x_640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_640 = x_634;
}
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_633);
return x_640;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_627);
lean_dec(x_12);
x_641 = lean_ctor_get(x_631, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_631, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_643 = x_631;
} else {
 lean_dec_ref(x_631);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_641);
lean_ctor_set(x_644, 1, x_642);
return x_644;
}
}
}
}
}
default: 
{
uint8_t x_645; 
x_645 = !lean_is_exclusive(x_1);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; size_t x_649; size_t x_650; lean_object* x_651; 
x_646 = lean_ctor_get(x_1, 0);
x_647 = lean_ctor_get(x_1, 2);
x_648 = lean_ctor_get(x_1, 1);
lean_dec(x_648);
x_649 = lean_array_size(x_647);
x_650 = 0;
x_651 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14(x_2, x_649, x_650, x_647, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_651) == 0)
{
uint8_t x_652; 
x_652 = !lean_is_exclusive(x_651);
if (x_652 == 0)
{
lean_object* x_653; uint8_t x_654; 
x_653 = lean_ctor_get(x_651, 0);
x_654 = !lean_is_exclusive(x_653);
if (x_654 == 0)
{
lean_object* x_655; 
x_655 = lean_ctor_get(x_653, 0);
lean_ctor_set(x_1, 2, x_655);
lean_ctor_set(x_653, 0, x_1);
return x_651;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_653, 0);
x_657 = lean_ctor_get(x_653, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_653);
lean_ctor_set(x_1, 2, x_656);
x_658 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_658, 0, x_1);
lean_ctor_set(x_658, 1, x_657);
lean_ctor_set(x_651, 0, x_658);
return x_651;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_659 = lean_ctor_get(x_651, 0);
x_660 = lean_ctor_get(x_651, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_651);
x_661 = lean_ctor_get(x_659, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_659, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_663 = x_659;
} else {
 lean_dec_ref(x_659);
 x_663 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_661);
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_1);
lean_ctor_set(x_664, 1, x_662);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_660);
return x_665;
}
}
else
{
uint8_t x_666; 
lean_free_object(x_1);
lean_dec(x_646);
lean_dec(x_12);
x_666 = !lean_is_exclusive(x_651);
if (x_666 == 0)
{
return x_651;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_667 = lean_ctor_get(x_651, 0);
x_668 = lean_ctor_get(x_651, 1);
lean_inc(x_668);
lean_inc(x_667);
lean_dec(x_651);
x_669 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_668);
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; size_t x_672; size_t x_673; lean_object* x_674; 
x_670 = lean_ctor_get(x_1, 0);
x_671 = lean_ctor_get(x_1, 2);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_1);
x_672 = lean_array_size(x_671);
x_673 = 0;
x_674 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14(x_2, x_672, x_673, x_671, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_677 = x_674;
} else {
 lean_dec_ref(x_674);
 x_677 = lean_box(0);
}
x_678 = lean_ctor_get(x_675, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_675, 1);
lean_inc(x_679);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 x_680 = x_675;
} else {
 lean_dec_ref(x_675);
 x_680 = lean_box(0);
}
x_681 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_681, 0, x_670);
lean_ctor_set(x_681, 1, x_12);
lean_ctor_set(x_681, 2, x_678);
if (lean_is_scalar(x_680)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_680;
}
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_679);
if (lean_is_scalar(x_677)) {
 x_683 = lean_alloc_ctor(0, 2, 0);
} else {
 x_683 = x_677;
}
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_676);
return x_683;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_dec(x_670);
lean_dec(x_12);
x_684 = lean_ctor_get(x_674, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_674, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_686 = x_674;
} else {
 lean_dec_ref(x_674);
 x_686 = lean_box(0);
}
if (lean_is_scalar(x_686)) {
 x_687 = lean_alloc_ctor(1, 2, 0);
} else {
 x_687 = x_686;
}
lean_ctor_set(x_687, 0, x_684);
lean_ctor_set(x_687, 1, x_685);
return x_687;
}
}
}
}
}
else
{
uint8_t x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_688 = 0;
x_689 = lean_box(x_688);
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_1);
lean_ctor_set(x_690, 1, x_689);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_11);
return x_691;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_3 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_box(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1(x_2, x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_2, x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg), 1, 0);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("calcFirstStep", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_2 = l_Lean_Elab_Term_getCalcFirstStep___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("calcStep", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_2 = l_Lean_Elab_Term_getCalcFirstStep___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":=", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_=_", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_getCalcFirstStep___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_2 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2;
x_3 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3;
x_4 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rfl", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_getCalcFirstStep___closed__11;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_getCalcFirstStep___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_getCalcFirstStep___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcFirstStep___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_getCalcFirstStep___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcFirstStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_getCalcFirstStep___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_6, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 10);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_18);
x_19 = l_Lean_Syntax_matchesNull(x_18, x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_13);
x_20 = lean_unsigned_to_nat(2u);
lean_inc(x_18);
x_21 = l_Lean_Syntax_matchesNull(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg(x_8);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = l_Lean_Syntax_getArg(x_18, x_17);
lean_dec(x_18);
x_24 = 0;
x_25 = l_Lean_SourceInfo_fromRef(x_14, x_24);
lean_dec(x_14);
x_26 = lean_st_ref_get(x_7, x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lean_Elab_Term_getCalcFirstStep___closed__5;
lean_inc(x_25);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Term_getCalcFirstStep___closed__4;
x_32 = l_Lean_Syntax_node3(x_25, x_31, x_16, x_30, x_23);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l_Lean_Elab_Term_getCalcFirstStep___closed__5;
lean_inc(x_25);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Term_getCalcFirstStep___closed__4;
x_37 = l_Lean_Syntax_node3(x_25, x_36, x_16, x_35, x_23);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_18);
x_39 = 0;
x_40 = l_Lean_SourceInfo_fromRef(x_14, x_39);
lean_dec(x_14);
x_41 = lean_st_ref_get(x_7, x_8);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_environment_main_module(x_44);
x_46 = l_Lean_Elab_Term_getCalcFirstStep___closed__8;
lean_inc(x_40);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Term_getCalcFirstStep___closed__10;
lean_inc(x_40);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Term_getCalcFirstStep___closed__9;
lean_inc(x_40);
x_51 = l_Lean_Syntax_node1(x_40, x_50, x_49);
x_52 = l_Lean_Elab_Term_getCalcFirstStep___closed__7;
lean_inc(x_40);
x_53 = l_Lean_Syntax_node3(x_40, x_52, x_16, x_47, x_51);
x_54 = l_Lean_Elab_Term_getCalcFirstStep___closed__5;
lean_inc(x_40);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Elab_Term_getCalcFirstStep___closed__13;
x_57 = l_Lean_addMacroScope(x_45, x_56, x_13);
x_58 = l_Lean_Elab_Term_getCalcFirstStep___closed__12;
x_59 = l_Lean_Elab_Term_getCalcFirstStep___closed__15;
lean_inc(x_40);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_40);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_59);
x_61 = l_Lean_Elab_Term_getCalcFirstStep___closed__4;
x_62 = l_Lean_Syntax_node3(x_40, x_61, x_53, x_55, x_60);
lean_ctor_set(x_41, 0, x_62);
return x_41;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_environment_main_module(x_65);
x_67 = l_Lean_Elab_Term_getCalcFirstStep___closed__8;
lean_inc(x_40);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Elab_Term_getCalcFirstStep___closed__10;
lean_inc(x_40);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_40);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Elab_Term_getCalcFirstStep___closed__9;
lean_inc(x_40);
x_72 = l_Lean_Syntax_node1(x_40, x_71, x_70);
x_73 = l_Lean_Elab_Term_getCalcFirstStep___closed__7;
lean_inc(x_40);
x_74 = l_Lean_Syntax_node3(x_40, x_73, x_16, x_68, x_72);
x_75 = l_Lean_Elab_Term_getCalcFirstStep___closed__5;
lean_inc(x_40);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_40);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Term_getCalcFirstStep___closed__13;
x_78 = l_Lean_addMacroScope(x_66, x_77, x_13);
x_79 = l_Lean_Elab_Term_getCalcFirstStep___closed__12;
x_80 = l_Lean_Elab_Term_getCalcFirstStep___closed__15;
lean_inc(x_40);
x_81 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_81, 0, x_40);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_80);
x_82 = l_Lean_Elab_Term_getCalcFirstStep___closed__4;
x_83 = l_Lean_Syntax_node3(x_40, x_82, x_74, x_76, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_64);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcFirstStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_getCalcFirstStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcSteps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("calcSteps", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcSteps___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_2 = l_Lean_Elab_Term_getCalcSteps___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcSteps___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.getCalcSteps", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcSteps___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__1;
x_2 = l_Lean_Elab_Term_getCalcSteps___closed__3;
x_3 = lean_unsigned_to_nat(87u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Elab_Term_mkCalcTrans___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_getCalcSteps___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcSteps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_getCalcSteps___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Lean_Elab_Term_getCalcSteps___closed__4;
x_12 = l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Elab_Term_getCalcFirstStep___closed__2;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_1);
x_17 = l_Lean_Elab_Term_getCalcSteps___closed__4;
x_18 = l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = l_Lean_Syntax_getArgs(x_20);
lean_dec(x_20);
x_22 = l_Lean_Elab_Term_getCalcFirstStep(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Elab_Term_getCalcSteps___closed__5;
x_26 = lean_array_push(x_25, x_24);
x_27 = l_Array_append___rarg(x_26, x_21);
lean_dec(x_21);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l_Lean_Elab_Term_getCalcSteps___closed__5;
x_31 = lean_array_push(x_30, x_28);
x_32 = l_Array_append___rarg(x_31, x_21);
lean_dec(x_21);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_21);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_box(0);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_box(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 9);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_15);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_16);
lean_closure_set(x_20, 5, x_8);
lean_closure_set(x_20, 6, x_9);
lean_closure_set(x_20, 7, x_10);
lean_closure_set(x_20, 8, x_11);
lean_inc(x_13);
lean_inc(x_12);
x_21 = l_Lean_Core_withFreshMacroScope___rarg(x_20, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_1);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_44 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_8, x_9, x_10, x_11, x_12, x_13, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = !lean_is_exclusive(x_12);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_12, 5);
x_48 = l_Lean_replaceRef(x_4, x_47);
lean_dec(x_47);
lean_ctor_set(x_12, 5, x_48);
x_49 = l_Lean_Elab_Term_mkCalcTrans(x_42, x_43, x_39, x_1, x_10, x_11, x_12, x_13, x_45);
lean_dec(x_43);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
lean_ctor_set(x_6, 0, x_51);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set(x_38, 0, x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
lean_ctor_set(x_6, 0, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set(x_38, 0, x_56);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_38);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_38);
lean_free_object(x_6);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
x_65 = lean_ctor_get(x_12, 2);
x_66 = lean_ctor_get(x_12, 3);
x_67 = lean_ctor_get(x_12, 4);
x_68 = lean_ctor_get(x_12, 5);
x_69 = lean_ctor_get(x_12, 6);
x_70 = lean_ctor_get(x_12, 7);
x_71 = lean_ctor_get(x_12, 8);
x_72 = lean_ctor_get(x_12, 9);
x_73 = lean_ctor_get(x_12, 10);
x_74 = lean_ctor_get_uint8(x_12, sizeof(void*)*12);
x_75 = lean_ctor_get(x_12, 11);
x_76 = lean_ctor_get_uint8(x_12, sizeof(void*)*12 + 1);
lean_inc(x_75);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_77 = l_Lean_replaceRef(x_4, x_68);
lean_dec(x_68);
x_78 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_78, 0, x_63);
lean_ctor_set(x_78, 1, x_64);
lean_ctor_set(x_78, 2, x_65);
lean_ctor_set(x_78, 3, x_66);
lean_ctor_set(x_78, 4, x_67);
lean_ctor_set(x_78, 5, x_77);
lean_ctor_set(x_78, 6, x_69);
lean_ctor_set(x_78, 7, x_70);
lean_ctor_set(x_78, 8, x_71);
lean_ctor_set(x_78, 9, x_72);
lean_ctor_set(x_78, 10, x_73);
lean_ctor_set(x_78, 11, x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*12, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*12 + 1, x_76);
x_79 = l_Lean_Elab_Term_mkCalcTrans(x_42, x_43, x_39, x_1, x_10, x_11, x_78, x_13, x_45);
lean_dec(x_43);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
lean_ctor_set(x_6, 0, x_80);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_3);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set(x_38, 0, x_83);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_38);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_38);
lean_free_object(x_6);
lean_dec(x_3);
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_88 = x_79;
} else {
 lean_dec_ref(x_79);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_free_object(x_38);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_39);
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_44);
if (x_90 == 0)
{
return x_44;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_44, 0);
x_92 = lean_ctor_get(x_44, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_44);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_38, 0);
x_95 = lean_ctor_get(x_38, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_38);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_96 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_8, x_9, x_10, x_11, x_12, x_13, x_40);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_ctor_get(x_12, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_12, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_12, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_12, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_12, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_12, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_12, 6);
lean_inc(x_104);
x_105 = lean_ctor_get(x_12, 7);
lean_inc(x_105);
x_106 = lean_ctor_get(x_12, 8);
lean_inc(x_106);
x_107 = lean_ctor_get(x_12, 9);
lean_inc(x_107);
x_108 = lean_ctor_get(x_12, 10);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_12, sizeof(void*)*12);
x_110 = lean_ctor_get(x_12, 11);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_12, sizeof(void*)*12 + 1);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 lean_ctor_release(x_12, 6);
 lean_ctor_release(x_12, 7);
 lean_ctor_release(x_12, 8);
 lean_ctor_release(x_12, 9);
 lean_ctor_release(x_12, 10);
 lean_ctor_release(x_12, 11);
 x_112 = x_12;
} else {
 lean_dec_ref(x_12);
 x_112 = lean_box(0);
}
x_113 = l_Lean_replaceRef(x_4, x_103);
lean_dec(x_103);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 12, 2);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_98);
lean_ctor_set(x_114, 1, x_99);
lean_ctor_set(x_114, 2, x_100);
lean_ctor_set(x_114, 3, x_101);
lean_ctor_set(x_114, 4, x_102);
lean_ctor_set(x_114, 5, x_113);
lean_ctor_set(x_114, 6, x_104);
lean_ctor_set(x_114, 7, x_105);
lean_ctor_set(x_114, 8, x_106);
lean_ctor_set(x_114, 9, x_107);
lean_ctor_set(x_114, 10, x_108);
lean_ctor_set(x_114, 11, x_110);
lean_ctor_set_uint8(x_114, sizeof(void*)*12, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*12 + 1, x_111);
x_115 = l_Lean_Elab_Term_mkCalcTrans(x_94, x_95, x_39, x_1, x_10, x_11, x_114, x_13, x_97);
lean_dec(x_95);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
lean_ctor_set(x_6, 0, x_116);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_3);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_6);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
if (lean_is_scalar(x_118)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_118;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_free_object(x_6);
lean_dec(x_3);
x_123 = lean_ctor_get(x_115, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_125 = x_115;
} else {
 lean_dec_ref(x_115);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_39);
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_127 = lean_ctor_get(x_96, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_96, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_129 = x_96;
} else {
 lean_dec_ref(x_96);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_6, 0);
lean_inc(x_131);
lean_dec(x_6);
x_132 = lean_ctor_get(x_21, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_21, 1);
lean_inc(x_133);
lean_dec(x_21);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_136 = x_131;
} else {
 lean_dec_ref(x_131);
 x_136 = lean_box(0);
}
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_137 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_8, x_9, x_10, x_11, x_12, x_13, x_133);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_ctor_get(x_12, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_12, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_12, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_12, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_12, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_12, 5);
lean_inc(x_144);
x_145 = lean_ctor_get(x_12, 6);
lean_inc(x_145);
x_146 = lean_ctor_get(x_12, 7);
lean_inc(x_146);
x_147 = lean_ctor_get(x_12, 8);
lean_inc(x_147);
x_148 = lean_ctor_get(x_12, 9);
lean_inc(x_148);
x_149 = lean_ctor_get(x_12, 10);
lean_inc(x_149);
x_150 = lean_ctor_get_uint8(x_12, sizeof(void*)*12);
x_151 = lean_ctor_get(x_12, 11);
lean_inc(x_151);
x_152 = lean_ctor_get_uint8(x_12, sizeof(void*)*12 + 1);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 lean_ctor_release(x_12, 6);
 lean_ctor_release(x_12, 7);
 lean_ctor_release(x_12, 8);
 lean_ctor_release(x_12, 9);
 lean_ctor_release(x_12, 10);
 lean_ctor_release(x_12, 11);
 x_153 = x_12;
} else {
 lean_dec_ref(x_12);
 x_153 = lean_box(0);
}
x_154 = l_Lean_replaceRef(x_4, x_144);
lean_dec(x_144);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 12, 2);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_139);
lean_ctor_set(x_155, 1, x_140);
lean_ctor_set(x_155, 2, x_141);
lean_ctor_set(x_155, 3, x_142);
lean_ctor_set(x_155, 4, x_143);
lean_ctor_set(x_155, 5, x_154);
lean_ctor_set(x_155, 6, x_145);
lean_ctor_set(x_155, 7, x_146);
lean_ctor_set(x_155, 8, x_147);
lean_ctor_set(x_155, 9, x_148);
lean_ctor_set(x_155, 10, x_149);
lean_ctor_set(x_155, 11, x_151);
lean_ctor_set_uint8(x_155, sizeof(void*)*12, x_150);
lean_ctor_set_uint8(x_155, sizeof(void*)*12 + 1, x_152);
x_156 = l_Lean_Elab_Term_mkCalcTrans(x_134, x_135, x_132, x_1, x_10, x_11, x_155, x_13, x_138);
lean_dec(x_135);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_157);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_3);
if (lean_is_scalar(x_136)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_136;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
if (lean_is_scalar(x_159)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_159;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_158);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_136);
lean_dec(x_3);
x_165 = lean_ctor_get(x_156, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_156, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_167 = x_156;
} else {
 lean_dec_ref(x_156);
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
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_ctor_get(x_137, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_137, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_171 = x_137;
} else {
 lean_dec_ref(x_137);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_21);
if (x_173 == 0)
{
return x_21;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_21, 0);
x_175 = lean_ctor_get(x_21, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_21);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.elabCalcSteps", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(93u);
x_4 = lean_unsigned_to_nat(51u);
x_5 = l_Lean_Elab_Term_mkCalcTrans___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'calc' step, relation expected", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'calc' step, left-hand-side is", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nprevious right-hand-side is", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_24; 
x_14 = lean_array_uget(x_1, x_3);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
x_27 = l_Lean_Elab_Term_getCalcFirstStep___closed__4;
lean_inc(x_14);
x_28 = l_Lean_Syntax_isOfKind(x_14, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__1(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_4);
x_15 = x_32;
x_16 = x_31;
goto block_23;
}
else
{
uint8_t x_33; 
lean_free_object(x_4);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_4);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_getArg(x_14, x_37);
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_Syntax_getArg(x_14, x_39);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_inc(x_38);
x_41 = x_38;
x_42 = x_11;
goto block_347;
}
else
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_25, 0);
lean_inc(x_348);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_349 = lean_infer_type(x_348, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_352 = l_Lean_Elab_Term_annotateFirstHoleWithType(x_38, x_350, x_5, x_6, x_7, x_8, x_9, x_10, x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_41 = x_353;
x_42 = x_354;
goto block_347;
}
else
{
uint8_t x_355; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_355 = !lean_is_exclusive(x_352);
if (x_355 == 0)
{
return x_352;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_352, 0);
x_357 = lean_ctor_get(x_352, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_352);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
else
{
uint8_t x_359; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_359 = !lean_is_exclusive(x_349);
if (x_359 == 0)
{
return x_349;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_349, 0);
x_361 = lean_ctor_get(x_349, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_349);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
block_347:
{
lean_object* x_43; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Lean_Elab_Term_elabType(x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Term_getCalcRelation_x3f(x_44, x_7, x_8, x_9, x_10, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = l_Lean_indentExpr(x_44);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__4;
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_51);
lean_ctor_set(x_46, 0, x_52);
x_53 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_38, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_38);
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
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_dec(x_46);
x_61 = l_Lean_indentExpr(x_44);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__4;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_38, x_65, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_38);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
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
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
lean_dec(x_47);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 1);
x_74 = lean_ctor_get(x_71, 0);
lean_dec(x_74);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_71);
x_75 = lean_ctor_get(x_46, 1);
lean_inc(x_75);
lean_dec(x_46);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_78 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_44, x_40, x_76, x_38, x_25, x_26, x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_75);
lean_dec(x_38);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_15 = x_79;
x_16 = x_80;
goto block_23;
}
else
{
uint8_t x_81; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_46);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_46, 1);
x_87 = lean_ctor_get(x_46, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_73);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_73, 0);
x_90 = lean_ctor_get(x_73, 1);
x_91 = lean_ctor_get(x_25, 0);
lean_inc(x_91);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_91);
lean_inc(x_89);
x_92 = l_Lean_Meta_isExprDefEqGuarded(x_89, x_91, x_7, x_8, x_9, x_10, x_86);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_90);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_89);
x_96 = lean_infer_type(x_89, x_7, x_8, x_9, x_10, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_91);
x_99 = lean_infer_type(x_91, x_7, x_8, x_9, x_10, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_MessageData_ofExpr(x_89);
x_103 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_102);
lean_ctor_set(x_73, 0, x_103);
x_104 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8;
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_104);
lean_ctor_set(x_71, 0, x_73);
x_105 = l_Lean_MessageData_ofExpr(x_97);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_105);
lean_ctor_set(x_46, 0, x_71);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_46);
lean_ctor_set(x_106, 1, x_103);
x_107 = l_Lean_indentD(x_106);
x_108 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_MessageData_ofExpr(x_91);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_103);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_104);
x_115 = l_Lean_MessageData_ofExpr(x_100);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_103);
x_118 = l_Lean_indentD(x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_111);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_103);
x_121 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_38, x_120, x_5, x_6, x_7, x_8, x_9, x_10, x_101);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_38);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_dec(x_97);
lean_dec(x_91);
lean_free_object(x_73);
lean_dec(x_89);
lean_free_object(x_46);
lean_free_object(x_71);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = !lean_is_exclusive(x_99);
if (x_126 == 0)
{
return x_99;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_99, 0);
x_128 = lean_ctor_get(x_99, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_99);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_91);
lean_free_object(x_73);
lean_dec(x_89);
lean_free_object(x_46);
lean_free_object(x_71);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_130 = !lean_is_exclusive(x_96);
if (x_130 == 0)
{
return x_96;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_96, 0);
x_132 = lean_ctor_get(x_96, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_96);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_91);
lean_free_object(x_73);
lean_dec(x_89);
lean_free_object(x_46);
lean_free_object(x_71);
x_134 = lean_ctor_get(x_92, 1);
lean_inc(x_134);
lean_dec(x_92);
x_135 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_136 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_44, x_40, x_90, x_38, x_25, x_26, x_135, x_5, x_6, x_7, x_8, x_9, x_10, x_134);
lean_dec(x_25);
lean_dec(x_38);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_15 = x_137;
x_16 = x_138;
goto block_23;
}
else
{
uint8_t x_139; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_139 = !lean_is_exclusive(x_136);
if (x_139 == 0)
{
return x_136;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_136, 0);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_136);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_91);
lean_free_object(x_73);
lean_dec(x_90);
lean_dec(x_89);
lean_free_object(x_46);
lean_free_object(x_71);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_143 = !lean_is_exclusive(x_92);
if (x_143 == 0)
{
return x_92;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_92, 0);
x_145 = lean_ctor_get(x_92, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_92);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_73, 0);
x_148 = lean_ctor_get(x_73, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_73);
x_149 = lean_ctor_get(x_25, 0);
lean_inc(x_149);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_149);
lean_inc(x_147);
x_150 = l_Lean_Meta_isExprDefEqGuarded(x_147, x_149, x_7, x_8, x_9, x_10, x_86);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_148);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_147);
x_154 = lean_infer_type(x_147, x_7, x_8, x_9, x_10, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_149);
x_157 = lean_infer_type(x_149, x_7, x_8, x_9, x_10, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_MessageData_ofExpr(x_147);
x_161 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8;
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_163);
lean_ctor_set(x_71, 0, x_162);
x_164 = l_Lean_MessageData_ofExpr(x_155);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_164);
lean_ctor_set(x_46, 0, x_71);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_46);
lean_ctor_set(x_165, 1, x_161);
x_166 = l_Lean_indentD(x_165);
x_167 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6;
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10;
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_MessageData_ofExpr(x_149);
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_161);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_163);
x_174 = l_Lean_MessageData_ofExpr(x_158);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_161);
x_177 = l_Lean_indentD(x_176);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_170);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_161);
x_180 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_38, x_179, x_5, x_6, x_7, x_8, x_9, x_10, x_159);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_38);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_155);
lean_dec(x_149);
lean_dec(x_147);
lean_free_object(x_46);
lean_free_object(x_71);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_185 = lean_ctor_get(x_157, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_157, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_187 = x_157;
} else {
 lean_dec_ref(x_157);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_149);
lean_dec(x_147);
lean_free_object(x_46);
lean_free_object(x_71);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_189 = lean_ctor_get(x_154, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_154, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_191 = x_154;
} else {
 lean_dec_ref(x_154);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_149);
lean_dec(x_147);
lean_free_object(x_46);
lean_free_object(x_71);
x_193 = lean_ctor_get(x_150, 1);
lean_inc(x_193);
lean_dec(x_150);
x_194 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_195 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_44, x_40, x_148, x_38, x_25, x_26, x_194, x_5, x_6, x_7, x_8, x_9, x_10, x_193);
lean_dec(x_25);
lean_dec(x_38);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_15 = x_196;
x_16 = x_197;
goto block_23;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_200 = x_195;
} else {
 lean_dec_ref(x_195);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_free_object(x_46);
lean_free_object(x_71);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_202 = lean_ctor_get(x_150, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_150, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_204 = x_150;
} else {
 lean_dec_ref(x_150);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_206 = lean_ctor_get(x_46, 1);
lean_inc(x_206);
lean_dec(x_46);
x_207 = lean_ctor_get(x_73, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_73, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_209 = x_73;
} else {
 lean_dec_ref(x_73);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_25, 0);
lean_inc(x_210);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_210);
lean_inc(x_207);
x_211 = l_Lean_Meta_isExprDefEqGuarded(x_207, x_210, x_7, x_8, x_9, x_10, x_206);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_unbox(x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_208);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_207);
x_215 = lean_infer_type(x_207, x_7, x_8, x_9, x_10, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_210);
x_218 = lean_infer_type(x_210, x_7, x_8, x_9, x_10, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = l_Lean_MessageData_ofExpr(x_207);
x_222 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_209)) {
 x_223 = lean_alloc_ctor(7, 2, 0);
} else {
 x_223 = x_209;
 lean_ctor_set_tag(x_223, 7);
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8;
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_224);
lean_ctor_set(x_71, 0, x_223);
x_225 = l_Lean_MessageData_ofExpr(x_216);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_71);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_222);
x_228 = l_Lean_indentD(x_227);
x_229 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6;
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10;
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_MessageData_ofExpr(x_210);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_222);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_224);
x_236 = l_Lean_MessageData_ofExpr(x_219);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_222);
x_239 = l_Lean_indentD(x_238);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_232);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_222);
x_242 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_38, x_241, x_5, x_6, x_7, x_8, x_9, x_10, x_220);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_38);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_216);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_free_object(x_71);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_247 = lean_ctor_get(x_218, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_218, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_249 = x_218;
} else {
 lean_dec_ref(x_218);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_free_object(x_71);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_251 = lean_ctor_get(x_215, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_215, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_253 = x_215;
} else {
 lean_dec_ref(x_215);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_free_object(x_71);
x_255 = lean_ctor_get(x_211, 1);
lean_inc(x_255);
lean_dec(x_211);
x_256 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_257 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_44, x_40, x_208, x_38, x_25, x_26, x_256, x_5, x_6, x_7, x_8, x_9, x_10, x_255);
lean_dec(x_25);
lean_dec(x_38);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_15 = x_258;
x_16 = x_259;
goto block_23;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_260 = lean_ctor_get(x_257, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_262 = x_257;
} else {
 lean_dec_ref(x_257);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_free_object(x_71);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_264 = lean_ctor_get(x_211, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_211, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_266 = x_211;
} else {
 lean_dec_ref(x_211);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
}
else
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_71, 1);
lean_inc(x_268);
lean_dec(x_71);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_46, 1);
lean_inc(x_269);
lean_dec(x_46);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_272 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_44, x_40, x_270, x_38, x_25, x_26, x_271, x_5, x_6, x_7, x_8, x_9, x_10, x_269);
lean_dec(x_38);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_15 = x_273;
x_16 = x_274;
goto block_23;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_277 = x_272;
} else {
 lean_dec_ref(x_272);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_279 = lean_ctor_get(x_46, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_280 = x_46;
} else {
 lean_dec_ref(x_46);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_268, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_268, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_283 = x_268;
} else {
 lean_dec_ref(x_268);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_25, 0);
lean_inc(x_284);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_284);
lean_inc(x_281);
x_285 = l_Lean_Meta_isExprDefEqGuarded(x_281, x_284, x_7, x_8, x_9, x_10, x_279);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_unbox(x_286);
lean_dec(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_282);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
lean_dec(x_285);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_281);
x_289 = lean_infer_type(x_281, x_7, x_8, x_9, x_10, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_284);
x_292 = lean_infer_type(x_284, x_7, x_8, x_9, x_10, x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = l_Lean_MessageData_ofExpr(x_281);
x_296 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_283)) {
 x_297 = lean_alloc_ctor(7, 2, 0);
} else {
 x_297 = x_283;
 lean_ctor_set_tag(x_297, 7);
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_295);
x_298 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8;
x_299 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = l_Lean_MessageData_ofExpr(x_290);
if (lean_is_scalar(x_280)) {
 x_301 = lean_alloc_ctor(7, 2, 0);
} else {
 x_301 = x_280;
 lean_ctor_set_tag(x_301, 7);
}
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_296);
x_303 = l_Lean_indentD(x_302);
x_304 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6;
x_305 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
x_306 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10;
x_307 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = l_Lean_MessageData_ofExpr(x_284);
x_309 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_309, 0, x_296);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_298);
x_311 = l_Lean_MessageData_ofExpr(x_293);
x_312 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_296);
x_314 = l_Lean_indentD(x_313);
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_307);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_296);
x_317 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_38, x_316, x_5, x_6, x_7, x_8, x_9, x_10, x_294);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_38);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_320 = x_317;
} else {
 lean_dec_ref(x_317);
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
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_290);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_322 = lean_ctor_get(x_292, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_292, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_324 = x_292;
} else {
 lean_dec_ref(x_292);
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
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_326 = lean_ctor_get(x_289, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_289, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_328 = x_289;
} else {
 lean_dec_ref(x_289);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_280);
x_330 = lean_ctor_get(x_285, 1);
lean_inc(x_330);
lean_dec(x_285);
x_331 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_332 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_44, x_40, x_282, x_38, x_25, x_26, x_331, x_5, x_6, x_7, x_8, x_9, x_10, x_330);
lean_dec(x_25);
lean_dec(x_38);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_15 = x_333;
x_16 = x_334;
goto block_23;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_335 = lean_ctor_get(x_332, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_332, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_337 = x_332;
} else {
 lean_dec_ref(x_332);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_339 = lean_ctor_get(x_285, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_285, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_341 = x_285;
} else {
 lean_dec_ref(x_285);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
}
}
}
else
{
uint8_t x_343; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_343 = !lean_is_exclusive(x_43);
if (x_343 == 0)
{
return x_43;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_43, 0);
x_345 = lean_ctor_get(x_43, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_43);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_363 = lean_ctor_get(x_4, 0);
x_364 = lean_ctor_get(x_4, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_4);
x_365 = l_Lean_Elab_Term_getCalcFirstStep___closed__4;
lean_inc(x_14);
x_366 = l_Lean_Syntax_isOfKind(x_14, x_365);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_14);
x_367 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_368 = l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__1(x_367, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_363);
lean_ctor_set(x_370, 1, x_364);
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_370);
x_15 = x_371;
x_16 = x_369;
goto block_23;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_372 = lean_ctor_get(x_368, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_368, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_374 = x_368;
} else {
 lean_dec_ref(x_368);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_unsigned_to_nat(0u);
x_377 = l_Lean_Syntax_getArg(x_14, x_376);
x_378 = lean_unsigned_to_nat(2u);
x_379 = l_Lean_Syntax_getArg(x_14, x_378);
lean_dec(x_14);
if (lean_obj_tag(x_363) == 0)
{
lean_inc(x_377);
x_380 = x_377;
x_381 = x_11;
goto block_480;
}
else
{
lean_object* x_481; lean_object* x_482; 
x_481 = lean_ctor_get(x_363, 0);
lean_inc(x_481);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_482 = lean_infer_type(x_481, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_377);
x_485 = l_Lean_Elab_Term_annotateFirstHoleWithType(x_377, x_483, x_5, x_6, x_7, x_8, x_9, x_10, x_484);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
x_380 = x_486;
x_381 = x_487;
goto block_480;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_488 = lean_ctor_get(x_485, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_485, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_490 = x_485;
} else {
 lean_dec_ref(x_485);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_489);
return x_491;
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_492 = lean_ctor_get(x_482, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_482, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_494 = x_482;
} else {
 lean_dec_ref(x_482);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_492);
lean_ctor_set(x_495, 1, x_493);
return x_495;
}
}
block_480:
{
lean_object* x_382; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_382 = l_Lean_Elab_Term_elabType(x_380, x_5, x_6, x_7, x_8, x_9, x_10, x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = l_Lean_Elab_Term_getCalcRelation_x3f(x_383, x_7, x_8, x_9, x_10, x_384);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_379);
lean_dec(x_364);
lean_dec(x_363);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_388 = x_385;
} else {
 lean_dec_ref(x_385);
 x_388 = lean_box(0);
}
x_389 = l_Lean_indentExpr(x_383);
x_390 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__4;
if (lean_is_scalar(x_388)) {
 x_391 = lean_alloc_ctor(7, 2, 0);
} else {
 x_391 = x_388;
 lean_ctor_set_tag(x_391, 7);
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_389);
x_392 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
x_393 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_377, x_393, x_5, x_6, x_7, x_8, x_9, x_10, x_387);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_377);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_397 = x_394;
} else {
 lean_dec_ref(x_394);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_386, 0);
lean_inc(x_399);
lean_dec(x_386);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_401 = x_399;
} else {
 lean_dec_ref(x_399);
 x_401 = lean_box(0);
}
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_401);
x_402 = lean_ctor_get(x_385, 1);
lean_inc(x_402);
lean_dec(x_385);
x_403 = lean_ctor_get(x_400, 1);
lean_inc(x_403);
lean_dec(x_400);
x_404 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_405 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_383, x_379, x_403, x_377, x_363, x_364, x_404, x_5, x_6, x_7, x_8, x_9, x_10, x_402);
lean_dec(x_377);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_15 = x_406;
x_16 = x_407;
goto block_23;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_410 = x_405;
} else {
 lean_dec_ref(x_405);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_412 = lean_ctor_get(x_385, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_413 = x_385;
} else {
 lean_dec_ref(x_385);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_400, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_400, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_416 = x_400;
} else {
 lean_dec_ref(x_400);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_363, 0);
lean_inc(x_417);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_417);
lean_inc(x_414);
x_418 = l_Lean_Meta_isExprDefEqGuarded(x_414, x_417, x_7, x_8, x_9, x_10, x_412);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; uint8_t x_420; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_unbox(x_419);
lean_dec(x_419);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; 
lean_dec(x_415);
lean_dec(x_383);
lean_dec(x_379);
lean_dec(x_364);
lean_dec(x_363);
x_421 = lean_ctor_get(x_418, 1);
lean_inc(x_421);
lean_dec(x_418);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_414);
x_422 = lean_infer_type(x_414, x_7, x_8, x_9, x_10, x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_417);
x_425 = lean_infer_type(x_417, x_7, x_8, x_9, x_10, x_424);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = l_Lean_MessageData_ofExpr(x_414);
x_429 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_416)) {
 x_430 = lean_alloc_ctor(7, 2, 0);
} else {
 x_430 = x_416;
 lean_ctor_set_tag(x_430, 7);
}
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8;
if (lean_is_scalar(x_401)) {
 x_432 = lean_alloc_ctor(7, 2, 0);
} else {
 x_432 = x_401;
 lean_ctor_set_tag(x_432, 7);
}
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
x_433 = l_Lean_MessageData_ofExpr(x_423);
if (lean_is_scalar(x_413)) {
 x_434 = lean_alloc_ctor(7, 2, 0);
} else {
 x_434 = x_413;
 lean_ctor_set_tag(x_434, 7);
}
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
x_435 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_429);
x_436 = l_Lean_indentD(x_435);
x_437 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6;
x_438 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_436);
x_439 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10;
x_440 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
x_441 = l_Lean_MessageData_ofExpr(x_417);
x_442 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_442, 0, x_429);
lean_ctor_set(x_442, 1, x_441);
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_431);
x_444 = l_Lean_MessageData_ofExpr(x_426);
x_445 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_429);
x_447 = l_Lean_indentD(x_446);
x_448 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_448, 0, x_440);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_429);
x_450 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_377, x_449, x_5, x_6, x_7, x_8, x_9, x_10, x_427);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_377);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_453 = x_450;
} else {
 lean_dec_ref(x_450);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_423);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_401);
lean_dec(x_377);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_455 = lean_ctor_get(x_425, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_425, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_457 = x_425;
} else {
 lean_dec_ref(x_425);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_455);
lean_ctor_set(x_458, 1, x_456);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_401);
lean_dec(x_377);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_459 = lean_ctor_get(x_422, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_422, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_461 = x_422;
} else {
 lean_dec_ref(x_422);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_460);
return x_462;
}
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_401);
x_463 = lean_ctor_get(x_418, 1);
lean_inc(x_463);
lean_dec(x_418);
x_464 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_465 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_383, x_379, x_415, x_377, x_363, x_364, x_464, x_5, x_6, x_7, x_8, x_9, x_10, x_463);
lean_dec(x_363);
lean_dec(x_377);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_15 = x_466;
x_16 = x_467;
goto block_23;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_468 = lean_ctor_get(x_465, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_465, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_470 = x_465;
} else {
 lean_dec_ref(x_465);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
return x_471;
}
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_401);
lean_dec(x_383);
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_472 = lean_ctor_get(x_418, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_418, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_474 = x_418;
} else {
 lean_dec_ref(x_418);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_472);
lean_ctor_set(x_475, 1, x_473);
return x_475;
}
}
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_476 = lean_ctor_get(x_382, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_382, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_478 = x_382;
} else {
 lean_dec_ref(x_382);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_477);
return x_479;
}
}
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_4 = x_19;
x_11 = x_16;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedExpr;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_elabCalcSteps___closed__2;
x_2 = l_Lean_Elab_Term_elabCalcSteps___closed__3;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Elab_Term_elabCalcSteps___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_getCalcSteps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_size(x_10);
x_13 = 0;
x_14 = l_Lean_Elab_Term_elabCalcSteps___closed__1;
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2(x_10, x_12, x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = l_Lean_Elab_Term_elabCalcSteps___closed__5;
x_21 = l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_Elab_Term_elabCalcSteps___closed__5;
x_25 = l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_15, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_elabCalcSteps(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Term_ensureHasType(x_2, x_13, x_17, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCalc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("calc", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabCalc", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__3;
x_3 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_termElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__5;
x_5 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__7;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elaborator for the `calc` term mode variant. ", 45, 45);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1___closed__1;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(116u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(121u);
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(15u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(116u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(116u);
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(12u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Elab_App(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Calc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_App(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__1 = _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__1);
l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__2 = _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__2);
l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__3 = _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__3);
l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4 = _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4);
l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1___closed__1 = _init_l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1___closed__1);
l_Lean_Elab_Term_mkCalcTrans___closed__1 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__1);
l_Lean_Elab_Term_mkCalcTrans___closed__2 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__2);
l_Lean_Elab_Term_mkCalcTrans___closed__3 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__3);
l_Lean_Elab_Term_mkCalcTrans___closed__4 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__4);
l_Lean_Elab_Term_mkCalcTrans___closed__5 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__5);
l_Lean_Elab_Term_mkCalcTrans___closed__6 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__6);
l_Lean_Elab_Term_mkCalcTrans___closed__7 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__7);
l_Lean_Elab_Term_mkCalcTrans___closed__8 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__8);
l_Lean_Elab_Term_mkCalcTrans___closed__9 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__9);
l_Lean_Elab_Term_mkCalcTrans___closed__10 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__10);
l_Lean_Elab_Term_mkCalcTrans___closed__11 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__11);
l_Lean_Elab_Term_mkCalcTrans___closed__12 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__12);
l_Lean_Elab_Term_mkCalcTrans___closed__13 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__13);
l_Lean_Elab_Term_mkCalcTrans___closed__14 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__14);
l_Lean_Elab_Term_mkCalcTrans___closed__15 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__15);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__4 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__4);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__5 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__5);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__9 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__9);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10);
l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11 = _init_l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getCalcFirstStep___spec__1___rarg___closed__2);
l_Lean_Elab_Term_getCalcFirstStep___closed__1 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__1);
l_Lean_Elab_Term_getCalcFirstStep___closed__2 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__2);
l_Lean_Elab_Term_getCalcFirstStep___closed__3 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__3);
l_Lean_Elab_Term_getCalcFirstStep___closed__4 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__4);
l_Lean_Elab_Term_getCalcFirstStep___closed__5 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__5);
l_Lean_Elab_Term_getCalcFirstStep___closed__6 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__6);
l_Lean_Elab_Term_getCalcFirstStep___closed__7 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__7);
l_Lean_Elab_Term_getCalcFirstStep___closed__8 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__8);
l_Lean_Elab_Term_getCalcFirstStep___closed__9 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__9);
l_Lean_Elab_Term_getCalcFirstStep___closed__10 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__10);
l_Lean_Elab_Term_getCalcFirstStep___closed__11 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__11);
l_Lean_Elab_Term_getCalcFirstStep___closed__12 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__12);
l_Lean_Elab_Term_getCalcFirstStep___closed__13 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__13);
l_Lean_Elab_Term_getCalcFirstStep___closed__14 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__14);
l_Lean_Elab_Term_getCalcFirstStep___closed__15 = _init_l_Lean_Elab_Term_getCalcFirstStep___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_getCalcFirstStep___closed__15);
l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1___closed__1 = _init_l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_getCalcSteps___spec__1___closed__1);
l_Lean_Elab_Term_getCalcSteps___closed__1 = _init_l_Lean_Elab_Term_getCalcSteps___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_getCalcSteps___closed__1);
l_Lean_Elab_Term_getCalcSteps___closed__2 = _init_l_Lean_Elab_Term_getCalcSteps___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_getCalcSteps___closed__2);
l_Lean_Elab_Term_getCalcSteps___closed__3 = _init_l_Lean_Elab_Term_getCalcSteps___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_getCalcSteps___closed__3);
l_Lean_Elab_Term_getCalcSteps___closed__4 = _init_l_Lean_Elab_Term_getCalcSteps___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_getCalcSteps___closed__4);
l_Lean_Elab_Term_getCalcSteps___closed__5 = _init_l_Lean_Elab_Term_getCalcSteps___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_getCalcSteps___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2___closed__10);
l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3___closed__1 = _init_l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3___closed__1);
l_Lean_Elab_Term_elabCalcSteps___closed__1 = _init_l_Lean_Elab_Term_elabCalcSteps___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabCalcSteps___closed__1);
l_Lean_Elab_Term_elabCalcSteps___closed__2 = _init_l_Lean_Elab_Term_elabCalcSteps___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabCalcSteps___closed__2);
l_Lean_Elab_Term_elabCalcSteps___closed__3 = _init_l_Lean_Elab_Term_elabCalcSteps___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabCalcSteps___closed__3);
l_Lean_Elab_Term_elabCalcSteps___closed__4 = _init_l_Lean_Elab_Term_elabCalcSteps___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabCalcSteps___closed__4);
l_Lean_Elab_Term_elabCalcSteps___closed__5 = _init_l_Lean_Elab_Term_elabCalcSteps___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabCalcSteps___closed__5);
l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1);
l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__2);
l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__3);
l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__4);
l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__5);
l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__6);
l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCalc__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1___closed__1);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
