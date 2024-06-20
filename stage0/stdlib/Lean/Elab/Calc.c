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
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__16;
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
size_t lean_usize_of_nat(lean_object*);
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
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__17;
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
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__18;
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
lean_object* lean_array_get_size(lean_object*);
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
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_useDiagnosticMsg;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trans", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__6;
x_2 = l_Lean_Elab_Term_mkCalcTrans___closed__14;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkCalcTrans___closed__17;
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
x_104 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_105 = l_Lean_Expr_const___override(x_104, x_34);
x_106 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
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
x_134 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
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
x_143 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
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
x_162 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
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
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
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
x_181 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_181);
lean_ctor_set(x_24, 0, x_28);
x_182 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_182);
lean_ctor_set(x_16, 0, x_24);
x_183 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_183);
lean_ctor_set(x_15, 0, x_16);
x_184 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_178);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_184;
}
}
else
{
uint8_t x_185; 
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
x_185 = !lean_is_exclusive(x_100);
if (x_185 == 0)
{
return x_100;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_100, 0);
x_187 = lean_ctor_get(x_100, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_100);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_189 = lean_ctor_get(x_84, 0);
x_190 = lean_ctor_get(x_84, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_84);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_67);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_192);
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
x_193 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_194 = l_Lean_Expr_const___override(x_193, x_34);
x_195 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_196 = lean_array_push(x_195, x_52);
lean_inc(x_55);
x_197 = lean_array_push(x_196, x_55);
lean_inc(x_58);
x_198 = lean_array_push(x_197, x_58);
lean_inc(x_19);
x_199 = lean_array_push(x_198, x_19);
lean_inc(x_40);
x_200 = lean_array_push(x_199, x_40);
lean_inc(x_189);
x_201 = lean_array_push(x_200, x_189);
x_202 = l_Lean_mkAppN(x_194, x_201);
lean_dec(x_201);
x_203 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_202);
x_204 = l_Lean_Meta_trySynthInstance(x_202, x_203, x_5, x_6, x_7, x_8, x_190);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 1)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_202);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_209 = l_Lean_Expr_const___override(x_208, x_34);
x_210 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_211 = lean_array_push(x_210, x_52);
x_212 = lean_array_push(x_211, x_55);
x_213 = lean_array_push(x_212, x_58);
x_214 = lean_array_push(x_213, x_19);
x_215 = lean_array_push(x_214, x_40);
x_216 = lean_array_push(x_215, x_189);
x_217 = lean_array_push(x_216, x_207);
x_218 = lean_array_push(x_217, x_22);
x_219 = lean_array_push(x_218, x_23);
x_220 = lean_array_push(x_219, x_43);
x_221 = lean_array_push(x_220, x_1);
x_222 = lean_array_push(x_221, x_3);
x_223 = l_Lean_mkAppN(x_209, x_222);
lean_dec(x_222);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_223);
x_224 = lean_infer_type(x_223, x_5, x_6, x_7, x_8, x_206);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_225, x_5, x_6, x_7, x_8, x_226);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_231 = l_Lean_Expr_headBeta(x_228);
x_232 = l_Lean_Elab_Term_getCalcRelation_x3f(x_231, x_5, x_6, x_7, x_8, x_229);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_223);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = l_Lean_indentExpr(x_231);
x_237 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_235)) {
 x_238 = lean_alloc_ctor(7, 2, 0);
} else {
 x_238 = x_235;
 lean_ctor_set_tag(x_238, 7);
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_230)) {
 x_240 = lean_alloc_ctor(7, 2, 0);
} else {
 x_240 = x_230;
 lean_ctor_set_tag(x_240, 7);
}
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_240, x_5, x_6, x_7, x_8, x_234);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_233);
lean_dec(x_230);
x_246 = lean_ctor_get(x_232, 1);
lean_inc(x_246);
lean_dec(x_232);
x_247 = lean_box(0);
x_248 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_223, x_231, x_247, x_5, x_6, x_7, x_8, x_246);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_223);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_249 = lean_ctor_get(x_224, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_224, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_251 = x_224;
} else {
 lean_dec_ref(x_224);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_205);
lean_dec(x_34);
lean_dec(x_189);
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
x_253 = lean_ctor_get(x_204, 1);
lean_inc(x_253);
lean_dec(x_204);
x_254 = l_Lean_indentExpr(x_202);
x_255 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_254);
lean_ctor_set(x_28, 0, x_255);
x_256 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_256);
lean_ctor_set(x_24, 0, x_28);
x_257 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_257);
lean_ctor_set(x_16, 0, x_24);
x_258 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_258);
lean_ctor_set(x_15, 0, x_16);
x_259 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_253);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_202);
lean_dec(x_34);
lean_dec(x_189);
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
x_260 = lean_ctor_get(x_204, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_204, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_262 = x_204;
} else {
 lean_dec_ref(x_204);
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
lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_264 = lean_ctor_get(x_78, 0);
x_265 = lean_ctor_get(x_78, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_78);
lean_ctor_set(x_29, 0, x_264);
x_266 = 0;
x_267 = lean_box(0);
lean_inc(x_5);
x_268 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_266, x_267, x_5, x_6, x_7, x_8, x_265);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
x_272 = lean_box(0);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_271;
 lean_ctor_set_tag(x_273, 1);
}
lean_ctor_set(x_273, 0, x_67);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_64);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 1, x_274);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 1, x_74);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_69);
lean_ctor_set(x_35, 0, x_49);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_46);
x_275 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_276 = l_Lean_Expr_const___override(x_275, x_34);
x_277 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_278 = lean_array_push(x_277, x_52);
lean_inc(x_55);
x_279 = lean_array_push(x_278, x_55);
lean_inc(x_58);
x_280 = lean_array_push(x_279, x_58);
lean_inc(x_19);
x_281 = lean_array_push(x_280, x_19);
lean_inc(x_40);
x_282 = lean_array_push(x_281, x_40);
lean_inc(x_269);
x_283 = lean_array_push(x_282, x_269);
x_284 = l_Lean_mkAppN(x_276, x_283);
lean_dec(x_283);
x_285 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_284);
x_286 = l_Lean_Meta_trySynthInstance(x_284, x_285, x_5, x_6, x_7, x_8, x_270);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 1)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_284);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_291 = l_Lean_Expr_const___override(x_290, x_34);
x_292 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_293 = lean_array_push(x_292, x_52);
x_294 = lean_array_push(x_293, x_55);
x_295 = lean_array_push(x_294, x_58);
x_296 = lean_array_push(x_295, x_19);
x_297 = lean_array_push(x_296, x_40);
x_298 = lean_array_push(x_297, x_269);
x_299 = lean_array_push(x_298, x_289);
x_300 = lean_array_push(x_299, x_22);
x_301 = lean_array_push(x_300, x_23);
x_302 = lean_array_push(x_301, x_43);
x_303 = lean_array_push(x_302, x_1);
x_304 = lean_array_push(x_303, x_3);
x_305 = l_Lean_mkAppN(x_291, x_304);
lean_dec(x_304);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_305);
x_306 = lean_infer_type(x_305, x_5, x_6, x_7, x_8, x_288);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_307, x_5, x_6, x_7, x_8, x_308);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_312 = x_309;
} else {
 lean_dec_ref(x_309);
 x_312 = lean_box(0);
}
x_313 = l_Lean_Expr_headBeta(x_310);
x_314 = l_Lean_Elab_Term_getCalcRelation_x3f(x_313, x_5, x_6, x_7, x_8, x_311);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_305);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_317 = x_314;
} else {
 lean_dec_ref(x_314);
 x_317 = lean_box(0);
}
x_318 = l_Lean_indentExpr(x_313);
x_319 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_317)) {
 x_320 = lean_alloc_ctor(7, 2, 0);
} else {
 x_320 = x_317;
 lean_ctor_set_tag(x_320, 7);
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_312)) {
 x_322 = lean_alloc_ctor(7, 2, 0);
} else {
 x_322 = x_312;
 lean_ctor_set_tag(x_322, 7);
}
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_322, x_5, x_6, x_7, x_8, x_316);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_326 = x_323;
} else {
 lean_dec_ref(x_323);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_315);
lean_dec(x_312);
x_328 = lean_ctor_get(x_314, 1);
lean_inc(x_328);
lean_dec(x_314);
x_329 = lean_box(0);
x_330 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_305, x_313, x_329, x_5, x_6, x_7, x_8, x_328);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_305);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_331 = lean_ctor_get(x_306, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_306, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_333 = x_306;
} else {
 lean_dec_ref(x_306);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_287);
lean_dec(x_34);
lean_dec(x_269);
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
x_335 = lean_ctor_get(x_286, 1);
lean_inc(x_335);
lean_dec(x_286);
x_336 = l_Lean_indentExpr(x_284);
x_337 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_336);
lean_ctor_set(x_28, 0, x_337);
x_338 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_338);
lean_ctor_set(x_24, 0, x_28);
x_339 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_339);
lean_ctor_set(x_16, 0, x_24);
x_340 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_340);
lean_ctor_set(x_15, 0, x_16);
x_341 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_335);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_284);
lean_dec(x_34);
lean_dec(x_269);
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
x_342 = lean_ctor_get(x_286, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_286, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_344 = x_286;
} else {
 lean_dec_ref(x_286);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_346 = lean_ctor_get(x_74, 0);
x_347 = lean_ctor_get(x_74, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_74);
lean_inc(x_52);
x_348 = l_Lean_mkArrow(x_52, x_346, x_7, x_8, x_347);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_351 = x_348;
} else {
 lean_dec_ref(x_348);
 x_351 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_349);
x_352 = 0;
x_353 = lean_box(0);
lean_inc(x_5);
x_354 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_352, x_353, x_5, x_6, x_7, x_8, x_350);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_357 = x_354;
} else {
 lean_dec_ref(x_354);
 x_357 = lean_box(0);
}
x_358 = lean_box(0);
if (lean_is_scalar(x_357)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_357;
 lean_ctor_set_tag(x_359, 1);
}
lean_ctor_set(x_359, 0, x_67);
lean_ctor_set(x_359, 1, x_358);
if (lean_is_scalar(x_351)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_351;
 lean_ctor_set_tag(x_360, 1);
}
lean_ctor_set(x_360, 0, x_64);
lean_ctor_set(x_360, 1, x_359);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_61);
lean_ctor_set(x_361, 1, x_360);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 1, x_361);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_69);
lean_ctor_set(x_35, 0, x_49);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_46);
x_362 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_363 = l_Lean_Expr_const___override(x_362, x_34);
x_364 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_365 = lean_array_push(x_364, x_52);
lean_inc(x_55);
x_366 = lean_array_push(x_365, x_55);
lean_inc(x_58);
x_367 = lean_array_push(x_366, x_58);
lean_inc(x_19);
x_368 = lean_array_push(x_367, x_19);
lean_inc(x_40);
x_369 = lean_array_push(x_368, x_40);
lean_inc(x_355);
x_370 = lean_array_push(x_369, x_355);
x_371 = l_Lean_mkAppN(x_363, x_370);
lean_dec(x_370);
x_372 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_371);
x_373 = l_Lean_Meta_trySynthInstance(x_371, x_372, x_5, x_6, x_7, x_8, x_356);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_obj_tag(x_374) == 1)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_371);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
lean_dec(x_374);
x_377 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_378 = l_Lean_Expr_const___override(x_377, x_34);
x_379 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_380 = lean_array_push(x_379, x_52);
x_381 = lean_array_push(x_380, x_55);
x_382 = lean_array_push(x_381, x_58);
x_383 = lean_array_push(x_382, x_19);
x_384 = lean_array_push(x_383, x_40);
x_385 = lean_array_push(x_384, x_355);
x_386 = lean_array_push(x_385, x_376);
x_387 = lean_array_push(x_386, x_22);
x_388 = lean_array_push(x_387, x_23);
x_389 = lean_array_push(x_388, x_43);
x_390 = lean_array_push(x_389, x_1);
x_391 = lean_array_push(x_390, x_3);
x_392 = l_Lean_mkAppN(x_378, x_391);
lean_dec(x_391);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_392);
x_393 = lean_infer_type(x_392, x_5, x_6, x_7, x_8, x_375);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_394, x_5, x_6, x_7, x_8, x_395);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_399 = x_396;
} else {
 lean_dec_ref(x_396);
 x_399 = lean_box(0);
}
x_400 = l_Lean_Expr_headBeta(x_397);
x_401 = l_Lean_Elab_Term_getCalcRelation_x3f(x_400, x_5, x_6, x_7, x_8, x_398);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_392);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
x_405 = l_Lean_indentExpr(x_400);
x_406 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_404)) {
 x_407 = lean_alloc_ctor(7, 2, 0);
} else {
 x_407 = x_404;
 lean_ctor_set_tag(x_407, 7);
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_405);
x_408 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_399)) {
 x_409 = lean_alloc_ctor(7, 2, 0);
} else {
 x_409 = x_399;
 lean_ctor_set_tag(x_409, 7);
}
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_410 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_409, x_5, x_6, x_7, x_8, x_403);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_413 = x_410;
} else {
 lean_dec_ref(x_410);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_402);
lean_dec(x_399);
x_415 = lean_ctor_get(x_401, 1);
lean_inc(x_415);
lean_dec(x_401);
x_416 = lean_box(0);
x_417 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_392, x_400, x_416, x_5, x_6, x_7, x_8, x_415);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_392);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_418 = lean_ctor_get(x_393, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_393, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_420 = x_393;
} else {
 lean_dec_ref(x_393);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_374);
lean_dec(x_34);
lean_dec(x_355);
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
x_422 = lean_ctor_get(x_373, 1);
lean_inc(x_422);
lean_dec(x_373);
x_423 = l_Lean_indentExpr(x_371);
x_424 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_423);
lean_ctor_set(x_28, 0, x_424);
x_425 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_425);
lean_ctor_set(x_24, 0, x_28);
x_426 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_426);
lean_ctor_set(x_16, 0, x_24);
x_427 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_427);
lean_ctor_set(x_15, 0, x_16);
x_428 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_422);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_371);
lean_dec(x_34);
lean_dec(x_355);
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
x_429 = lean_ctor_get(x_373, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_373, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_431 = x_373;
} else {
 lean_dec_ref(x_373);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_433 = lean_ctor_get(x_69, 0);
x_434 = lean_ctor_get(x_69, 1);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_69);
lean_inc(x_433);
x_435 = l_Lean_Expr_sort___override(x_433);
lean_inc(x_58);
x_436 = l_Lean_mkArrow(x_58, x_435, x_7, x_8, x_434);
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
lean_inc(x_52);
x_440 = l_Lean_mkArrow(x_52, x_437, x_7, x_8, x_438);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_443 = x_440;
} else {
 lean_dec_ref(x_440);
 x_443 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_441);
x_444 = 0;
x_445 = lean_box(0);
lean_inc(x_5);
x_446 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_444, x_445, x_5, x_6, x_7, x_8, x_442);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_449 = x_446;
} else {
 lean_dec_ref(x_446);
 x_449 = lean_box(0);
}
x_450 = lean_box(0);
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_449;
 lean_ctor_set_tag(x_451, 1);
}
lean_ctor_set(x_451, 0, x_67);
lean_ctor_set(x_451, 1, x_450);
if (lean_is_scalar(x_443)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_443;
 lean_ctor_set_tag(x_452, 1);
}
lean_ctor_set(x_452, 0, x_64);
lean_ctor_set(x_452, 1, x_451);
if (lean_is_scalar(x_439)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_439;
 lean_ctor_set_tag(x_453, 1);
}
lean_ctor_set(x_453, 0, x_61);
lean_ctor_set(x_453, 1, x_452);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_433);
lean_ctor_set(x_454, 1, x_453);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_454);
lean_ctor_set(x_35, 0, x_49);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_46);
x_455 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_456 = l_Lean_Expr_const___override(x_455, x_34);
x_457 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_52);
x_458 = lean_array_push(x_457, x_52);
lean_inc(x_55);
x_459 = lean_array_push(x_458, x_55);
lean_inc(x_58);
x_460 = lean_array_push(x_459, x_58);
lean_inc(x_19);
x_461 = lean_array_push(x_460, x_19);
lean_inc(x_40);
x_462 = lean_array_push(x_461, x_40);
lean_inc(x_447);
x_463 = lean_array_push(x_462, x_447);
x_464 = l_Lean_mkAppN(x_456, x_463);
lean_dec(x_463);
x_465 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_464);
x_466 = l_Lean_Meta_trySynthInstance(x_464, x_465, x_5, x_6, x_7, x_8, x_448);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 1)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_464);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_469 = lean_ctor_get(x_467, 0);
lean_inc(x_469);
lean_dec(x_467);
x_470 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_471 = l_Lean_Expr_const___override(x_470, x_34);
x_472 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_473 = lean_array_push(x_472, x_52);
x_474 = lean_array_push(x_473, x_55);
x_475 = lean_array_push(x_474, x_58);
x_476 = lean_array_push(x_475, x_19);
x_477 = lean_array_push(x_476, x_40);
x_478 = lean_array_push(x_477, x_447);
x_479 = lean_array_push(x_478, x_469);
x_480 = lean_array_push(x_479, x_22);
x_481 = lean_array_push(x_480, x_23);
x_482 = lean_array_push(x_481, x_43);
x_483 = lean_array_push(x_482, x_1);
x_484 = lean_array_push(x_483, x_3);
x_485 = l_Lean_mkAppN(x_471, x_484);
lean_dec(x_484);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_485);
x_486 = lean_infer_type(x_485, x_5, x_6, x_7, x_8, x_468);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_487, x_5, x_6, x_7, x_8, x_488);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_492 = x_489;
} else {
 lean_dec_ref(x_489);
 x_492 = lean_box(0);
}
x_493 = l_Lean_Expr_headBeta(x_490);
x_494 = l_Lean_Elab_Term_getCalcRelation_x3f(x_493, x_5, x_6, x_7, x_8, x_491);
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_485);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_497 = x_494;
} else {
 lean_dec_ref(x_494);
 x_497 = lean_box(0);
}
x_498 = l_Lean_indentExpr(x_493);
x_499 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_497)) {
 x_500 = lean_alloc_ctor(7, 2, 0);
} else {
 x_500 = x_497;
 lean_ctor_set_tag(x_500, 7);
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_498);
x_501 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_492)) {
 x_502 = lean_alloc_ctor(7, 2, 0);
} else {
 x_502 = x_492;
 lean_ctor_set_tag(x_502, 7);
}
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
x_503 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_502, x_5, x_6, x_7, x_8, x_496);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_506 = x_503;
} else {
 lean_dec_ref(x_503);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_495);
lean_dec(x_492);
x_508 = lean_ctor_get(x_494, 1);
lean_inc(x_508);
lean_dec(x_494);
x_509 = lean_box(0);
x_510 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_485, x_493, x_509, x_5, x_6, x_7, x_8, x_508);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_510;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_485);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_511 = lean_ctor_get(x_486, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_486, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_513 = x_486;
} else {
 lean_dec_ref(x_486);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_467);
lean_dec(x_34);
lean_dec(x_447);
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
x_515 = lean_ctor_get(x_466, 1);
lean_inc(x_515);
lean_dec(x_466);
x_516 = l_Lean_indentExpr(x_464);
x_517 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_516);
lean_ctor_set(x_28, 0, x_517);
x_518 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_518);
lean_ctor_set(x_24, 0, x_28);
x_519 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_519);
lean_ctor_set(x_16, 0, x_24);
x_520 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_520);
lean_ctor_set(x_15, 0, x_16);
x_521 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_515);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_521;
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_464);
lean_dec(x_34);
lean_dec(x_447);
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
x_522 = lean_ctor_get(x_466, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_466, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_524 = x_466;
} else {
 lean_dec_ref(x_466);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_523);
return x_525;
}
}
}
else
{
uint8_t x_526; 
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
x_526 = !lean_is_exclusive(x_66);
if (x_526 == 0)
{
return x_66;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_66, 0);
x_528 = lean_ctor_get(x_66, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_66);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_528);
return x_529;
}
}
}
else
{
uint8_t x_530; 
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
x_530 = !lean_is_exclusive(x_63);
if (x_530 == 0)
{
return x_63;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_63, 0);
x_532 = lean_ctor_get(x_63, 1);
lean_inc(x_532);
lean_inc(x_531);
lean_dec(x_63);
x_533 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_533, 0, x_531);
lean_ctor_set(x_533, 1, x_532);
return x_533;
}
}
}
else
{
uint8_t x_534; 
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
x_534 = !lean_is_exclusive(x_60);
if (x_534 == 0)
{
return x_60;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_60, 0);
x_536 = lean_ctor_get(x_60, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_60);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
else
{
uint8_t x_538; 
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
x_538 = !lean_is_exclusive(x_57);
if (x_538 == 0)
{
return x_57;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_57, 0);
x_540 = lean_ctor_get(x_57, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_57);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
}
}
else
{
uint8_t x_542; 
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
x_542 = !lean_is_exclusive(x_54);
if (x_542 == 0)
{
return x_54;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_54, 0);
x_544 = lean_ctor_get(x_54, 1);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_54);
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
return x_545;
}
}
}
else
{
uint8_t x_546; 
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
x_546 = !lean_is_exclusive(x_51);
if (x_546 == 0)
{
return x_51;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_51, 0);
x_548 = lean_ctor_get(x_51, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_51);
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
return x_549;
}
}
}
else
{
uint8_t x_550; 
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
x_550 = !lean_is_exclusive(x_48);
if (x_550 == 0)
{
return x_48;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_48, 0);
x_552 = lean_ctor_get(x_48, 1);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_48);
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
return x_553;
}
}
}
else
{
uint8_t x_554; 
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
x_554 = !lean_is_exclusive(x_45);
if (x_554 == 0)
{
return x_45;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_45, 0);
x_556 = lean_ctor_get(x_45, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_45);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
}
else
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_35, 1);
lean_inc(x_558);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_559 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_40);
x_562 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_40, x_5, x_6, x_7, x_8, x_561);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
lean_dec(x_562);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_565 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_564);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
lean_dec(x_565);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_568 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_567);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec(x_568);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_558);
x_571 = lean_infer_type(x_558, x_5, x_6, x_7, x_8, x_570);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
lean_dec(x_571);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_566);
x_574 = l_Lean_Meta_getLevel(x_566, x_5, x_6, x_7, x_8, x_573);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_569);
x_577 = l_Lean_Meta_getLevel(x_569, x_5, x_6, x_7, x_8, x_576);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_572);
x_580 = l_Lean_Meta_getLevel(x_572, x_5, x_6, x_7, x_8, x_579);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_583 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_582);
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
lean_inc(x_584);
x_587 = l_Lean_Expr_sort___override(x_584);
lean_inc(x_572);
x_588 = l_Lean_mkArrow(x_572, x_587, x_7, x_8, x_585);
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
lean_inc(x_566);
x_592 = l_Lean_mkArrow(x_566, x_589, x_7, x_8, x_590);
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_595 = x_592;
} else {
 lean_dec_ref(x_592);
 x_595 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_593);
x_596 = 0;
x_597 = lean_box(0);
lean_inc(x_5);
x_598 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_596, x_597, x_5, x_6, x_7, x_8, x_594);
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_601 = x_598;
} else {
 lean_dec_ref(x_598);
 x_601 = lean_box(0);
}
x_602 = lean_box(0);
if (lean_is_scalar(x_601)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_601;
 lean_ctor_set_tag(x_603, 1);
}
lean_ctor_set(x_603, 0, x_581);
lean_ctor_set(x_603, 1, x_602);
if (lean_is_scalar(x_595)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_595;
 lean_ctor_set_tag(x_604, 1);
}
lean_ctor_set(x_604, 0, x_578);
lean_ctor_set(x_604, 1, x_603);
if (lean_is_scalar(x_591)) {
 x_605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_605 = x_591;
 lean_ctor_set_tag(x_605, 1);
}
lean_ctor_set(x_605, 0, x_575);
lean_ctor_set(x_605, 1, x_604);
if (lean_is_scalar(x_586)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_586;
 lean_ctor_set_tag(x_606, 1);
}
lean_ctor_set(x_606, 0, x_584);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_563);
lean_ctor_set(x_607, 1, x_606);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_607);
lean_ctor_set(x_34, 0, x_560);
x_608 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_34);
x_609 = l_Lean_Expr_const___override(x_608, x_34);
x_610 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_566);
x_611 = lean_array_push(x_610, x_566);
lean_inc(x_569);
x_612 = lean_array_push(x_611, x_569);
lean_inc(x_572);
x_613 = lean_array_push(x_612, x_572);
lean_inc(x_19);
x_614 = lean_array_push(x_613, x_19);
lean_inc(x_40);
x_615 = lean_array_push(x_614, x_40);
lean_inc(x_599);
x_616 = lean_array_push(x_615, x_599);
x_617 = l_Lean_mkAppN(x_609, x_616);
lean_dec(x_616);
x_618 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_617);
x_619 = l_Lean_Meta_trySynthInstance(x_617, x_618, x_5, x_6, x_7, x_8, x_600);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
if (lean_obj_tag(x_620) == 1)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_617);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
x_622 = lean_ctor_get(x_620, 0);
lean_inc(x_622);
lean_dec(x_620);
x_623 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_624 = l_Lean_Expr_const___override(x_623, x_34);
x_625 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_626 = lean_array_push(x_625, x_566);
x_627 = lean_array_push(x_626, x_569);
x_628 = lean_array_push(x_627, x_572);
x_629 = lean_array_push(x_628, x_19);
x_630 = lean_array_push(x_629, x_40);
x_631 = lean_array_push(x_630, x_599);
x_632 = lean_array_push(x_631, x_622);
x_633 = lean_array_push(x_632, x_22);
x_634 = lean_array_push(x_633, x_23);
x_635 = lean_array_push(x_634, x_558);
x_636 = lean_array_push(x_635, x_1);
x_637 = lean_array_push(x_636, x_3);
x_638 = l_Lean_mkAppN(x_624, x_637);
lean_dec(x_637);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_638);
x_639 = lean_infer_type(x_638, x_5, x_6, x_7, x_8, x_621);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec(x_639);
x_642 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_640, x_5, x_6, x_7, x_8, x_641);
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
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
x_646 = l_Lean_Expr_headBeta(x_643);
x_647 = l_Lean_Elab_Term_getCalcRelation_x3f(x_646, x_5, x_6, x_7, x_8, x_644);
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_638);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 x_650 = x_647;
} else {
 lean_dec_ref(x_647);
 x_650 = lean_box(0);
}
x_651 = l_Lean_indentExpr(x_646);
x_652 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_650)) {
 x_653 = lean_alloc_ctor(7, 2, 0);
} else {
 x_653 = x_650;
 lean_ctor_set_tag(x_653, 7);
}
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_651);
x_654 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_645)) {
 x_655 = lean_alloc_ctor(7, 2, 0);
} else {
 x_655 = x_645;
 lean_ctor_set_tag(x_655, 7);
}
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
x_656 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_655, x_5, x_6, x_7, x_8, x_649);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 lean_ctor_release(x_656, 1);
 x_659 = x_656;
} else {
 lean_dec_ref(x_656);
 x_659 = lean_box(0);
}
if (lean_is_scalar(x_659)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_659;
}
lean_ctor_set(x_660, 0, x_657);
lean_ctor_set(x_660, 1, x_658);
return x_660;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_648);
lean_dec(x_645);
x_661 = lean_ctor_get(x_647, 1);
lean_inc(x_661);
lean_dec(x_647);
x_662 = lean_box(0);
x_663 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_638, x_646, x_662, x_5, x_6, x_7, x_8, x_661);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_663;
}
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_638);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_664 = lean_ctor_get(x_639, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_639, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_666 = x_639;
} else {
 lean_dec_ref(x_639);
 x_666 = lean_box(0);
}
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_667 = x_666;
}
lean_ctor_set(x_667, 0, x_664);
lean_ctor_set(x_667, 1, x_665);
return x_667;
}
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_620);
lean_dec(x_34);
lean_dec(x_599);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_558);
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_668 = lean_ctor_get(x_619, 1);
lean_inc(x_668);
lean_dec(x_619);
x_669 = l_Lean_indentExpr(x_617);
x_670 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_669);
lean_ctor_set(x_28, 0, x_670);
x_671 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_671);
lean_ctor_set(x_24, 0, x_28);
x_672 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_672);
lean_ctor_set(x_16, 0, x_24);
x_673 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_673);
lean_ctor_set(x_15, 0, x_16);
x_674 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_668);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_674;
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_617);
lean_dec(x_34);
lean_dec(x_599);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_558);
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
x_675 = lean_ctor_get(x_619, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_619, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_677 = x_619;
} else {
 lean_dec_ref(x_619);
 x_677 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_678 = lean_alloc_ctor(1, 2, 0);
} else {
 x_678 = x_677;
}
lean_ctor_set(x_678, 0, x_675);
lean_ctor_set(x_678, 1, x_676);
return x_678;
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_578);
lean_dec(x_575);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
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
x_679 = lean_ctor_get(x_580, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_580, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_681 = x_580;
} else {
 lean_dec_ref(x_580);
 x_681 = lean_box(0);
}
if (lean_is_scalar(x_681)) {
 x_682 = lean_alloc_ctor(1, 2, 0);
} else {
 x_682 = x_681;
}
lean_ctor_set(x_682, 0, x_679);
lean_ctor_set(x_682, 1, x_680);
return x_682;
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec(x_575);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
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
x_683 = lean_ctor_get(x_577, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_577, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_685 = x_577;
} else {
 lean_dec_ref(x_577);
 x_685 = lean_box(0);
}
if (lean_is_scalar(x_685)) {
 x_686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_686 = x_685;
}
lean_ctor_set(x_686, 0, x_683);
lean_ctor_set(x_686, 1, x_684);
return x_686;
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
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
x_687 = lean_ctor_get(x_574, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_574, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_689 = x_574;
} else {
 lean_dec_ref(x_574);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(1, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
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
x_691 = lean_ctor_get(x_571, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_571, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_693 = x_571;
} else {
 lean_dec_ref(x_571);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_691);
lean_ctor_set(x_694, 1, x_692);
return x_694;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_566);
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
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
x_695 = lean_ctor_get(x_568, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_568, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_697 = x_568;
} else {
 lean_dec_ref(x_568);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
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
x_699 = lean_ctor_get(x_565, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_565, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_701 = x_565;
} else {
 lean_dec_ref(x_565);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_699);
lean_ctor_set(x_702, 1, x_700);
return x_702;
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_560);
lean_dec(x_558);
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
x_703 = lean_ctor_get(x_562, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_562, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_705 = x_562;
} else {
 lean_dec_ref(x_562);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(1, 2, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_703);
lean_ctor_set(x_706, 1, x_704);
return x_706;
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
lean_dec(x_558);
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
x_707 = lean_ctor_get(x_559, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_559, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_709 = x_559;
} else {
 lean_dec_ref(x_559);
 x_709 = lean_box(0);
}
if (lean_is_scalar(x_709)) {
 x_710 = lean_alloc_ctor(1, 2, 0);
} else {
 x_710 = x_709;
}
lean_ctor_set(x_710, 0, x_707);
lean_ctor_set(x_710, 1, x_708);
return x_710;
}
}
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_711 = lean_ctor_get(x_34, 0);
lean_inc(x_711);
lean_dec(x_34);
x_712 = lean_ctor_get(x_35, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_713 = x_35;
} else {
 lean_dec_ref(x_35);
 x_713 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_714 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_37);
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
lean_inc(x_711);
x_717 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_711, x_5, x_6, x_7, x_8, x_716);
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
lean_inc(x_22);
x_720 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_719);
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
lean_inc(x_23);
x_723 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_722);
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
lean_inc(x_712);
x_726 = lean_infer_type(x_712, x_5, x_6, x_7, x_8, x_725);
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
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_724);
x_732 = l_Lean_Meta_getLevel(x_724, x_5, x_6, x_7, x_8, x_731);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_727);
x_735 = l_Lean_Meta_getLevel(x_727, x_5, x_6, x_7, x_8, x_734);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
x_738 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_737);
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 x_741 = x_738;
} else {
 lean_dec_ref(x_738);
 x_741 = lean_box(0);
}
lean_inc(x_739);
x_742 = l_Lean_Expr_sort___override(x_739);
lean_inc(x_727);
x_743 = l_Lean_mkArrow(x_727, x_742, x_7, x_8, x_740);
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_746 = x_743;
} else {
 lean_dec_ref(x_743);
 x_746 = lean_box(0);
}
lean_inc(x_721);
x_747 = l_Lean_mkArrow(x_721, x_744, x_7, x_8, x_745);
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
lean_ctor_set(x_29, 0, x_748);
x_751 = 0;
x_752 = lean_box(0);
lean_inc(x_5);
x_753 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_751, x_752, x_5, x_6, x_7, x_8, x_749);
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_756 = x_753;
} else {
 lean_dec_ref(x_753);
 x_756 = lean_box(0);
}
x_757 = lean_box(0);
if (lean_is_scalar(x_756)) {
 x_758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_758 = x_756;
 lean_ctor_set_tag(x_758, 1);
}
lean_ctor_set(x_758, 0, x_736);
lean_ctor_set(x_758, 1, x_757);
if (lean_is_scalar(x_750)) {
 x_759 = lean_alloc_ctor(1, 2, 0);
} else {
 x_759 = x_750;
 lean_ctor_set_tag(x_759, 1);
}
lean_ctor_set(x_759, 0, x_733);
lean_ctor_set(x_759, 1, x_758);
if (lean_is_scalar(x_746)) {
 x_760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_760 = x_746;
 lean_ctor_set_tag(x_760, 1);
}
lean_ctor_set(x_760, 0, x_730);
lean_ctor_set(x_760, 1, x_759);
if (lean_is_scalar(x_741)) {
 x_761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_761 = x_741;
 lean_ctor_set_tag(x_761, 1);
}
lean_ctor_set(x_761, 0, x_739);
lean_ctor_set(x_761, 1, x_760);
if (lean_is_scalar(x_713)) {
 x_762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_762 = x_713;
 lean_ctor_set_tag(x_762, 1);
}
lean_ctor_set(x_762, 0, x_718);
lean_ctor_set(x_762, 1, x_761);
x_763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_763, 0, x_715);
lean_ctor_set(x_763, 1, x_762);
x_764 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_763);
x_765 = l_Lean_Expr_const___override(x_764, x_763);
x_766 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_721);
x_767 = lean_array_push(x_766, x_721);
lean_inc(x_724);
x_768 = lean_array_push(x_767, x_724);
lean_inc(x_727);
x_769 = lean_array_push(x_768, x_727);
lean_inc(x_19);
x_770 = lean_array_push(x_769, x_19);
lean_inc(x_711);
x_771 = lean_array_push(x_770, x_711);
lean_inc(x_754);
x_772 = lean_array_push(x_771, x_754);
x_773 = l_Lean_mkAppN(x_765, x_772);
lean_dec(x_772);
x_774 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_773);
x_775 = l_Lean_Meta_trySynthInstance(x_773, x_774, x_5, x_6, x_7, x_8, x_755);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
if (lean_obj_tag(x_776) == 1)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_773);
lean_free_object(x_28);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = lean_ctor_get(x_776, 0);
lean_inc(x_778);
lean_dec(x_776);
x_779 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_780 = l_Lean_Expr_const___override(x_779, x_763);
x_781 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_782 = lean_array_push(x_781, x_721);
x_783 = lean_array_push(x_782, x_724);
x_784 = lean_array_push(x_783, x_727);
x_785 = lean_array_push(x_784, x_19);
x_786 = lean_array_push(x_785, x_711);
x_787 = lean_array_push(x_786, x_754);
x_788 = lean_array_push(x_787, x_778);
x_789 = lean_array_push(x_788, x_22);
x_790 = lean_array_push(x_789, x_23);
x_791 = lean_array_push(x_790, x_712);
x_792 = lean_array_push(x_791, x_1);
x_793 = lean_array_push(x_792, x_3);
x_794 = l_Lean_mkAppN(x_780, x_793);
lean_dec(x_793);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_794);
x_795 = lean_infer_type(x_794, x_5, x_6, x_7, x_8, x_777);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
x_798 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_796, x_5, x_6, x_7, x_8, x_797);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 x_801 = x_798;
} else {
 lean_dec_ref(x_798);
 x_801 = lean_box(0);
}
x_802 = l_Lean_Expr_headBeta(x_799);
x_803 = l_Lean_Elab_Term_getCalcRelation_x3f(x_802, x_5, x_6, x_7, x_8, x_800);
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_794);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_806 = x_803;
} else {
 lean_dec_ref(x_803);
 x_806 = lean_box(0);
}
x_807 = l_Lean_indentExpr(x_802);
x_808 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_806)) {
 x_809 = lean_alloc_ctor(7, 2, 0);
} else {
 x_809 = x_806;
 lean_ctor_set_tag(x_809, 7);
}
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_807);
x_810 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_801)) {
 x_811 = lean_alloc_ctor(7, 2, 0);
} else {
 x_811 = x_801;
 lean_ctor_set_tag(x_811, 7);
}
lean_ctor_set(x_811, 0, x_809);
lean_ctor_set(x_811, 1, x_810);
x_812 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_811, x_5, x_6, x_7, x_8, x_805);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_812, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_815 = x_812;
} else {
 lean_dec_ref(x_812);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_814);
return x_816;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
lean_dec(x_804);
lean_dec(x_801);
x_817 = lean_ctor_get(x_803, 1);
lean_inc(x_817);
lean_dec(x_803);
x_818 = lean_box(0);
x_819 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_794, x_802, x_818, x_5, x_6, x_7, x_8, x_817);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_819;
}
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_794);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_820 = lean_ctor_get(x_795, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_795, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 x_822 = x_795;
} else {
 lean_dec_ref(x_795);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_822)) {
 x_823 = lean_alloc_ctor(1, 2, 0);
} else {
 x_823 = x_822;
}
lean_ctor_set(x_823, 0, x_820);
lean_ctor_set(x_823, 1, x_821);
return x_823;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
lean_dec(x_776);
lean_dec(x_763);
lean_dec(x_754);
lean_dec(x_727);
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_824 = lean_ctor_get(x_775, 1);
lean_inc(x_824);
lean_dec(x_775);
x_825 = l_Lean_indentExpr(x_773);
x_826 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_825);
lean_ctor_set(x_28, 0, x_826);
x_827 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_827);
lean_ctor_set(x_24, 0, x_28);
x_828 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_828);
lean_ctor_set(x_16, 0, x_24);
x_829 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_829);
lean_ctor_set(x_15, 0, x_16);
x_830 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_824);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_830;
}
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_773);
lean_dec(x_763);
lean_dec(x_754);
lean_dec(x_727);
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_712);
lean_dec(x_711);
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
x_831 = lean_ctor_get(x_775, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_775, 1);
lean_inc(x_832);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_833 = x_775;
} else {
 lean_dec_ref(x_775);
 x_833 = lean_box(0);
}
if (lean_is_scalar(x_833)) {
 x_834 = lean_alloc_ctor(1, 2, 0);
} else {
 x_834 = x_833;
}
lean_ctor_set(x_834, 0, x_831);
lean_ctor_set(x_834, 1, x_832);
return x_834;
}
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec(x_733);
lean_dec(x_730);
lean_dec(x_727);
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
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
x_835 = lean_ctor_get(x_735, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_735, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_837 = x_735;
} else {
 lean_dec_ref(x_735);
 x_837 = lean_box(0);
}
if (lean_is_scalar(x_837)) {
 x_838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_838 = x_837;
}
lean_ctor_set(x_838, 0, x_835);
lean_ctor_set(x_838, 1, x_836);
return x_838;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_730);
lean_dec(x_727);
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
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
x_839 = lean_ctor_get(x_732, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_732, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_732)) {
 lean_ctor_release(x_732, 0);
 lean_ctor_release(x_732, 1);
 x_841 = x_732;
} else {
 lean_dec_ref(x_732);
 x_841 = lean_box(0);
}
if (lean_is_scalar(x_841)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_841;
}
lean_ctor_set(x_842, 0, x_839);
lean_ctor_set(x_842, 1, x_840);
return x_842;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_727);
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
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
x_843 = lean_ctor_get(x_729, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_729, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_845 = x_729;
} else {
 lean_dec_ref(x_729);
 x_845 = lean_box(0);
}
if (lean_is_scalar(x_845)) {
 x_846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_846 = x_845;
}
lean_ctor_set(x_846, 0, x_843);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
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
x_847 = lean_ctor_get(x_726, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_726, 1);
lean_inc(x_848);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_849 = x_726;
} else {
 lean_dec_ref(x_726);
 x_849 = lean_box(0);
}
if (lean_is_scalar(x_849)) {
 x_850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_850 = x_849;
}
lean_ctor_set(x_850, 0, x_847);
lean_ctor_set(x_850, 1, x_848);
return x_850;
}
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
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
x_851 = lean_ctor_get(x_723, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_723, 1);
lean_inc(x_852);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_853 = x_723;
} else {
 lean_dec_ref(x_723);
 x_853 = lean_box(0);
}
if (lean_is_scalar(x_853)) {
 x_854 = lean_alloc_ctor(1, 2, 0);
} else {
 x_854 = x_853;
}
lean_ctor_set(x_854, 0, x_851);
lean_ctor_set(x_854, 1, x_852);
return x_854;
}
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec(x_718);
lean_dec(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
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
x_855 = lean_ctor_get(x_720, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_720, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_857 = x_720;
} else {
 lean_dec_ref(x_720);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_855);
lean_ctor_set(x_858, 1, x_856);
return x_858;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_715);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
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
x_859 = lean_ctor_get(x_717, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_717, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_861 = x_717;
} else {
 lean_dec_ref(x_717);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(1, 2, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_859);
lean_ctor_set(x_862, 1, x_860);
return x_862;
}
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
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
x_863 = lean_ctor_get(x_714, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_714, 1);
lean_inc(x_864);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_865 = x_714;
} else {
 lean_dec_ref(x_714);
 x_865 = lean_box(0);
}
if (lean_is_scalar(x_865)) {
 x_866 = lean_alloc_ctor(1, 2, 0);
} else {
 x_866 = x_865;
}
lean_ctor_set(x_866, 0, x_863);
lean_ctor_set(x_866, 1, x_864);
return x_866;
}
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_867 = lean_ctor_get(x_28, 1);
lean_inc(x_867);
lean_dec(x_28);
x_868 = lean_ctor_get(x_34, 0);
lean_inc(x_868);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_869 = x_34;
} else {
 lean_dec_ref(x_34);
 x_869 = lean_box(0);
}
x_870 = lean_ctor_get(x_35, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_871 = x_35;
} else {
 lean_dec_ref(x_35);
 x_871 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_872 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_867);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_868);
x_875 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_868, x_5, x_6, x_7, x_8, x_874);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_878 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_877);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_881 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_880);
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_870);
x_884 = lean_infer_type(x_870, x_5, x_6, x_7, x_8, x_883);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_879);
x_887 = l_Lean_Meta_getLevel(x_879, x_5, x_6, x_7, x_8, x_886);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
lean_dec(x_887);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_882);
x_890 = l_Lean_Meta_getLevel(x_882, x_5, x_6, x_7, x_8, x_889);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_885);
x_893 = l_Lean_Meta_getLevel(x_885, x_5, x_6, x_7, x_8, x_892);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; uint8_t x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec(x_893);
x_896 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_895);
x_897 = lean_ctor_get(x_896, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_896, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 lean_ctor_release(x_896, 1);
 x_899 = x_896;
} else {
 lean_dec_ref(x_896);
 x_899 = lean_box(0);
}
lean_inc(x_897);
x_900 = l_Lean_Expr_sort___override(x_897);
lean_inc(x_885);
x_901 = l_Lean_mkArrow(x_885, x_900, x_7, x_8, x_898);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_904 = x_901;
} else {
 lean_dec_ref(x_901);
 x_904 = lean_box(0);
}
lean_inc(x_879);
x_905 = l_Lean_mkArrow(x_879, x_902, x_7, x_8, x_903);
x_906 = lean_ctor_get(x_905, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_905, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_908 = x_905;
} else {
 lean_dec_ref(x_905);
 x_908 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_906);
x_909 = 0;
x_910 = lean_box(0);
lean_inc(x_5);
x_911 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_909, x_910, x_5, x_6, x_7, x_8, x_907);
x_912 = lean_ctor_get(x_911, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_911, 1);
lean_inc(x_913);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 lean_ctor_release(x_911, 1);
 x_914 = x_911;
} else {
 lean_dec_ref(x_911);
 x_914 = lean_box(0);
}
x_915 = lean_box(0);
if (lean_is_scalar(x_914)) {
 x_916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_916 = x_914;
 lean_ctor_set_tag(x_916, 1);
}
lean_ctor_set(x_916, 0, x_894);
lean_ctor_set(x_916, 1, x_915);
if (lean_is_scalar(x_908)) {
 x_917 = lean_alloc_ctor(1, 2, 0);
} else {
 x_917 = x_908;
 lean_ctor_set_tag(x_917, 1);
}
lean_ctor_set(x_917, 0, x_891);
lean_ctor_set(x_917, 1, x_916);
if (lean_is_scalar(x_904)) {
 x_918 = lean_alloc_ctor(1, 2, 0);
} else {
 x_918 = x_904;
 lean_ctor_set_tag(x_918, 1);
}
lean_ctor_set(x_918, 0, x_888);
lean_ctor_set(x_918, 1, x_917);
if (lean_is_scalar(x_899)) {
 x_919 = lean_alloc_ctor(1, 2, 0);
} else {
 x_919 = x_899;
 lean_ctor_set_tag(x_919, 1);
}
lean_ctor_set(x_919, 0, x_897);
lean_ctor_set(x_919, 1, x_918);
if (lean_is_scalar(x_871)) {
 x_920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_920 = x_871;
 lean_ctor_set_tag(x_920, 1);
}
lean_ctor_set(x_920, 0, x_876);
lean_ctor_set(x_920, 1, x_919);
if (lean_is_scalar(x_869)) {
 x_921 = lean_alloc_ctor(1, 2, 0);
} else {
 x_921 = x_869;
 lean_ctor_set_tag(x_921, 1);
}
lean_ctor_set(x_921, 0, x_873);
lean_ctor_set(x_921, 1, x_920);
x_922 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_921);
x_923 = l_Lean_Expr_const___override(x_922, x_921);
x_924 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_879);
x_925 = lean_array_push(x_924, x_879);
lean_inc(x_882);
x_926 = lean_array_push(x_925, x_882);
lean_inc(x_885);
x_927 = lean_array_push(x_926, x_885);
lean_inc(x_19);
x_928 = lean_array_push(x_927, x_19);
lean_inc(x_868);
x_929 = lean_array_push(x_928, x_868);
lean_inc(x_912);
x_930 = lean_array_push(x_929, x_912);
x_931 = l_Lean_mkAppN(x_923, x_930);
lean_dec(x_930);
x_932 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_931);
x_933 = l_Lean_Meta_trySynthInstance(x_931, x_932, x_5, x_6, x_7, x_8, x_913);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; 
x_934 = lean_ctor_get(x_933, 0);
lean_inc(x_934);
if (lean_obj_tag(x_934) == 1)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
lean_dec(x_931);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_935 = lean_ctor_get(x_933, 1);
lean_inc(x_935);
lean_dec(x_933);
x_936 = lean_ctor_get(x_934, 0);
lean_inc(x_936);
lean_dec(x_934);
x_937 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_938 = l_Lean_Expr_const___override(x_937, x_921);
x_939 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_940 = lean_array_push(x_939, x_879);
x_941 = lean_array_push(x_940, x_882);
x_942 = lean_array_push(x_941, x_885);
x_943 = lean_array_push(x_942, x_19);
x_944 = lean_array_push(x_943, x_868);
x_945 = lean_array_push(x_944, x_912);
x_946 = lean_array_push(x_945, x_936);
x_947 = lean_array_push(x_946, x_22);
x_948 = lean_array_push(x_947, x_23);
x_949 = lean_array_push(x_948, x_870);
x_950 = lean_array_push(x_949, x_1);
x_951 = lean_array_push(x_950, x_3);
x_952 = l_Lean_mkAppN(x_938, x_951);
lean_dec(x_951);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_952);
x_953 = lean_infer_type(x_952, x_5, x_6, x_7, x_8, x_935);
if (lean_obj_tag(x_953) == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_954 = lean_ctor_get(x_953, 0);
lean_inc(x_954);
x_955 = lean_ctor_get(x_953, 1);
lean_inc(x_955);
lean_dec(x_953);
x_956 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_954, x_5, x_6, x_7, x_8, x_955);
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_959 = x_956;
} else {
 lean_dec_ref(x_956);
 x_959 = lean_box(0);
}
x_960 = l_Lean_Expr_headBeta(x_957);
x_961 = l_Lean_Elab_Term_getCalcRelation_x3f(x_960, x_5, x_6, x_7, x_8, x_958);
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_dec(x_952);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_964 = x_961;
} else {
 lean_dec_ref(x_961);
 x_964 = lean_box(0);
}
x_965 = l_Lean_indentExpr(x_960);
x_966 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_964)) {
 x_967 = lean_alloc_ctor(7, 2, 0);
} else {
 x_967 = x_964;
 lean_ctor_set_tag(x_967, 7);
}
lean_ctor_set(x_967, 0, x_966);
lean_ctor_set(x_967, 1, x_965);
x_968 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_959)) {
 x_969 = lean_alloc_ctor(7, 2, 0);
} else {
 x_969 = x_959;
 lean_ctor_set_tag(x_969, 7);
}
lean_ctor_set(x_969, 0, x_967);
lean_ctor_set(x_969, 1, x_968);
x_970 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_969, x_5, x_6, x_7, x_8, x_963);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 lean_ctor_release(x_970, 1);
 x_973 = x_970;
} else {
 lean_dec_ref(x_970);
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
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_962);
lean_dec(x_959);
x_975 = lean_ctor_get(x_961, 1);
lean_inc(x_975);
lean_dec(x_961);
x_976 = lean_box(0);
x_977 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_952, x_960, x_976, x_5, x_6, x_7, x_8, x_975);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_977;
}
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
lean_dec(x_952);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_978 = lean_ctor_get(x_953, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_953, 1);
lean_inc(x_979);
if (lean_is_exclusive(x_953)) {
 lean_ctor_release(x_953, 0);
 lean_ctor_release(x_953, 1);
 x_980 = x_953;
} else {
 lean_dec_ref(x_953);
 x_980 = lean_box(0);
}
if (lean_is_scalar(x_980)) {
 x_981 = lean_alloc_ctor(1, 2, 0);
} else {
 x_981 = x_980;
}
lean_ctor_set(x_981, 0, x_978);
lean_ctor_set(x_981, 1, x_979);
return x_981;
}
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_934);
lean_dec(x_921);
lean_dec(x_912);
lean_dec(x_885);
lean_dec(x_882);
lean_dec(x_879);
lean_dec(x_870);
lean_dec(x_868);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_982 = lean_ctor_get(x_933, 1);
lean_inc(x_982);
lean_dec(x_933);
x_983 = l_Lean_indentExpr(x_931);
x_984 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
x_985 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_983);
x_986 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_986);
lean_ctor_set(x_24, 0, x_985);
x_987 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_987);
lean_ctor_set(x_16, 0, x_24);
x_988 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_988);
lean_ctor_set(x_15, 0, x_16);
x_989 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_982);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_989;
}
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_931);
lean_dec(x_921);
lean_dec(x_912);
lean_dec(x_885);
lean_dec(x_882);
lean_dec(x_879);
lean_dec(x_870);
lean_dec(x_868);
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
x_990 = lean_ctor_get(x_933, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_933, 1);
lean_inc(x_991);
if (lean_is_exclusive(x_933)) {
 lean_ctor_release(x_933, 0);
 lean_ctor_release(x_933, 1);
 x_992 = x_933;
} else {
 lean_dec_ref(x_933);
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
lean_dec(x_891);
lean_dec(x_888);
lean_dec(x_885);
lean_dec(x_882);
lean_dec(x_879);
lean_dec(x_876);
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
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
x_994 = lean_ctor_get(x_893, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_893, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_996 = x_893;
} else {
 lean_dec_ref(x_893);
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
lean_dec(x_888);
lean_dec(x_885);
lean_dec(x_882);
lean_dec(x_879);
lean_dec(x_876);
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
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
x_998 = lean_ctor_get(x_890, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_890, 1);
lean_inc(x_999);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_1000 = x_890;
} else {
 lean_dec_ref(x_890);
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
lean_dec(x_885);
lean_dec(x_882);
lean_dec(x_879);
lean_dec(x_876);
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
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
x_1002 = lean_ctor_get(x_887, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_887, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_1004 = x_887;
} else {
 lean_dec_ref(x_887);
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
lean_dec(x_882);
lean_dec(x_879);
lean_dec(x_876);
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
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
x_1006 = lean_ctor_get(x_884, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_884, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 x_1008 = x_884;
} else {
 lean_dec_ref(x_884);
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
lean_dec(x_879);
lean_dec(x_876);
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
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
x_1010 = lean_ctor_get(x_881, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_881, 1);
lean_inc(x_1011);
if (lean_is_exclusive(x_881)) {
 lean_ctor_release(x_881, 0);
 lean_ctor_release(x_881, 1);
 x_1012 = x_881;
} else {
 lean_dec_ref(x_881);
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
lean_dec(x_876);
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
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
x_1014 = lean_ctor_get(x_878, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_878, 1);
lean_inc(x_1015);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_1016 = x_878;
} else {
 lean_dec_ref(x_878);
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
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
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
x_1018 = lean_ctor_get(x_875, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_875, 1);
lean_inc(x_1019);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_1020 = x_875;
} else {
 lean_dec_ref(x_875);
 x_1020 = lean_box(0);
}
if (lean_is_scalar(x_1020)) {
 x_1021 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1021 = x_1020;
}
lean_ctor_set(x_1021, 0, x_1018);
lean_ctor_set(x_1021, 1, x_1019);
return x_1021;
}
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
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
x_1022 = lean_ctor_get(x_872, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_872, 1);
lean_inc(x_1023);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_1024 = x_872;
} else {
 lean_dec_ref(x_872);
 x_1024 = lean_box(0);
}
if (lean_is_scalar(x_1024)) {
 x_1025 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1025 = x_1024;
}
lean_ctor_set(x_1025, 0, x_1022);
lean_ctor_set(x_1025, 1, x_1023);
return x_1025;
}
}
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1026 = lean_ctor_get(x_29, 0);
lean_inc(x_1026);
lean_dec(x_29);
x_1027 = lean_ctor_get(x_1026, 1);
lean_inc(x_1027);
x_1028 = lean_ctor_get(x_28, 1);
lean_inc(x_1028);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_1029 = x_28;
} else {
 lean_dec_ref(x_28);
 x_1029 = lean_box(0);
}
x_1030 = lean_ctor_get(x_1026, 0);
lean_inc(x_1030);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1031 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1031 = lean_box(0);
}
x_1032 = lean_ctor_get(x_1027, 1);
lean_inc(x_1032);
if (lean_is_exclusive(x_1027)) {
 lean_ctor_release(x_1027, 0);
 lean_ctor_release(x_1027, 1);
 x_1033 = x_1027;
} else {
 lean_dec_ref(x_1027);
 x_1033 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_1034 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_1028);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1035 = lean_ctor_get(x_1034, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1034, 1);
lean_inc(x_1036);
lean_dec(x_1034);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1030);
x_1037 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1030, x_5, x_6, x_7, x_8, x_1036);
if (lean_obj_tag(x_1037) == 0)
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
lean_dec(x_1037);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_1040 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_1039);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
lean_dec(x_1040);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_1043 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_1042);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1044 = lean_ctor_get(x_1043, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1043, 1);
lean_inc(x_1045);
lean_dec(x_1043);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1032);
x_1046 = lean_infer_type(x_1032, x_5, x_6, x_7, x_8, x_1045);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1041);
x_1049 = l_Lean_Meta_getLevel(x_1041, x_5, x_6, x_7, x_8, x_1048);
if (lean_obj_tag(x_1049) == 0)
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1044);
x_1052 = l_Lean_Meta_getLevel(x_1044, x_5, x_6, x_7, x_8, x_1051);
if (lean_obj_tag(x_1052) == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1053 = lean_ctor_get(x_1052, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1052, 1);
lean_inc(x_1054);
lean_dec(x_1052);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1047);
x_1055 = l_Lean_Meta_getLevel(x_1047, x_5, x_6, x_7, x_8, x_1054);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; uint8_t x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1055, 1);
lean_inc(x_1057);
lean_dec(x_1055);
x_1058 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1057);
x_1059 = lean_ctor_get(x_1058, 0);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1058, 1);
lean_inc(x_1060);
if (lean_is_exclusive(x_1058)) {
 lean_ctor_release(x_1058, 0);
 lean_ctor_release(x_1058, 1);
 x_1061 = x_1058;
} else {
 lean_dec_ref(x_1058);
 x_1061 = lean_box(0);
}
lean_inc(x_1059);
x_1062 = l_Lean_Expr_sort___override(x_1059);
lean_inc(x_1047);
x_1063 = l_Lean_mkArrow(x_1047, x_1062, x_7, x_8, x_1060);
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1066 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1066 = lean_box(0);
}
lean_inc(x_1041);
x_1067 = l_Lean_mkArrow(x_1041, x_1064, x_7, x_8, x_1065);
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1067, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 lean_ctor_release(x_1067, 1);
 x_1070 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1070 = lean_box(0);
}
x_1071 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1071, 0, x_1068);
x_1072 = 0;
x_1073 = lean_box(0);
lean_inc(x_5);
x_1074 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1071, x_1072, x_1073, x_5, x_6, x_7, x_8, x_1069);
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1077 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1077 = lean_box(0);
}
x_1078 = lean_box(0);
if (lean_is_scalar(x_1077)) {
 x_1079 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1079 = x_1077;
 lean_ctor_set_tag(x_1079, 1);
}
lean_ctor_set(x_1079, 0, x_1056);
lean_ctor_set(x_1079, 1, x_1078);
if (lean_is_scalar(x_1070)) {
 x_1080 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1080 = x_1070;
 lean_ctor_set_tag(x_1080, 1);
}
lean_ctor_set(x_1080, 0, x_1053);
lean_ctor_set(x_1080, 1, x_1079);
if (lean_is_scalar(x_1066)) {
 x_1081 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1081 = x_1066;
 lean_ctor_set_tag(x_1081, 1);
}
lean_ctor_set(x_1081, 0, x_1050);
lean_ctor_set(x_1081, 1, x_1080);
if (lean_is_scalar(x_1061)) {
 x_1082 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1082 = x_1061;
 lean_ctor_set_tag(x_1082, 1);
}
lean_ctor_set(x_1082, 0, x_1059);
lean_ctor_set(x_1082, 1, x_1081);
if (lean_is_scalar(x_1033)) {
 x_1083 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1083 = x_1033;
 lean_ctor_set_tag(x_1083, 1);
}
lean_ctor_set(x_1083, 0, x_1038);
lean_ctor_set(x_1083, 1, x_1082);
if (lean_is_scalar(x_1031)) {
 x_1084 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1084 = x_1031;
 lean_ctor_set_tag(x_1084, 1);
}
lean_ctor_set(x_1084, 0, x_1035);
lean_ctor_set(x_1084, 1, x_1083);
x_1085 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_1084);
x_1086 = l_Lean_Expr_const___override(x_1085, x_1084);
x_1087 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_1041);
x_1088 = lean_array_push(x_1087, x_1041);
lean_inc(x_1044);
x_1089 = lean_array_push(x_1088, x_1044);
lean_inc(x_1047);
x_1090 = lean_array_push(x_1089, x_1047);
lean_inc(x_19);
x_1091 = lean_array_push(x_1090, x_19);
lean_inc(x_1030);
x_1092 = lean_array_push(x_1091, x_1030);
lean_inc(x_1075);
x_1093 = lean_array_push(x_1092, x_1075);
x_1094 = l_Lean_mkAppN(x_1086, x_1093);
lean_dec(x_1093);
x_1095 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1094);
x_1096 = l_Lean_Meta_trySynthInstance(x_1094, x_1095, x_5, x_6, x_7, x_8, x_1076);
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1097; 
x_1097 = lean_ctor_get(x_1096, 0);
lean_inc(x_1097);
if (lean_obj_tag(x_1097) == 1)
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
lean_dec(x_1094);
lean_dec(x_1029);
lean_free_object(x_24);
lean_free_object(x_16);
lean_free_object(x_15);
x_1098 = lean_ctor_get(x_1096, 1);
lean_inc(x_1098);
lean_dec(x_1096);
x_1099 = lean_ctor_get(x_1097, 0);
lean_inc(x_1099);
lean_dec(x_1097);
x_1100 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_1101 = l_Lean_Expr_const___override(x_1100, x_1084);
x_1102 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_1103 = lean_array_push(x_1102, x_1041);
x_1104 = lean_array_push(x_1103, x_1044);
x_1105 = lean_array_push(x_1104, x_1047);
x_1106 = lean_array_push(x_1105, x_19);
x_1107 = lean_array_push(x_1106, x_1030);
x_1108 = lean_array_push(x_1107, x_1075);
x_1109 = lean_array_push(x_1108, x_1099);
x_1110 = lean_array_push(x_1109, x_22);
x_1111 = lean_array_push(x_1110, x_23);
x_1112 = lean_array_push(x_1111, x_1032);
x_1113 = lean_array_push(x_1112, x_1);
x_1114 = lean_array_push(x_1113, x_3);
x_1115 = l_Lean_mkAppN(x_1101, x_1114);
lean_dec(x_1114);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1115);
x_1116 = lean_infer_type(x_1115, x_5, x_6, x_7, x_8, x_1098);
if (lean_obj_tag(x_1116) == 0)
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1116, 1);
lean_inc(x_1118);
lean_dec(x_1116);
x_1119 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1117, x_5, x_6, x_7, x_8, x_1118);
x_1120 = lean_ctor_get(x_1119, 0);
lean_inc(x_1120);
x_1121 = lean_ctor_get(x_1119, 1);
lean_inc(x_1121);
if (lean_is_exclusive(x_1119)) {
 lean_ctor_release(x_1119, 0);
 lean_ctor_release(x_1119, 1);
 x_1122 = x_1119;
} else {
 lean_dec_ref(x_1119);
 x_1122 = lean_box(0);
}
x_1123 = l_Lean_Expr_headBeta(x_1120);
x_1124 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1123, x_5, x_6, x_7, x_8, x_1121);
x_1125 = lean_ctor_get(x_1124, 0);
lean_inc(x_1125);
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
lean_dec(x_1115);
x_1126 = lean_ctor_get(x_1124, 1);
lean_inc(x_1126);
if (lean_is_exclusive(x_1124)) {
 lean_ctor_release(x_1124, 0);
 lean_ctor_release(x_1124, 1);
 x_1127 = x_1124;
} else {
 lean_dec_ref(x_1124);
 x_1127 = lean_box(0);
}
x_1128 = l_Lean_indentExpr(x_1123);
x_1129 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_1127)) {
 x_1130 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1130 = x_1127;
 lean_ctor_set_tag(x_1130, 7);
}
lean_ctor_set(x_1130, 0, x_1129);
lean_ctor_set(x_1130, 1, x_1128);
x_1131 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1122)) {
 x_1132 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1132 = x_1122;
 lean_ctor_set_tag(x_1132, 7);
}
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set(x_1132, 1, x_1131);
x_1133 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1132, x_5, x_6, x_7, x_8, x_1126);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1133, 1);
lean_inc(x_1135);
if (lean_is_exclusive(x_1133)) {
 lean_ctor_release(x_1133, 0);
 lean_ctor_release(x_1133, 1);
 x_1136 = x_1133;
} else {
 lean_dec_ref(x_1133);
 x_1136 = lean_box(0);
}
if (lean_is_scalar(x_1136)) {
 x_1137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1137 = x_1136;
}
lean_ctor_set(x_1137, 0, x_1134);
lean_ctor_set(x_1137, 1, x_1135);
return x_1137;
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1125);
lean_dec(x_1122);
x_1138 = lean_ctor_get(x_1124, 1);
lean_inc(x_1138);
lean_dec(x_1124);
x_1139 = lean_box(0);
x_1140 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1115, x_1123, x_1139, x_5, x_6, x_7, x_8, x_1138);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1140;
}
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
lean_dec(x_1115);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1141 = lean_ctor_get(x_1116, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1116, 1);
lean_inc(x_1142);
if (lean_is_exclusive(x_1116)) {
 lean_ctor_release(x_1116, 0);
 lean_ctor_release(x_1116, 1);
 x_1143 = x_1116;
} else {
 lean_dec_ref(x_1116);
 x_1143 = lean_box(0);
}
if (lean_is_scalar(x_1143)) {
 x_1144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1144 = x_1143;
}
lean_ctor_set(x_1144, 0, x_1141);
lean_ctor_set(x_1144, 1, x_1142);
return x_1144;
}
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
lean_dec(x_1097);
lean_dec(x_1084);
lean_dec(x_1075);
lean_dec(x_1047);
lean_dec(x_1044);
lean_dec(x_1041);
lean_dec(x_1032);
lean_dec(x_1030);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1145 = lean_ctor_get(x_1096, 1);
lean_inc(x_1145);
lean_dec(x_1096);
x_1146 = l_Lean_indentExpr(x_1094);
x_1147 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
if (lean_is_scalar(x_1029)) {
 x_1148 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1148 = x_1029;
 lean_ctor_set_tag(x_1148, 7);
}
lean_ctor_set(x_1148, 0, x_1147);
lean_ctor_set(x_1148, 1, x_1146);
x_1149 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_1149);
lean_ctor_set(x_24, 0, x_1148);
x_1150 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_1150);
lean_ctor_set(x_16, 0, x_24);
x_1151 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_1151);
lean_ctor_set(x_15, 0, x_16);
x_1152 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_1145);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1152;
}
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
lean_dec(x_1094);
lean_dec(x_1084);
lean_dec(x_1075);
lean_dec(x_1047);
lean_dec(x_1044);
lean_dec(x_1041);
lean_dec(x_1032);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1153 = lean_ctor_get(x_1096, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1096, 1);
lean_inc(x_1154);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1155 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1155 = lean_box(0);
}
if (lean_is_scalar(x_1155)) {
 x_1156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1156 = x_1155;
}
lean_ctor_set(x_1156, 0, x_1153);
lean_ctor_set(x_1156, 1, x_1154);
return x_1156;
}
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
lean_dec(x_1053);
lean_dec(x_1050);
lean_dec(x_1047);
lean_dec(x_1044);
lean_dec(x_1041);
lean_dec(x_1038);
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1157 = lean_ctor_get(x_1055, 0);
lean_inc(x_1157);
x_1158 = lean_ctor_get(x_1055, 1);
lean_inc(x_1158);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 lean_ctor_release(x_1055, 1);
 x_1159 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1159 = lean_box(0);
}
if (lean_is_scalar(x_1159)) {
 x_1160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1160 = x_1159;
}
lean_ctor_set(x_1160, 0, x_1157);
lean_ctor_set(x_1160, 1, x_1158);
return x_1160;
}
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
lean_dec(x_1050);
lean_dec(x_1047);
lean_dec(x_1044);
lean_dec(x_1041);
lean_dec(x_1038);
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1161 = lean_ctor_get(x_1052, 0);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1052, 1);
lean_inc(x_1162);
if (lean_is_exclusive(x_1052)) {
 lean_ctor_release(x_1052, 0);
 lean_ctor_release(x_1052, 1);
 x_1163 = x_1052;
} else {
 lean_dec_ref(x_1052);
 x_1163 = lean_box(0);
}
if (lean_is_scalar(x_1163)) {
 x_1164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1164 = x_1163;
}
lean_ctor_set(x_1164, 0, x_1161);
lean_ctor_set(x_1164, 1, x_1162);
return x_1164;
}
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1047);
lean_dec(x_1044);
lean_dec(x_1041);
lean_dec(x_1038);
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1165 = lean_ctor_get(x_1049, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1049, 1);
lean_inc(x_1166);
if (lean_is_exclusive(x_1049)) {
 lean_ctor_release(x_1049, 0);
 lean_ctor_release(x_1049, 1);
 x_1167 = x_1049;
} else {
 lean_dec_ref(x_1049);
 x_1167 = lean_box(0);
}
if (lean_is_scalar(x_1167)) {
 x_1168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1168 = x_1167;
}
lean_ctor_set(x_1168, 0, x_1165);
lean_ctor_set(x_1168, 1, x_1166);
return x_1168;
}
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
lean_dec(x_1044);
lean_dec(x_1041);
lean_dec(x_1038);
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1169 = lean_ctor_get(x_1046, 0);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1046, 1);
lean_inc(x_1170);
if (lean_is_exclusive(x_1046)) {
 lean_ctor_release(x_1046, 0);
 lean_ctor_release(x_1046, 1);
 x_1171 = x_1046;
} else {
 lean_dec_ref(x_1046);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1169);
lean_ctor_set(x_1172, 1, x_1170);
return x_1172;
}
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
lean_dec(x_1041);
lean_dec(x_1038);
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1173 = lean_ctor_get(x_1043, 0);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1043, 1);
lean_inc(x_1174);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1175 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1175 = lean_box(0);
}
if (lean_is_scalar(x_1175)) {
 x_1176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1176 = x_1175;
}
lean_ctor_set(x_1176, 0, x_1173);
lean_ctor_set(x_1176, 1, x_1174);
return x_1176;
}
}
else
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
lean_dec(x_1038);
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1177 = lean_ctor_get(x_1040, 0);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1040, 1);
lean_inc(x_1178);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1179 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1179 = lean_box(0);
}
if (lean_is_scalar(x_1179)) {
 x_1180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1180 = x_1179;
}
lean_ctor_set(x_1180, 0, x_1177);
lean_ctor_set(x_1180, 1, x_1178);
return x_1180;
}
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; 
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1181 = lean_ctor_get(x_1037, 0);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1037, 1);
lean_inc(x_1182);
if (lean_is_exclusive(x_1037)) {
 lean_ctor_release(x_1037, 0);
 lean_ctor_release(x_1037, 1);
 x_1183 = x_1037;
} else {
 lean_dec_ref(x_1037);
 x_1183 = lean_box(0);
}
if (lean_is_scalar(x_1183)) {
 x_1184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1184 = x_1183;
}
lean_ctor_set(x_1184, 0, x_1181);
lean_ctor_set(x_1184, 1, x_1182);
return x_1184;
}
}
else
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
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
x_1185 = lean_ctor_get(x_1034, 0);
lean_inc(x_1185);
x_1186 = lean_ctor_get(x_1034, 1);
lean_inc(x_1186);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1187 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1187 = lean_box(0);
}
if (lean_is_scalar(x_1187)) {
 x_1188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1188 = x_1187;
}
lean_ctor_set(x_1188, 0, x_1185);
lean_ctor_set(x_1188, 1, x_1186);
return x_1188;
}
}
}
}
else
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1189 = lean_ctor_get(x_24, 0);
x_1190 = lean_ctor_get(x_24, 1);
lean_inc(x_1190);
lean_inc(x_1189);
lean_dec(x_24);
x_1191 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1189, x_5, x_6, x_7, x_8, x_1190);
lean_dec(x_1189);
x_1192 = lean_ctor_get(x_1191, 0);
lean_inc(x_1192);
if (lean_obj_tag(x_1192) == 0)
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
lean_free_object(x_16);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1193 = lean_ctor_get(x_1191, 1);
lean_inc(x_1193);
lean_dec(x_1191);
x_1194 = l_Lean_Elab_Term_mkCalcTrans___closed__5;
x_1195 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(x_1194, x_5, x_6, x_7, x_8, x_1193);
return x_1195;
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1196 = lean_ctor_get(x_1192, 0);
lean_inc(x_1196);
if (lean_is_exclusive(x_1192)) {
 lean_ctor_release(x_1192, 0);
 x_1197 = x_1192;
} else {
 lean_dec_ref(x_1192);
 x_1197 = lean_box(0);
}
x_1198 = lean_ctor_get(x_1196, 1);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_1191, 1);
lean_inc(x_1199);
if (lean_is_exclusive(x_1191)) {
 lean_ctor_release(x_1191, 0);
 lean_ctor_release(x_1191, 1);
 x_1200 = x_1191;
} else {
 lean_dec_ref(x_1191);
 x_1200 = lean_box(0);
}
x_1201 = lean_ctor_get(x_1196, 0);
lean_inc(x_1201);
if (lean_is_exclusive(x_1196)) {
 lean_ctor_release(x_1196, 0);
 lean_ctor_release(x_1196, 1);
 x_1202 = x_1196;
} else {
 lean_dec_ref(x_1196);
 x_1202 = lean_box(0);
}
x_1203 = lean_ctor_get(x_1198, 1);
lean_inc(x_1203);
if (lean_is_exclusive(x_1198)) {
 lean_ctor_release(x_1198, 0);
 lean_ctor_release(x_1198, 1);
 x_1204 = x_1198;
} else {
 lean_dec_ref(x_1198);
 x_1204 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_1205 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_1199);
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
lean_inc(x_1201);
x_1208 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1201, x_5, x_6, x_7, x_8, x_1207);
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
lean_inc(x_22);
x_1211 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_1210);
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
lean_inc(x_23);
x_1214 = lean_infer_type(x_23, x_5, x_6, x_7, x_8, x_1213);
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
lean_inc(x_1203);
x_1217 = lean_infer_type(x_1203, x_5, x_6, x_7, x_8, x_1216);
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
x_1218 = lean_ctor_get(x_1217, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1217, 1);
lean_inc(x_1219);
lean_dec(x_1217);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1212);
x_1220 = l_Lean_Meta_getLevel(x_1212, x_5, x_6, x_7, x_8, x_1219);
if (lean_obj_tag(x_1220) == 0)
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
x_1221 = lean_ctor_get(x_1220, 0);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1220, 1);
lean_inc(x_1222);
lean_dec(x_1220);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1215);
x_1223 = l_Lean_Meta_getLevel(x_1215, x_5, x_6, x_7, x_8, x_1222);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1224 = lean_ctor_get(x_1223, 0);
lean_inc(x_1224);
x_1225 = lean_ctor_get(x_1223, 1);
lean_inc(x_1225);
lean_dec(x_1223);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1218);
x_1226 = l_Lean_Meta_getLevel(x_1218, x_5, x_6, x_7, x_8, x_1225);
if (lean_obj_tag(x_1226) == 0)
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; uint8_t x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1227 = lean_ctor_get(x_1226, 0);
lean_inc(x_1227);
x_1228 = lean_ctor_get(x_1226, 1);
lean_inc(x_1228);
lean_dec(x_1226);
x_1229 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1228);
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
lean_inc(x_1230);
x_1233 = l_Lean_Expr_sort___override(x_1230);
lean_inc(x_1218);
x_1234 = l_Lean_mkArrow(x_1218, x_1233, x_7, x_8, x_1231);
x_1235 = lean_ctor_get(x_1234, 0);
lean_inc(x_1235);
x_1236 = lean_ctor_get(x_1234, 1);
lean_inc(x_1236);
if (lean_is_exclusive(x_1234)) {
 lean_ctor_release(x_1234, 0);
 lean_ctor_release(x_1234, 1);
 x_1237 = x_1234;
} else {
 lean_dec_ref(x_1234);
 x_1237 = lean_box(0);
}
lean_inc(x_1212);
x_1238 = l_Lean_mkArrow(x_1212, x_1235, x_7, x_8, x_1236);
x_1239 = lean_ctor_get(x_1238, 0);
lean_inc(x_1239);
x_1240 = lean_ctor_get(x_1238, 1);
lean_inc(x_1240);
if (lean_is_exclusive(x_1238)) {
 lean_ctor_release(x_1238, 0);
 lean_ctor_release(x_1238, 1);
 x_1241 = x_1238;
} else {
 lean_dec_ref(x_1238);
 x_1241 = lean_box(0);
}
if (lean_is_scalar(x_1197)) {
 x_1242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1242 = x_1197;
}
lean_ctor_set(x_1242, 0, x_1239);
x_1243 = 0;
x_1244 = lean_box(0);
lean_inc(x_5);
x_1245 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1242, x_1243, x_1244, x_5, x_6, x_7, x_8, x_1240);
x_1246 = lean_ctor_get(x_1245, 0);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1245, 1);
lean_inc(x_1247);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1248 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1248 = lean_box(0);
}
x_1249 = lean_box(0);
if (lean_is_scalar(x_1248)) {
 x_1250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1250 = x_1248;
 lean_ctor_set_tag(x_1250, 1);
}
lean_ctor_set(x_1250, 0, x_1227);
lean_ctor_set(x_1250, 1, x_1249);
if (lean_is_scalar(x_1241)) {
 x_1251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1251 = x_1241;
 lean_ctor_set_tag(x_1251, 1);
}
lean_ctor_set(x_1251, 0, x_1224);
lean_ctor_set(x_1251, 1, x_1250);
if (lean_is_scalar(x_1237)) {
 x_1252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1252 = x_1237;
 lean_ctor_set_tag(x_1252, 1);
}
lean_ctor_set(x_1252, 0, x_1221);
lean_ctor_set(x_1252, 1, x_1251);
if (lean_is_scalar(x_1232)) {
 x_1253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1253 = x_1232;
 lean_ctor_set_tag(x_1253, 1);
}
lean_ctor_set(x_1253, 0, x_1230);
lean_ctor_set(x_1253, 1, x_1252);
if (lean_is_scalar(x_1204)) {
 x_1254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1254 = x_1204;
 lean_ctor_set_tag(x_1254, 1);
}
lean_ctor_set(x_1254, 0, x_1209);
lean_ctor_set(x_1254, 1, x_1253);
if (lean_is_scalar(x_1202)) {
 x_1255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1255 = x_1202;
 lean_ctor_set_tag(x_1255, 1);
}
lean_ctor_set(x_1255, 0, x_1206);
lean_ctor_set(x_1255, 1, x_1254);
x_1256 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_1255);
x_1257 = l_Lean_Expr_const___override(x_1256, x_1255);
x_1258 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_1212);
x_1259 = lean_array_push(x_1258, x_1212);
lean_inc(x_1215);
x_1260 = lean_array_push(x_1259, x_1215);
lean_inc(x_1218);
x_1261 = lean_array_push(x_1260, x_1218);
lean_inc(x_19);
x_1262 = lean_array_push(x_1261, x_19);
lean_inc(x_1201);
x_1263 = lean_array_push(x_1262, x_1201);
lean_inc(x_1246);
x_1264 = lean_array_push(x_1263, x_1246);
x_1265 = l_Lean_mkAppN(x_1257, x_1264);
lean_dec(x_1264);
x_1266 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1265);
x_1267 = l_Lean_Meta_trySynthInstance(x_1265, x_1266, x_5, x_6, x_7, x_8, x_1247);
if (lean_obj_tag(x_1267) == 0)
{
lean_object* x_1268; 
x_1268 = lean_ctor_get(x_1267, 0);
lean_inc(x_1268);
if (lean_obj_tag(x_1268) == 1)
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
lean_dec(x_1265);
lean_dec(x_1200);
lean_free_object(x_16);
lean_free_object(x_15);
x_1269 = lean_ctor_get(x_1267, 1);
lean_inc(x_1269);
lean_dec(x_1267);
x_1270 = lean_ctor_get(x_1268, 0);
lean_inc(x_1270);
lean_dec(x_1268);
x_1271 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_1272 = l_Lean_Expr_const___override(x_1271, x_1255);
x_1273 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_1274 = lean_array_push(x_1273, x_1212);
x_1275 = lean_array_push(x_1274, x_1215);
x_1276 = lean_array_push(x_1275, x_1218);
x_1277 = lean_array_push(x_1276, x_19);
x_1278 = lean_array_push(x_1277, x_1201);
x_1279 = lean_array_push(x_1278, x_1246);
x_1280 = lean_array_push(x_1279, x_1270);
x_1281 = lean_array_push(x_1280, x_22);
x_1282 = lean_array_push(x_1281, x_23);
x_1283 = lean_array_push(x_1282, x_1203);
x_1284 = lean_array_push(x_1283, x_1);
x_1285 = lean_array_push(x_1284, x_3);
x_1286 = l_Lean_mkAppN(x_1272, x_1285);
lean_dec(x_1285);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1286);
x_1287 = lean_infer_type(x_1286, x_5, x_6, x_7, x_8, x_1269);
if (lean_obj_tag(x_1287) == 0)
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1288 = lean_ctor_get(x_1287, 0);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1287, 1);
lean_inc(x_1289);
lean_dec(x_1287);
x_1290 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1288, x_5, x_6, x_7, x_8, x_1289);
x_1291 = lean_ctor_get(x_1290, 0);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1290, 1);
lean_inc(x_1292);
if (lean_is_exclusive(x_1290)) {
 lean_ctor_release(x_1290, 0);
 lean_ctor_release(x_1290, 1);
 x_1293 = x_1290;
} else {
 lean_dec_ref(x_1290);
 x_1293 = lean_box(0);
}
x_1294 = l_Lean_Expr_headBeta(x_1291);
x_1295 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1294, x_5, x_6, x_7, x_8, x_1292);
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
if (lean_obj_tag(x_1296) == 0)
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; 
lean_dec(x_1286);
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
x_1299 = l_Lean_indentExpr(x_1294);
x_1300 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_1298)) {
 x_1301 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1301 = x_1298;
 lean_ctor_set_tag(x_1301, 7);
}
lean_ctor_set(x_1301, 0, x_1300);
lean_ctor_set(x_1301, 1, x_1299);
x_1302 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1293)) {
 x_1303 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1303 = x_1293;
 lean_ctor_set_tag(x_1303, 7);
}
lean_ctor_set(x_1303, 0, x_1301);
lean_ctor_set(x_1303, 1, x_1302);
x_1304 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1303, x_5, x_6, x_7, x_8, x_1297);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1305 = lean_ctor_get(x_1304, 0);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1304, 1);
lean_inc(x_1306);
if (lean_is_exclusive(x_1304)) {
 lean_ctor_release(x_1304, 0);
 lean_ctor_release(x_1304, 1);
 x_1307 = x_1304;
} else {
 lean_dec_ref(x_1304);
 x_1307 = lean_box(0);
}
if (lean_is_scalar(x_1307)) {
 x_1308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1308 = x_1307;
}
lean_ctor_set(x_1308, 0, x_1305);
lean_ctor_set(x_1308, 1, x_1306);
return x_1308;
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
lean_dec(x_1296);
lean_dec(x_1293);
x_1309 = lean_ctor_get(x_1295, 1);
lean_inc(x_1309);
lean_dec(x_1295);
x_1310 = lean_box(0);
x_1311 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1286, x_1294, x_1310, x_5, x_6, x_7, x_8, x_1309);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1311;
}
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
lean_dec(x_1286);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1312 = lean_ctor_get(x_1287, 0);
lean_inc(x_1312);
x_1313 = lean_ctor_get(x_1287, 1);
lean_inc(x_1313);
if (lean_is_exclusive(x_1287)) {
 lean_ctor_release(x_1287, 0);
 lean_ctor_release(x_1287, 1);
 x_1314 = x_1287;
} else {
 lean_dec_ref(x_1287);
 x_1314 = lean_box(0);
}
if (lean_is_scalar(x_1314)) {
 x_1315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1315 = x_1314;
}
lean_ctor_set(x_1315, 0, x_1312);
lean_ctor_set(x_1315, 1, x_1313);
return x_1315;
}
}
else
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
lean_dec(x_1268);
lean_dec(x_1255);
lean_dec(x_1246);
lean_dec(x_1218);
lean_dec(x_1215);
lean_dec(x_1212);
lean_dec(x_1203);
lean_dec(x_1201);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1316 = lean_ctor_get(x_1267, 1);
lean_inc(x_1316);
lean_dec(x_1267);
x_1317 = l_Lean_indentExpr(x_1265);
x_1318 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
if (lean_is_scalar(x_1200)) {
 x_1319 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1319 = x_1200;
 lean_ctor_set_tag(x_1319, 7);
}
lean_ctor_set(x_1319, 0, x_1318);
lean_ctor_set(x_1319, 1, x_1317);
x_1320 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
x_1321 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1321, 0, x_1319);
lean_ctor_set(x_1321, 1, x_1320);
x_1322 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_1322);
lean_ctor_set(x_16, 0, x_1321);
x_1323 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_1323);
lean_ctor_set(x_15, 0, x_16);
x_1324 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_1316);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1324;
}
}
else
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; 
lean_dec(x_1265);
lean_dec(x_1255);
lean_dec(x_1246);
lean_dec(x_1218);
lean_dec(x_1215);
lean_dec(x_1212);
lean_dec(x_1203);
lean_dec(x_1201);
lean_dec(x_1200);
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
x_1325 = lean_ctor_get(x_1267, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1267, 1);
lean_inc(x_1326);
if (lean_is_exclusive(x_1267)) {
 lean_ctor_release(x_1267, 0);
 lean_ctor_release(x_1267, 1);
 x_1327 = x_1267;
} else {
 lean_dec_ref(x_1267);
 x_1327 = lean_box(0);
}
if (lean_is_scalar(x_1327)) {
 x_1328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1328 = x_1327;
}
lean_ctor_set(x_1328, 0, x_1325);
lean_ctor_set(x_1328, 1, x_1326);
return x_1328;
}
}
else
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
lean_dec(x_1224);
lean_dec(x_1221);
lean_dec(x_1218);
lean_dec(x_1215);
lean_dec(x_1212);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1197);
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
x_1329 = lean_ctor_get(x_1226, 0);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1226, 1);
lean_inc(x_1330);
if (lean_is_exclusive(x_1226)) {
 lean_ctor_release(x_1226, 0);
 lean_ctor_release(x_1226, 1);
 x_1331 = x_1226;
} else {
 lean_dec_ref(x_1226);
 x_1331 = lean_box(0);
}
if (lean_is_scalar(x_1331)) {
 x_1332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1332 = x_1331;
}
lean_ctor_set(x_1332, 0, x_1329);
lean_ctor_set(x_1332, 1, x_1330);
return x_1332;
}
}
else
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
lean_dec(x_1221);
lean_dec(x_1218);
lean_dec(x_1215);
lean_dec(x_1212);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1197);
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
x_1333 = lean_ctor_get(x_1223, 0);
lean_inc(x_1333);
x_1334 = lean_ctor_get(x_1223, 1);
lean_inc(x_1334);
if (lean_is_exclusive(x_1223)) {
 lean_ctor_release(x_1223, 0);
 lean_ctor_release(x_1223, 1);
 x_1335 = x_1223;
} else {
 lean_dec_ref(x_1223);
 x_1335 = lean_box(0);
}
if (lean_is_scalar(x_1335)) {
 x_1336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1336 = x_1335;
}
lean_ctor_set(x_1336, 0, x_1333);
lean_ctor_set(x_1336, 1, x_1334);
return x_1336;
}
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
lean_dec(x_1218);
lean_dec(x_1215);
lean_dec(x_1212);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1197);
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
x_1337 = lean_ctor_get(x_1220, 0);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1220, 1);
lean_inc(x_1338);
if (lean_is_exclusive(x_1220)) {
 lean_ctor_release(x_1220, 0);
 lean_ctor_release(x_1220, 1);
 x_1339 = x_1220;
} else {
 lean_dec_ref(x_1220);
 x_1339 = lean_box(0);
}
if (lean_is_scalar(x_1339)) {
 x_1340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1340 = x_1339;
}
lean_ctor_set(x_1340, 0, x_1337);
lean_ctor_set(x_1340, 1, x_1338);
return x_1340;
}
}
else
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
lean_dec(x_1215);
lean_dec(x_1212);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1197);
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
x_1341 = lean_ctor_get(x_1217, 0);
lean_inc(x_1341);
x_1342 = lean_ctor_get(x_1217, 1);
lean_inc(x_1342);
if (lean_is_exclusive(x_1217)) {
 lean_ctor_release(x_1217, 0);
 lean_ctor_release(x_1217, 1);
 x_1343 = x_1217;
} else {
 lean_dec_ref(x_1217);
 x_1343 = lean_box(0);
}
if (lean_is_scalar(x_1343)) {
 x_1344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1344 = x_1343;
}
lean_ctor_set(x_1344, 0, x_1341);
lean_ctor_set(x_1344, 1, x_1342);
return x_1344;
}
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
lean_dec(x_1212);
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1197);
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
x_1345 = lean_ctor_get(x_1214, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1214, 1);
lean_inc(x_1346);
if (lean_is_exclusive(x_1214)) {
 lean_ctor_release(x_1214, 0);
 lean_ctor_release(x_1214, 1);
 x_1347 = x_1214;
} else {
 lean_dec_ref(x_1214);
 x_1347 = lean_box(0);
}
if (lean_is_scalar(x_1347)) {
 x_1348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1348 = x_1347;
}
lean_ctor_set(x_1348, 0, x_1345);
lean_ctor_set(x_1348, 1, x_1346);
return x_1348;
}
}
else
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
lean_dec(x_1209);
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1197);
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
x_1349 = lean_ctor_get(x_1211, 0);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1211, 1);
lean_inc(x_1350);
if (lean_is_exclusive(x_1211)) {
 lean_ctor_release(x_1211, 0);
 lean_ctor_release(x_1211, 1);
 x_1351 = x_1211;
} else {
 lean_dec_ref(x_1211);
 x_1351 = lean_box(0);
}
if (lean_is_scalar(x_1351)) {
 x_1352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1352 = x_1351;
}
lean_ctor_set(x_1352, 0, x_1349);
lean_ctor_set(x_1352, 1, x_1350);
return x_1352;
}
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
lean_dec(x_1206);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1197);
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
x_1353 = lean_ctor_get(x_1208, 0);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1208, 1);
lean_inc(x_1354);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1355 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1355 = lean_box(0);
}
if (lean_is_scalar(x_1355)) {
 x_1356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1356 = x_1355;
}
lean_ctor_set(x_1356, 0, x_1353);
lean_ctor_set(x_1356, 1, x_1354);
return x_1356;
}
}
else
{
lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1197);
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
x_1357 = lean_ctor_get(x_1205, 0);
lean_inc(x_1357);
x_1358 = lean_ctor_get(x_1205, 1);
lean_inc(x_1358);
if (lean_is_exclusive(x_1205)) {
 lean_ctor_release(x_1205, 0);
 lean_ctor_release(x_1205, 1);
 x_1359 = x_1205;
} else {
 lean_dec_ref(x_1205);
 x_1359 = lean_box(0);
}
if (lean_is_scalar(x_1359)) {
 x_1360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1360 = x_1359;
}
lean_ctor_set(x_1360, 0, x_1357);
lean_ctor_set(x_1360, 1, x_1358);
return x_1360;
}
}
}
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; 
x_1361 = lean_ctor_get(x_16, 0);
x_1362 = lean_ctor_get(x_16, 1);
lean_inc(x_1362);
lean_inc(x_1361);
lean_dec(x_16);
x_1363 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_4, x_5, x_6, x_7, x_8, x_17);
x_1364 = lean_ctor_get(x_1363, 0);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1363, 1);
lean_inc(x_1365);
if (lean_is_exclusive(x_1363)) {
 lean_ctor_release(x_1363, 0);
 lean_ctor_release(x_1363, 1);
 x_1366 = x_1363;
} else {
 lean_dec_ref(x_1363);
 x_1366 = lean_box(0);
}
x_1367 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1364, x_5, x_6, x_7, x_8, x_1365);
lean_dec(x_1364);
x_1368 = lean_ctor_get(x_1367, 0);
lean_inc(x_1368);
if (lean_obj_tag(x_1368) == 0)
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1369 = lean_ctor_get(x_1367, 1);
lean_inc(x_1369);
lean_dec(x_1367);
x_1370 = l_Lean_Elab_Term_mkCalcTrans___closed__5;
x_1371 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(x_1370, x_5, x_6, x_7, x_8, x_1369);
return x_1371;
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1372 = lean_ctor_get(x_1368, 0);
lean_inc(x_1372);
if (lean_is_exclusive(x_1368)) {
 lean_ctor_release(x_1368, 0);
 x_1373 = x_1368;
} else {
 lean_dec_ref(x_1368);
 x_1373 = lean_box(0);
}
x_1374 = lean_ctor_get(x_1372, 1);
lean_inc(x_1374);
x_1375 = lean_ctor_get(x_1367, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1367)) {
 lean_ctor_release(x_1367, 0);
 lean_ctor_release(x_1367, 1);
 x_1376 = x_1367;
} else {
 lean_dec_ref(x_1367);
 x_1376 = lean_box(0);
}
x_1377 = lean_ctor_get(x_1372, 0);
lean_inc(x_1377);
if (lean_is_exclusive(x_1372)) {
 lean_ctor_release(x_1372, 0);
 lean_ctor_release(x_1372, 1);
 x_1378 = x_1372;
} else {
 lean_dec_ref(x_1372);
 x_1378 = lean_box(0);
}
x_1379 = lean_ctor_get(x_1374, 1);
lean_inc(x_1379);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1380 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1380 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_1381 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_19, x_5, x_6, x_7, x_8, x_1375);
if (lean_obj_tag(x_1381) == 0)
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; 
x_1382 = lean_ctor_get(x_1381, 0);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1381, 1);
lean_inc(x_1383);
lean_dec(x_1381);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1377);
x_1384 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1377, x_5, x_6, x_7, x_8, x_1383);
if (lean_obj_tag(x_1384) == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_1384, 0);
lean_inc(x_1385);
x_1386 = lean_ctor_get(x_1384, 1);
lean_inc(x_1386);
lean_dec(x_1384);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1361);
x_1387 = lean_infer_type(x_1361, x_5, x_6, x_7, x_8, x_1386);
if (lean_obj_tag(x_1387) == 0)
{
lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; 
x_1388 = lean_ctor_get(x_1387, 0);
lean_inc(x_1388);
x_1389 = lean_ctor_get(x_1387, 1);
lean_inc(x_1389);
lean_dec(x_1387);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1362);
x_1390 = lean_infer_type(x_1362, x_5, x_6, x_7, x_8, x_1389);
if (lean_obj_tag(x_1390) == 0)
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
x_1391 = lean_ctor_get(x_1390, 0);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_1390, 1);
lean_inc(x_1392);
lean_dec(x_1390);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1379);
x_1393 = lean_infer_type(x_1379, x_5, x_6, x_7, x_8, x_1392);
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
x_1394 = lean_ctor_get(x_1393, 0);
lean_inc(x_1394);
x_1395 = lean_ctor_get(x_1393, 1);
lean_inc(x_1395);
lean_dec(x_1393);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1388);
x_1396 = l_Lean_Meta_getLevel(x_1388, x_5, x_6, x_7, x_8, x_1395);
if (lean_obj_tag(x_1396) == 0)
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
x_1397 = lean_ctor_get(x_1396, 0);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1396, 1);
lean_inc(x_1398);
lean_dec(x_1396);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1391);
x_1399 = l_Lean_Meta_getLevel(x_1391, x_5, x_6, x_7, x_8, x_1398);
if (lean_obj_tag(x_1399) == 0)
{
lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; 
x_1400 = lean_ctor_get(x_1399, 0);
lean_inc(x_1400);
x_1401 = lean_ctor_get(x_1399, 1);
lean_inc(x_1401);
lean_dec(x_1399);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1394);
x_1402 = l_Lean_Meta_getLevel(x_1394, x_5, x_6, x_7, x_8, x_1401);
if (lean_obj_tag(x_1402) == 0)
{
lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; uint8_t x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; 
x_1403 = lean_ctor_get(x_1402, 0);
lean_inc(x_1403);
x_1404 = lean_ctor_get(x_1402, 1);
lean_inc(x_1404);
lean_dec(x_1402);
x_1405 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1404);
x_1406 = lean_ctor_get(x_1405, 0);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1405, 1);
lean_inc(x_1407);
if (lean_is_exclusive(x_1405)) {
 lean_ctor_release(x_1405, 0);
 lean_ctor_release(x_1405, 1);
 x_1408 = x_1405;
} else {
 lean_dec_ref(x_1405);
 x_1408 = lean_box(0);
}
lean_inc(x_1406);
x_1409 = l_Lean_Expr_sort___override(x_1406);
lean_inc(x_1394);
x_1410 = l_Lean_mkArrow(x_1394, x_1409, x_7, x_8, x_1407);
x_1411 = lean_ctor_get(x_1410, 0);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1410, 1);
lean_inc(x_1412);
if (lean_is_exclusive(x_1410)) {
 lean_ctor_release(x_1410, 0);
 lean_ctor_release(x_1410, 1);
 x_1413 = x_1410;
} else {
 lean_dec_ref(x_1410);
 x_1413 = lean_box(0);
}
lean_inc(x_1388);
x_1414 = l_Lean_mkArrow(x_1388, x_1411, x_7, x_8, x_1412);
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1414, 1);
lean_inc(x_1416);
if (lean_is_exclusive(x_1414)) {
 lean_ctor_release(x_1414, 0);
 lean_ctor_release(x_1414, 1);
 x_1417 = x_1414;
} else {
 lean_dec_ref(x_1414);
 x_1417 = lean_box(0);
}
if (lean_is_scalar(x_1373)) {
 x_1418 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1418 = x_1373;
}
lean_ctor_set(x_1418, 0, x_1415);
x_1419 = 0;
x_1420 = lean_box(0);
lean_inc(x_5);
x_1421 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1418, x_1419, x_1420, x_5, x_6, x_7, x_8, x_1416);
x_1422 = lean_ctor_get(x_1421, 0);
lean_inc(x_1422);
x_1423 = lean_ctor_get(x_1421, 1);
lean_inc(x_1423);
if (lean_is_exclusive(x_1421)) {
 lean_ctor_release(x_1421, 0);
 lean_ctor_release(x_1421, 1);
 x_1424 = x_1421;
} else {
 lean_dec_ref(x_1421);
 x_1424 = lean_box(0);
}
x_1425 = lean_box(0);
if (lean_is_scalar(x_1424)) {
 x_1426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1426 = x_1424;
 lean_ctor_set_tag(x_1426, 1);
}
lean_ctor_set(x_1426, 0, x_1403);
lean_ctor_set(x_1426, 1, x_1425);
if (lean_is_scalar(x_1417)) {
 x_1427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1427 = x_1417;
 lean_ctor_set_tag(x_1427, 1);
}
lean_ctor_set(x_1427, 0, x_1400);
lean_ctor_set(x_1427, 1, x_1426);
if (lean_is_scalar(x_1413)) {
 x_1428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1428 = x_1413;
 lean_ctor_set_tag(x_1428, 1);
}
lean_ctor_set(x_1428, 0, x_1397);
lean_ctor_set(x_1428, 1, x_1427);
if (lean_is_scalar(x_1408)) {
 x_1429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1429 = x_1408;
 lean_ctor_set_tag(x_1429, 1);
}
lean_ctor_set(x_1429, 0, x_1406);
lean_ctor_set(x_1429, 1, x_1428);
if (lean_is_scalar(x_1380)) {
 x_1430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1430 = x_1380;
 lean_ctor_set_tag(x_1430, 1);
}
lean_ctor_set(x_1430, 0, x_1385);
lean_ctor_set(x_1430, 1, x_1429);
if (lean_is_scalar(x_1378)) {
 x_1431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1431 = x_1378;
 lean_ctor_set_tag(x_1431, 1);
}
lean_ctor_set(x_1431, 0, x_1382);
lean_ctor_set(x_1431, 1, x_1430);
x_1432 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_1431);
x_1433 = l_Lean_Expr_const___override(x_1432, x_1431);
x_1434 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_1388);
x_1435 = lean_array_push(x_1434, x_1388);
lean_inc(x_1391);
x_1436 = lean_array_push(x_1435, x_1391);
lean_inc(x_1394);
x_1437 = lean_array_push(x_1436, x_1394);
lean_inc(x_19);
x_1438 = lean_array_push(x_1437, x_19);
lean_inc(x_1377);
x_1439 = lean_array_push(x_1438, x_1377);
lean_inc(x_1422);
x_1440 = lean_array_push(x_1439, x_1422);
x_1441 = l_Lean_mkAppN(x_1433, x_1440);
lean_dec(x_1440);
x_1442 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1441);
x_1443 = l_Lean_Meta_trySynthInstance(x_1441, x_1442, x_5, x_6, x_7, x_8, x_1423);
if (lean_obj_tag(x_1443) == 0)
{
lean_object* x_1444; 
x_1444 = lean_ctor_get(x_1443, 0);
lean_inc(x_1444);
if (lean_obj_tag(x_1444) == 1)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
lean_dec(x_1441);
lean_dec(x_1376);
lean_dec(x_1366);
lean_free_object(x_15);
x_1445 = lean_ctor_get(x_1443, 1);
lean_inc(x_1445);
lean_dec(x_1443);
x_1446 = lean_ctor_get(x_1444, 0);
lean_inc(x_1446);
lean_dec(x_1444);
x_1447 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_1448 = l_Lean_Expr_const___override(x_1447, x_1431);
x_1449 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_1450 = lean_array_push(x_1449, x_1388);
x_1451 = lean_array_push(x_1450, x_1391);
x_1452 = lean_array_push(x_1451, x_1394);
x_1453 = lean_array_push(x_1452, x_19);
x_1454 = lean_array_push(x_1453, x_1377);
x_1455 = lean_array_push(x_1454, x_1422);
x_1456 = lean_array_push(x_1455, x_1446);
x_1457 = lean_array_push(x_1456, x_1361);
x_1458 = lean_array_push(x_1457, x_1362);
x_1459 = lean_array_push(x_1458, x_1379);
x_1460 = lean_array_push(x_1459, x_1);
x_1461 = lean_array_push(x_1460, x_3);
x_1462 = l_Lean_mkAppN(x_1448, x_1461);
lean_dec(x_1461);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1462);
x_1463 = lean_infer_type(x_1462, x_5, x_6, x_7, x_8, x_1445);
if (lean_obj_tag(x_1463) == 0)
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
x_1465 = lean_ctor_get(x_1463, 1);
lean_inc(x_1465);
lean_dec(x_1463);
x_1466 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1464, x_5, x_6, x_7, x_8, x_1465);
x_1467 = lean_ctor_get(x_1466, 0);
lean_inc(x_1467);
x_1468 = lean_ctor_get(x_1466, 1);
lean_inc(x_1468);
if (lean_is_exclusive(x_1466)) {
 lean_ctor_release(x_1466, 0);
 lean_ctor_release(x_1466, 1);
 x_1469 = x_1466;
} else {
 lean_dec_ref(x_1466);
 x_1469 = lean_box(0);
}
x_1470 = l_Lean_Expr_headBeta(x_1467);
x_1471 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1470, x_5, x_6, x_7, x_8, x_1468);
x_1472 = lean_ctor_get(x_1471, 0);
lean_inc(x_1472);
if (lean_obj_tag(x_1472) == 0)
{
lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; 
lean_dec(x_1462);
x_1473 = lean_ctor_get(x_1471, 1);
lean_inc(x_1473);
if (lean_is_exclusive(x_1471)) {
 lean_ctor_release(x_1471, 0);
 lean_ctor_release(x_1471, 1);
 x_1474 = x_1471;
} else {
 lean_dec_ref(x_1471);
 x_1474 = lean_box(0);
}
x_1475 = l_Lean_indentExpr(x_1470);
x_1476 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_1474)) {
 x_1477 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1477 = x_1474;
 lean_ctor_set_tag(x_1477, 7);
}
lean_ctor_set(x_1477, 0, x_1476);
lean_ctor_set(x_1477, 1, x_1475);
x_1478 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1469)) {
 x_1479 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1479 = x_1469;
 lean_ctor_set_tag(x_1479, 7);
}
lean_ctor_set(x_1479, 0, x_1477);
lean_ctor_set(x_1479, 1, x_1478);
x_1480 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1479, x_5, x_6, x_7, x_8, x_1473);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1481 = lean_ctor_get(x_1480, 0);
lean_inc(x_1481);
x_1482 = lean_ctor_get(x_1480, 1);
lean_inc(x_1482);
if (lean_is_exclusive(x_1480)) {
 lean_ctor_release(x_1480, 0);
 lean_ctor_release(x_1480, 1);
 x_1483 = x_1480;
} else {
 lean_dec_ref(x_1480);
 x_1483 = lean_box(0);
}
if (lean_is_scalar(x_1483)) {
 x_1484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1484 = x_1483;
}
lean_ctor_set(x_1484, 0, x_1481);
lean_ctor_set(x_1484, 1, x_1482);
return x_1484;
}
else
{
lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; 
lean_dec(x_1472);
lean_dec(x_1469);
x_1485 = lean_ctor_get(x_1471, 1);
lean_inc(x_1485);
lean_dec(x_1471);
x_1486 = lean_box(0);
x_1487 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1462, x_1470, x_1486, x_5, x_6, x_7, x_8, x_1485);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1487;
}
}
else
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
lean_dec(x_1462);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1488 = lean_ctor_get(x_1463, 0);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1463, 1);
lean_inc(x_1489);
if (lean_is_exclusive(x_1463)) {
 lean_ctor_release(x_1463, 0);
 lean_ctor_release(x_1463, 1);
 x_1490 = x_1463;
} else {
 lean_dec_ref(x_1463);
 x_1490 = lean_box(0);
}
if (lean_is_scalar(x_1490)) {
 x_1491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1491 = x_1490;
}
lean_ctor_set(x_1491, 0, x_1488);
lean_ctor_set(x_1491, 1, x_1489);
return x_1491;
}
}
else
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; 
lean_dec(x_1444);
lean_dec(x_1431);
lean_dec(x_1422);
lean_dec(x_1394);
lean_dec(x_1391);
lean_dec(x_1388);
lean_dec(x_1379);
lean_dec(x_1377);
lean_dec(x_1362);
lean_dec(x_1361);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_1492 = lean_ctor_get(x_1443, 1);
lean_inc(x_1492);
lean_dec(x_1443);
x_1493 = l_Lean_indentExpr(x_1441);
x_1494 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
if (lean_is_scalar(x_1376)) {
 x_1495 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1495 = x_1376;
 lean_ctor_set_tag(x_1495, 7);
}
lean_ctor_set(x_1495, 0, x_1494);
lean_ctor_set(x_1495, 1, x_1493);
x_1496 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
if (lean_is_scalar(x_1366)) {
 x_1497 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1497 = x_1366;
 lean_ctor_set_tag(x_1497, 7);
}
lean_ctor_set(x_1497, 0, x_1495);
lean_ctor_set(x_1497, 1, x_1496);
x_1498 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
x_1499 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1499, 0, x_1497);
lean_ctor_set(x_1499, 1, x_1498);
x_1500 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_1500);
lean_ctor_set(x_15, 0, x_1499);
x_1501 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_15, x_5, x_6, x_7, x_8, x_1492);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1501;
}
}
else
{
lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
lean_dec(x_1441);
lean_dec(x_1431);
lean_dec(x_1422);
lean_dec(x_1394);
lean_dec(x_1391);
lean_dec(x_1388);
lean_dec(x_1379);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1502 = lean_ctor_get(x_1443, 0);
lean_inc(x_1502);
x_1503 = lean_ctor_get(x_1443, 1);
lean_inc(x_1503);
if (lean_is_exclusive(x_1443)) {
 lean_ctor_release(x_1443, 0);
 lean_ctor_release(x_1443, 1);
 x_1504 = x_1443;
} else {
 lean_dec_ref(x_1443);
 x_1504 = lean_box(0);
}
if (lean_is_scalar(x_1504)) {
 x_1505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1505 = x_1504;
}
lean_ctor_set(x_1505, 0, x_1502);
lean_ctor_set(x_1505, 1, x_1503);
return x_1505;
}
}
else
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
lean_dec(x_1400);
lean_dec(x_1397);
lean_dec(x_1394);
lean_dec(x_1391);
lean_dec(x_1388);
lean_dec(x_1385);
lean_dec(x_1382);
lean_dec(x_1380);
lean_dec(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1373);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1506 = lean_ctor_get(x_1402, 0);
lean_inc(x_1506);
x_1507 = lean_ctor_get(x_1402, 1);
lean_inc(x_1507);
if (lean_is_exclusive(x_1402)) {
 lean_ctor_release(x_1402, 0);
 lean_ctor_release(x_1402, 1);
 x_1508 = x_1402;
} else {
 lean_dec_ref(x_1402);
 x_1508 = lean_box(0);
}
if (lean_is_scalar(x_1508)) {
 x_1509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1509 = x_1508;
}
lean_ctor_set(x_1509, 0, x_1506);
lean_ctor_set(x_1509, 1, x_1507);
return x_1509;
}
}
else
{
lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
lean_dec(x_1397);
lean_dec(x_1394);
lean_dec(x_1391);
lean_dec(x_1388);
lean_dec(x_1385);
lean_dec(x_1382);
lean_dec(x_1380);
lean_dec(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1373);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1510 = lean_ctor_get(x_1399, 0);
lean_inc(x_1510);
x_1511 = lean_ctor_get(x_1399, 1);
lean_inc(x_1511);
if (lean_is_exclusive(x_1399)) {
 lean_ctor_release(x_1399, 0);
 lean_ctor_release(x_1399, 1);
 x_1512 = x_1399;
} else {
 lean_dec_ref(x_1399);
 x_1512 = lean_box(0);
}
if (lean_is_scalar(x_1512)) {
 x_1513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1513 = x_1512;
}
lean_ctor_set(x_1513, 0, x_1510);
lean_ctor_set(x_1513, 1, x_1511);
return x_1513;
}
}
else
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; 
lean_dec(x_1394);
lean_dec(x_1391);
lean_dec(x_1388);
lean_dec(x_1385);
lean_dec(x_1382);
lean_dec(x_1380);
lean_dec(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1373);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1514 = lean_ctor_get(x_1396, 0);
lean_inc(x_1514);
x_1515 = lean_ctor_get(x_1396, 1);
lean_inc(x_1515);
if (lean_is_exclusive(x_1396)) {
 lean_ctor_release(x_1396, 0);
 lean_ctor_release(x_1396, 1);
 x_1516 = x_1396;
} else {
 lean_dec_ref(x_1396);
 x_1516 = lean_box(0);
}
if (lean_is_scalar(x_1516)) {
 x_1517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1517 = x_1516;
}
lean_ctor_set(x_1517, 0, x_1514);
lean_ctor_set(x_1517, 1, x_1515);
return x_1517;
}
}
else
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; 
lean_dec(x_1391);
lean_dec(x_1388);
lean_dec(x_1385);
lean_dec(x_1382);
lean_dec(x_1380);
lean_dec(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1373);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1518 = lean_ctor_get(x_1393, 0);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1393, 1);
lean_inc(x_1519);
if (lean_is_exclusive(x_1393)) {
 lean_ctor_release(x_1393, 0);
 lean_ctor_release(x_1393, 1);
 x_1520 = x_1393;
} else {
 lean_dec_ref(x_1393);
 x_1520 = lean_box(0);
}
if (lean_is_scalar(x_1520)) {
 x_1521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1521 = x_1520;
}
lean_ctor_set(x_1521, 0, x_1518);
lean_ctor_set(x_1521, 1, x_1519);
return x_1521;
}
}
else
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; 
lean_dec(x_1388);
lean_dec(x_1385);
lean_dec(x_1382);
lean_dec(x_1380);
lean_dec(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1373);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1522 = lean_ctor_get(x_1390, 0);
lean_inc(x_1522);
x_1523 = lean_ctor_get(x_1390, 1);
lean_inc(x_1523);
if (lean_is_exclusive(x_1390)) {
 lean_ctor_release(x_1390, 0);
 lean_ctor_release(x_1390, 1);
 x_1524 = x_1390;
} else {
 lean_dec_ref(x_1390);
 x_1524 = lean_box(0);
}
if (lean_is_scalar(x_1524)) {
 x_1525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1525 = x_1524;
}
lean_ctor_set(x_1525, 0, x_1522);
lean_ctor_set(x_1525, 1, x_1523);
return x_1525;
}
}
else
{
lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; 
lean_dec(x_1385);
lean_dec(x_1382);
lean_dec(x_1380);
lean_dec(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1373);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1526 = lean_ctor_get(x_1387, 0);
lean_inc(x_1526);
x_1527 = lean_ctor_get(x_1387, 1);
lean_inc(x_1527);
if (lean_is_exclusive(x_1387)) {
 lean_ctor_release(x_1387, 0);
 lean_ctor_release(x_1387, 1);
 x_1528 = x_1387;
} else {
 lean_dec_ref(x_1387);
 x_1528 = lean_box(0);
}
if (lean_is_scalar(x_1528)) {
 x_1529 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1529 = x_1528;
}
lean_ctor_set(x_1529, 0, x_1526);
lean_ctor_set(x_1529, 1, x_1527);
return x_1529;
}
}
else
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; 
lean_dec(x_1382);
lean_dec(x_1380);
lean_dec(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1373);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1530 = lean_ctor_get(x_1384, 0);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_1384, 1);
lean_inc(x_1531);
if (lean_is_exclusive(x_1384)) {
 lean_ctor_release(x_1384, 0);
 lean_ctor_release(x_1384, 1);
 x_1532 = x_1384;
} else {
 lean_dec_ref(x_1384);
 x_1532 = lean_box(0);
}
if (lean_is_scalar(x_1532)) {
 x_1533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1533 = x_1532;
}
lean_ctor_set(x_1533, 0, x_1530);
lean_ctor_set(x_1533, 1, x_1531);
return x_1533;
}
}
else
{
lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; 
lean_dec(x_1380);
lean_dec(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1376);
lean_dec(x_1373);
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_1361);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1534 = lean_ctor_get(x_1381, 0);
lean_inc(x_1534);
x_1535 = lean_ctor_get(x_1381, 1);
lean_inc(x_1535);
if (lean_is_exclusive(x_1381)) {
 lean_ctor_release(x_1381, 0);
 lean_ctor_release(x_1381, 1);
 x_1536 = x_1381;
} else {
 lean_dec_ref(x_1381);
 x_1536 = lean_box(0);
}
if (lean_is_scalar(x_1536)) {
 x_1537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1537 = x_1536;
}
lean_ctor_set(x_1537, 0, x_1534);
lean_ctor_set(x_1537, 1, x_1535);
return x_1537;
}
}
}
}
else
{
lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; 
x_1538 = lean_ctor_get(x_15, 0);
lean_inc(x_1538);
lean_dec(x_15);
x_1539 = lean_ctor_get(x_16, 0);
lean_inc(x_1539);
x_1540 = lean_ctor_get(x_16, 1);
lean_inc(x_1540);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_1541 = x_16;
} else {
 lean_dec_ref(x_16);
 x_1541 = lean_box(0);
}
x_1542 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_4, x_5, x_6, x_7, x_8, x_17);
x_1543 = lean_ctor_get(x_1542, 0);
lean_inc(x_1543);
x_1544 = lean_ctor_get(x_1542, 1);
lean_inc(x_1544);
if (lean_is_exclusive(x_1542)) {
 lean_ctor_release(x_1542, 0);
 lean_ctor_release(x_1542, 1);
 x_1545 = x_1542;
} else {
 lean_dec_ref(x_1542);
 x_1545 = lean_box(0);
}
x_1546 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1543, x_5, x_6, x_7, x_8, x_1544);
lean_dec(x_1543);
x_1547 = lean_ctor_get(x_1546, 0);
lean_inc(x_1547);
if (lean_obj_tag(x_1547) == 0)
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_3);
lean_dec(x_1);
x_1548 = lean_ctor_get(x_1546, 1);
lean_inc(x_1548);
lean_dec(x_1546);
x_1549 = l_Lean_Elab_Term_mkCalcTrans___closed__5;
x_1550 = l_panic___at_Lean_Elab_Term_mkCalcTrans___spec__1(x_1549, x_5, x_6, x_7, x_8, x_1548);
return x_1550;
}
else
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
x_1551 = lean_ctor_get(x_1547, 0);
lean_inc(x_1551);
if (lean_is_exclusive(x_1547)) {
 lean_ctor_release(x_1547, 0);
 x_1552 = x_1547;
} else {
 lean_dec_ref(x_1547);
 x_1552 = lean_box(0);
}
x_1553 = lean_ctor_get(x_1551, 1);
lean_inc(x_1553);
x_1554 = lean_ctor_get(x_1546, 1);
lean_inc(x_1554);
if (lean_is_exclusive(x_1546)) {
 lean_ctor_release(x_1546, 0);
 lean_ctor_release(x_1546, 1);
 x_1555 = x_1546;
} else {
 lean_dec_ref(x_1546);
 x_1555 = lean_box(0);
}
x_1556 = lean_ctor_get(x_1551, 0);
lean_inc(x_1556);
if (lean_is_exclusive(x_1551)) {
 lean_ctor_release(x_1551, 0);
 lean_ctor_release(x_1551, 1);
 x_1557 = x_1551;
} else {
 lean_dec_ref(x_1551);
 x_1557 = lean_box(0);
}
x_1558 = lean_ctor_get(x_1553, 1);
lean_inc(x_1558);
if (lean_is_exclusive(x_1553)) {
 lean_ctor_release(x_1553, 0);
 lean_ctor_release(x_1553, 1);
 x_1559 = x_1553;
} else {
 lean_dec_ref(x_1553);
 x_1559 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1538);
x_1560 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1538, x_5, x_6, x_7, x_8, x_1554);
if (lean_obj_tag(x_1560) == 0)
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
x_1561 = lean_ctor_get(x_1560, 0);
lean_inc(x_1561);
x_1562 = lean_ctor_get(x_1560, 1);
lean_inc(x_1562);
lean_dec(x_1560);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1556);
x_1563 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1556, x_5, x_6, x_7, x_8, x_1562);
if (lean_obj_tag(x_1563) == 0)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; 
x_1564 = lean_ctor_get(x_1563, 0);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1563, 1);
lean_inc(x_1565);
lean_dec(x_1563);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1539);
x_1566 = lean_infer_type(x_1539, x_5, x_6, x_7, x_8, x_1565);
if (lean_obj_tag(x_1566) == 0)
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1567 = lean_ctor_get(x_1566, 0);
lean_inc(x_1567);
x_1568 = lean_ctor_get(x_1566, 1);
lean_inc(x_1568);
lean_dec(x_1566);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1540);
x_1569 = lean_infer_type(x_1540, x_5, x_6, x_7, x_8, x_1568);
if (lean_obj_tag(x_1569) == 0)
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; 
x_1570 = lean_ctor_get(x_1569, 0);
lean_inc(x_1570);
x_1571 = lean_ctor_get(x_1569, 1);
lean_inc(x_1571);
lean_dec(x_1569);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1558);
x_1572 = lean_infer_type(x_1558, x_5, x_6, x_7, x_8, x_1571);
if (lean_obj_tag(x_1572) == 0)
{
lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; 
x_1573 = lean_ctor_get(x_1572, 0);
lean_inc(x_1573);
x_1574 = lean_ctor_get(x_1572, 1);
lean_inc(x_1574);
lean_dec(x_1572);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1567);
x_1575 = l_Lean_Meta_getLevel(x_1567, x_5, x_6, x_7, x_8, x_1574);
if (lean_obj_tag(x_1575) == 0)
{
lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; 
x_1576 = lean_ctor_get(x_1575, 0);
lean_inc(x_1576);
x_1577 = lean_ctor_get(x_1575, 1);
lean_inc(x_1577);
lean_dec(x_1575);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1570);
x_1578 = l_Lean_Meta_getLevel(x_1570, x_5, x_6, x_7, x_8, x_1577);
if (lean_obj_tag(x_1578) == 0)
{
lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
x_1579 = lean_ctor_get(x_1578, 0);
lean_inc(x_1579);
x_1580 = lean_ctor_get(x_1578, 1);
lean_inc(x_1580);
lean_dec(x_1578);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1573);
x_1581 = l_Lean_Meta_getLevel(x_1573, x_5, x_6, x_7, x_8, x_1580);
if (lean_obj_tag(x_1581) == 0)
{
lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; uint8_t x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
x_1582 = lean_ctor_get(x_1581, 0);
lean_inc(x_1582);
x_1583 = lean_ctor_get(x_1581, 1);
lean_inc(x_1583);
lean_dec(x_1581);
x_1584 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1583);
x_1585 = lean_ctor_get(x_1584, 0);
lean_inc(x_1585);
x_1586 = lean_ctor_get(x_1584, 1);
lean_inc(x_1586);
if (lean_is_exclusive(x_1584)) {
 lean_ctor_release(x_1584, 0);
 lean_ctor_release(x_1584, 1);
 x_1587 = x_1584;
} else {
 lean_dec_ref(x_1584);
 x_1587 = lean_box(0);
}
lean_inc(x_1585);
x_1588 = l_Lean_Expr_sort___override(x_1585);
lean_inc(x_1573);
x_1589 = l_Lean_mkArrow(x_1573, x_1588, x_7, x_8, x_1586);
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
lean_inc(x_1567);
x_1593 = l_Lean_mkArrow(x_1567, x_1590, x_7, x_8, x_1591);
x_1594 = lean_ctor_get(x_1593, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1593, 1);
lean_inc(x_1595);
if (lean_is_exclusive(x_1593)) {
 lean_ctor_release(x_1593, 0);
 lean_ctor_release(x_1593, 1);
 x_1596 = x_1593;
} else {
 lean_dec_ref(x_1593);
 x_1596 = lean_box(0);
}
if (lean_is_scalar(x_1552)) {
 x_1597 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1597 = x_1552;
}
lean_ctor_set(x_1597, 0, x_1594);
x_1598 = 0;
x_1599 = lean_box(0);
lean_inc(x_5);
x_1600 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1597, x_1598, x_1599, x_5, x_6, x_7, x_8, x_1595);
x_1601 = lean_ctor_get(x_1600, 0);
lean_inc(x_1601);
x_1602 = lean_ctor_get(x_1600, 1);
lean_inc(x_1602);
if (lean_is_exclusive(x_1600)) {
 lean_ctor_release(x_1600, 0);
 lean_ctor_release(x_1600, 1);
 x_1603 = x_1600;
} else {
 lean_dec_ref(x_1600);
 x_1603 = lean_box(0);
}
x_1604 = lean_box(0);
if (lean_is_scalar(x_1603)) {
 x_1605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1605 = x_1603;
 lean_ctor_set_tag(x_1605, 1);
}
lean_ctor_set(x_1605, 0, x_1582);
lean_ctor_set(x_1605, 1, x_1604);
if (lean_is_scalar(x_1596)) {
 x_1606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1606 = x_1596;
 lean_ctor_set_tag(x_1606, 1);
}
lean_ctor_set(x_1606, 0, x_1579);
lean_ctor_set(x_1606, 1, x_1605);
if (lean_is_scalar(x_1592)) {
 x_1607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1607 = x_1592;
 lean_ctor_set_tag(x_1607, 1);
}
lean_ctor_set(x_1607, 0, x_1576);
lean_ctor_set(x_1607, 1, x_1606);
if (lean_is_scalar(x_1587)) {
 x_1608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1608 = x_1587;
 lean_ctor_set_tag(x_1608, 1);
}
lean_ctor_set(x_1608, 0, x_1585);
lean_ctor_set(x_1608, 1, x_1607);
if (lean_is_scalar(x_1559)) {
 x_1609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1609 = x_1559;
 lean_ctor_set_tag(x_1609, 1);
}
lean_ctor_set(x_1609, 0, x_1564);
lean_ctor_set(x_1609, 1, x_1608);
if (lean_is_scalar(x_1557)) {
 x_1610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1610 = x_1557;
 lean_ctor_set_tag(x_1610, 1);
}
lean_ctor_set(x_1610, 0, x_1561);
lean_ctor_set(x_1610, 1, x_1609);
x_1611 = l_Lean_Elab_Term_mkCalcTrans___closed__7;
lean_inc(x_1610);
x_1612 = l_Lean_Expr_const___override(x_1611, x_1610);
x_1613 = l_Lean_Elab_Term_mkCalcTrans___closed__8;
lean_inc(x_1567);
x_1614 = lean_array_push(x_1613, x_1567);
lean_inc(x_1570);
x_1615 = lean_array_push(x_1614, x_1570);
lean_inc(x_1573);
x_1616 = lean_array_push(x_1615, x_1573);
lean_inc(x_1538);
x_1617 = lean_array_push(x_1616, x_1538);
lean_inc(x_1556);
x_1618 = lean_array_push(x_1617, x_1556);
lean_inc(x_1601);
x_1619 = lean_array_push(x_1618, x_1601);
x_1620 = l_Lean_mkAppN(x_1612, x_1619);
lean_dec(x_1619);
x_1621 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1620);
x_1622 = l_Lean_Meta_trySynthInstance(x_1620, x_1621, x_5, x_6, x_7, x_8, x_1602);
if (lean_obj_tag(x_1622) == 0)
{
lean_object* x_1623; 
x_1623 = lean_ctor_get(x_1622, 0);
lean_inc(x_1623);
if (lean_obj_tag(x_1623) == 1)
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
lean_dec(x_1620);
lean_dec(x_1555);
lean_dec(x_1545);
lean_dec(x_1541);
x_1624 = lean_ctor_get(x_1622, 1);
lean_inc(x_1624);
lean_dec(x_1622);
x_1625 = lean_ctor_get(x_1623, 0);
lean_inc(x_1625);
lean_dec(x_1623);
x_1626 = l_Lean_Elab_Term_mkCalcTrans___closed__15;
x_1627 = l_Lean_Expr_const___override(x_1626, x_1610);
x_1628 = l_Lean_Elab_Term_mkCalcTrans___closed__16;
x_1629 = lean_array_push(x_1628, x_1567);
x_1630 = lean_array_push(x_1629, x_1570);
x_1631 = lean_array_push(x_1630, x_1573);
x_1632 = lean_array_push(x_1631, x_1538);
x_1633 = lean_array_push(x_1632, x_1556);
x_1634 = lean_array_push(x_1633, x_1601);
x_1635 = lean_array_push(x_1634, x_1625);
x_1636 = lean_array_push(x_1635, x_1539);
x_1637 = lean_array_push(x_1636, x_1540);
x_1638 = lean_array_push(x_1637, x_1558);
x_1639 = lean_array_push(x_1638, x_1);
x_1640 = lean_array_push(x_1639, x_3);
x_1641 = l_Lean_mkAppN(x_1627, x_1640);
lean_dec(x_1640);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1641);
x_1642 = lean_infer_type(x_1641, x_5, x_6, x_7, x_8, x_1624);
if (lean_obj_tag(x_1642) == 0)
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; 
x_1643 = lean_ctor_get(x_1642, 0);
lean_inc(x_1643);
x_1644 = lean_ctor_get(x_1642, 1);
lean_inc(x_1644);
lean_dec(x_1642);
x_1645 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1643, x_5, x_6, x_7, x_8, x_1644);
x_1646 = lean_ctor_get(x_1645, 0);
lean_inc(x_1646);
x_1647 = lean_ctor_get(x_1645, 1);
lean_inc(x_1647);
if (lean_is_exclusive(x_1645)) {
 lean_ctor_release(x_1645, 0);
 lean_ctor_release(x_1645, 1);
 x_1648 = x_1645;
} else {
 lean_dec_ref(x_1645);
 x_1648 = lean_box(0);
}
x_1649 = l_Lean_Expr_headBeta(x_1646);
x_1650 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1649, x_5, x_6, x_7, x_8, x_1647);
x_1651 = lean_ctor_get(x_1650, 0);
lean_inc(x_1651);
if (lean_obj_tag(x_1651) == 0)
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; 
lean_dec(x_1641);
x_1652 = lean_ctor_get(x_1650, 1);
lean_inc(x_1652);
if (lean_is_exclusive(x_1650)) {
 lean_ctor_release(x_1650, 0);
 lean_ctor_release(x_1650, 1);
 x_1653 = x_1650;
} else {
 lean_dec_ref(x_1650);
 x_1653 = lean_box(0);
}
x_1654 = l_Lean_indentExpr(x_1649);
x_1655 = l_Lean_Elab_Term_mkCalcTrans___closed__18;
if (lean_is_scalar(x_1653)) {
 x_1656 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1656 = x_1653;
 lean_ctor_set_tag(x_1656, 7);
}
lean_ctor_set(x_1656, 0, x_1655);
lean_ctor_set(x_1656, 1, x_1654);
x_1657 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
if (lean_is_scalar(x_1648)) {
 x_1658 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1658 = x_1648;
 lean_ctor_set_tag(x_1658, 7);
}
lean_ctor_set(x_1658, 0, x_1656);
lean_ctor_set(x_1658, 1, x_1657);
x_1659 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1658, x_5, x_6, x_7, x_8, x_1652);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1660 = lean_ctor_get(x_1659, 0);
lean_inc(x_1660);
x_1661 = lean_ctor_get(x_1659, 1);
lean_inc(x_1661);
if (lean_is_exclusive(x_1659)) {
 lean_ctor_release(x_1659, 0);
 lean_ctor_release(x_1659, 1);
 x_1662 = x_1659;
} else {
 lean_dec_ref(x_1659);
 x_1662 = lean_box(0);
}
if (lean_is_scalar(x_1662)) {
 x_1663 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1663 = x_1662;
}
lean_ctor_set(x_1663, 0, x_1660);
lean_ctor_set(x_1663, 1, x_1661);
return x_1663;
}
else
{
lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
lean_dec(x_1651);
lean_dec(x_1648);
x_1664 = lean_ctor_get(x_1650, 1);
lean_inc(x_1664);
lean_dec(x_1650);
x_1665 = lean_box(0);
x_1666 = l_Lean_Elab_Term_mkCalcTrans___lambda__1(x_1641, x_1649, x_1665, x_5, x_6, x_7, x_8, x_1664);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1666;
}
}
else
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; 
lean_dec(x_1641);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1667 = lean_ctor_get(x_1642, 0);
lean_inc(x_1667);
x_1668 = lean_ctor_get(x_1642, 1);
lean_inc(x_1668);
if (lean_is_exclusive(x_1642)) {
 lean_ctor_release(x_1642, 0);
 lean_ctor_release(x_1642, 1);
 x_1669 = x_1642;
} else {
 lean_dec_ref(x_1642);
 x_1669 = lean_box(0);
}
if (lean_is_scalar(x_1669)) {
 x_1670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1670 = x_1669;
}
lean_ctor_set(x_1670, 0, x_1667);
lean_ctor_set(x_1670, 1, x_1668);
return x_1670;
}
}
else
{
lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
lean_dec(x_1623);
lean_dec(x_1610);
lean_dec(x_1601);
lean_dec(x_1573);
lean_dec(x_1570);
lean_dec(x_1567);
lean_dec(x_1558);
lean_dec(x_1556);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_3);
lean_dec(x_1);
x_1671 = lean_ctor_get(x_1622, 1);
lean_inc(x_1671);
lean_dec(x_1622);
x_1672 = l_Lean_indentExpr(x_1620);
x_1673 = l_Lean_Elab_Term_mkCalcTrans___closed__10;
if (lean_is_scalar(x_1555)) {
 x_1674 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1674 = x_1555;
 lean_ctor_set_tag(x_1674, 7);
}
lean_ctor_set(x_1674, 0, x_1673);
lean_ctor_set(x_1674, 1, x_1672);
x_1675 = l_Lean_Elab_Term_mkCalcTrans___closed__12;
if (lean_is_scalar(x_1545)) {
 x_1676 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1676 = x_1545;
 lean_ctor_set_tag(x_1676, 7);
}
lean_ctor_set(x_1676, 0, x_1674);
lean_ctor_set(x_1676, 1, x_1675);
x_1677 = l_Lean_Elab_Term_mkCalcTrans___closed__13;
if (lean_is_scalar(x_1541)) {
 x_1678 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1678 = x_1541;
 lean_ctor_set_tag(x_1678, 7);
}
lean_ctor_set(x_1678, 0, x_1676);
lean_ctor_set(x_1678, 1, x_1677);
x_1679 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lambda__1___closed__4;
x_1680 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1680, 0, x_1678);
lean_ctor_set(x_1680, 1, x_1679);
x_1681 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_1680, x_5, x_6, x_7, x_8, x_1671);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1681;
}
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
lean_dec(x_1620);
lean_dec(x_1610);
lean_dec(x_1601);
lean_dec(x_1573);
lean_dec(x_1570);
lean_dec(x_1567);
lean_dec(x_1558);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1682 = lean_ctor_get(x_1622, 0);
lean_inc(x_1682);
x_1683 = lean_ctor_get(x_1622, 1);
lean_inc(x_1683);
if (lean_is_exclusive(x_1622)) {
 lean_ctor_release(x_1622, 0);
 lean_ctor_release(x_1622, 1);
 x_1684 = x_1622;
} else {
 lean_dec_ref(x_1622);
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
lean_dec(x_1579);
lean_dec(x_1576);
lean_dec(x_1573);
lean_dec(x_1570);
lean_dec(x_1567);
lean_dec(x_1564);
lean_dec(x_1561);
lean_dec(x_1559);
lean_dec(x_1558);
lean_dec(x_1557);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1552);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1686 = lean_ctor_get(x_1581, 0);
lean_inc(x_1686);
x_1687 = lean_ctor_get(x_1581, 1);
lean_inc(x_1687);
if (lean_is_exclusive(x_1581)) {
 lean_ctor_release(x_1581, 0);
 lean_ctor_release(x_1581, 1);
 x_1688 = x_1581;
} else {
 lean_dec_ref(x_1581);
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
lean_dec(x_1576);
lean_dec(x_1573);
lean_dec(x_1570);
lean_dec(x_1567);
lean_dec(x_1564);
lean_dec(x_1561);
lean_dec(x_1559);
lean_dec(x_1558);
lean_dec(x_1557);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1552);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1690 = lean_ctor_get(x_1578, 0);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1578, 1);
lean_inc(x_1691);
if (lean_is_exclusive(x_1578)) {
 lean_ctor_release(x_1578, 0);
 lean_ctor_release(x_1578, 1);
 x_1692 = x_1578;
} else {
 lean_dec_ref(x_1578);
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
lean_dec(x_1573);
lean_dec(x_1570);
lean_dec(x_1567);
lean_dec(x_1564);
lean_dec(x_1561);
lean_dec(x_1559);
lean_dec(x_1558);
lean_dec(x_1557);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1552);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1694 = lean_ctor_get(x_1575, 0);
lean_inc(x_1694);
x_1695 = lean_ctor_get(x_1575, 1);
lean_inc(x_1695);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1696 = x_1575;
} else {
 lean_dec_ref(x_1575);
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
lean_dec(x_1570);
lean_dec(x_1567);
lean_dec(x_1564);
lean_dec(x_1561);
lean_dec(x_1559);
lean_dec(x_1558);
lean_dec(x_1557);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1552);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1698 = lean_ctor_get(x_1572, 0);
lean_inc(x_1698);
x_1699 = lean_ctor_get(x_1572, 1);
lean_inc(x_1699);
if (lean_is_exclusive(x_1572)) {
 lean_ctor_release(x_1572, 0);
 lean_ctor_release(x_1572, 1);
 x_1700 = x_1572;
} else {
 lean_dec_ref(x_1572);
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
lean_dec(x_1567);
lean_dec(x_1564);
lean_dec(x_1561);
lean_dec(x_1559);
lean_dec(x_1558);
lean_dec(x_1557);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1552);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1702 = lean_ctor_get(x_1569, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1569, 1);
lean_inc(x_1703);
if (lean_is_exclusive(x_1569)) {
 lean_ctor_release(x_1569, 0);
 lean_ctor_release(x_1569, 1);
 x_1704 = x_1569;
} else {
 lean_dec_ref(x_1569);
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
else
{
lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; 
lean_dec(x_1564);
lean_dec(x_1561);
lean_dec(x_1559);
lean_dec(x_1558);
lean_dec(x_1557);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1552);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1706 = lean_ctor_get(x_1566, 0);
lean_inc(x_1706);
x_1707 = lean_ctor_get(x_1566, 1);
lean_inc(x_1707);
if (lean_is_exclusive(x_1566)) {
 lean_ctor_release(x_1566, 0);
 lean_ctor_release(x_1566, 1);
 x_1708 = x_1566;
} else {
 lean_dec_ref(x_1566);
 x_1708 = lean_box(0);
}
if (lean_is_scalar(x_1708)) {
 x_1709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1709 = x_1708;
}
lean_ctor_set(x_1709, 0, x_1706);
lean_ctor_set(x_1709, 1, x_1707);
return x_1709;
}
}
else
{
lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; 
lean_dec(x_1561);
lean_dec(x_1559);
lean_dec(x_1558);
lean_dec(x_1557);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1552);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1710 = lean_ctor_get(x_1563, 0);
lean_inc(x_1710);
x_1711 = lean_ctor_get(x_1563, 1);
lean_inc(x_1711);
if (lean_is_exclusive(x_1563)) {
 lean_ctor_release(x_1563, 0);
 lean_ctor_release(x_1563, 1);
 x_1712 = x_1563;
} else {
 lean_dec_ref(x_1563);
 x_1712 = lean_box(0);
}
if (lean_is_scalar(x_1712)) {
 x_1713 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1713 = x_1712;
}
lean_ctor_set(x_1713, 0, x_1710);
lean_ctor_set(x_1713, 1, x_1711);
return x_1713;
}
}
else
{
lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; 
lean_dec(x_1559);
lean_dec(x_1558);
lean_dec(x_1557);
lean_dec(x_1556);
lean_dec(x_1555);
lean_dec(x_1552);
lean_dec(x_1545);
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1539);
lean_dec(x_1538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1714 = lean_ctor_get(x_1560, 0);
lean_inc(x_1714);
x_1715 = lean_ctor_get(x_1560, 1);
lean_inc(x_1715);
if (lean_is_exclusive(x_1560)) {
 lean_ctor_release(x_1560, 0);
 lean_ctor_release(x_1560, 1);
 x_1716 = x_1560;
} else {
 lean_dec_ref(x_1560);
 x_1716 = lean_box(0);
}
if (lean_is_scalar(x_1716)) {
 x_1717 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1717 = x_1716;
}
lean_ctor_set(x_1717, 0, x_1714);
lean_ctor_set(x_1717, 1, x_1715);
return x_1717;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_array_get_size(x_15);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1(x_2, x_18, x_19, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_1, 2, x_24);
lean_ctor_set(x_22, 0, x_1);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_1, 2, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_30);
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_1);
lean_dec(x_14);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = 0;
x_44 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__1(x_2, x_42, x_43, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_12);
lean_ctor_set(x_51, 2, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
if (lean_is_scalar(x_47)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_47;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_39);
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
case 1:
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_12, 0);
lean_inc(x_58);
switch (lean_obj_tag(x_58)) {
case 0:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_1);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_1, 0);
x_61 = lean_ctor_get(x_1, 2);
x_62 = lean_ctor_get(x_1, 1);
lean_dec(x_62);
x_63 = lean_array_get_size(x_61);
x_64 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_65 = 0;
x_66 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2(x_2, x_64, x_65, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_ctor_set(x_1, 2, x_70);
lean_ctor_set(x_68, 0, x_1);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_68, 0);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_68);
lean_ctor_set(x_1, 2, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_66, 0, x_73);
return x_66;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_66);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_76);
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
lean_dec(x_60);
lean_dec(x_12);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_1, 0);
x_86 = lean_ctor_get(x_1, 2);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_1);
x_87 = lean_array_get_size(x_86);
x_88 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_89 = 0;
x_90 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__2(x_2, x_88, x_89, x_86, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_85);
lean_ctor_set(x_97, 1, x_12);
lean_ctor_set(x_97, 2, x_94);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_93;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_92);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_85);
lean_dec(x_12);
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_90, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_102 = x_90;
} else {
 lean_dec_ref(x_90);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
case 1:
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_58, 0);
lean_inc(x_104);
switch (lean_obj_tag(x_104)) {
case 0:
{
uint8_t x_105; 
lean_dec(x_58);
x_105 = !lean_is_exclusive(x_1);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_1, 0);
x_107 = lean_ctor_get(x_1, 2);
x_108 = lean_ctor_get(x_1, 1);
lean_dec(x_108);
x_109 = lean_array_get_size(x_107);
x_110 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_111 = 0;
x_112 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3(x_2, x_110, x_111, x_107, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_ctor_set(x_1, 2, x_116);
lean_ctor_set(x_114, 0, x_1);
return x_112;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_114, 0);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_114);
lean_ctor_set(x_1, 2, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_1);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_112, 0, x_119);
return x_112;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_112, 0);
x_121 = lean_ctor_get(x_112, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_112);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_122);
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_121);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_free_object(x_1);
lean_dec(x_106);
lean_dec(x_12);
x_127 = !lean_is_exclusive(x_112);
if (x_127 == 0)
{
return x_112;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_112, 0);
x_129 = lean_ctor_get(x_112, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_112);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; size_t x_134; size_t x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_1, 0);
x_132 = lean_ctor_get(x_1, 2);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_1);
x_133 = lean_array_get_size(x_132);
x_134 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_135 = 0;
x_136 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__3(x_2, x_134, x_135, x_132, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_142 = x_137;
} else {
 lean_dec_ref(x_137);
 x_142 = lean_box(0);
}
x_143 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_143, 0, x_131);
lean_ctor_set(x_143, 1, x_12);
lean_ctor_set(x_143, 2, x_140);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_139;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_138);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_131);
lean_dec(x_12);
x_146 = lean_ctor_get(x_136, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_136, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_148 = x_136;
} else {
 lean_dec_ref(x_136);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
case 1:
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_104, 0);
lean_inc(x_150);
switch (lean_obj_tag(x_150)) {
case 0:
{
uint8_t x_151; 
lean_dec(x_104);
lean_dec(x_58);
x_151 = !lean_is_exclusive(x_1);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; size_t x_156; size_t x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_1, 0);
x_153 = lean_ctor_get(x_1, 2);
x_154 = lean_ctor_get(x_1, 1);
lean_dec(x_154);
x_155 = lean_array_get_size(x_153);
x_156 = lean_usize_of_nat(x_155);
lean_dec(x_155);
x_157 = 0;
x_158 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4(x_2, x_156, x_157, x_153, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_160, 0);
lean_ctor_set(x_1, 2, x_162);
lean_ctor_set(x_160, 0, x_1);
return x_158;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_160, 0);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_160);
lean_ctor_set(x_1, 2, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_170 = x_166;
} else {
 lean_dec_ref(x_166);
 x_170 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_168);
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_169);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
}
else
{
uint8_t x_173; 
lean_free_object(x_1);
lean_dec(x_152);
lean_dec(x_12);
x_173 = !lean_is_exclusive(x_158);
if (x_173 == 0)
{
return x_158;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_158, 0);
x_175 = lean_ctor_get(x_158, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_158);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; size_t x_180; size_t x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_1, 0);
x_178 = lean_ctor_get(x_1, 2);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_1);
x_179 = lean_array_get_size(x_178);
x_180 = lean_usize_of_nat(x_179);
lean_dec(x_179);
x_181 = 0;
x_182 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__4(x_2, x_180, x_181, x_178, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_188 = x_183;
} else {
 lean_dec_ref(x_183);
 x_188 = lean_box(0);
}
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_177);
lean_ctor_set(x_189, 1, x_12);
lean_ctor_set(x_189, 2, x_186);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
if (lean_is_scalar(x_185)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_185;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_184);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_177);
lean_dec(x_12);
x_192 = lean_ctor_get(x_182, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_182, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_194 = x_182;
} else {
 lean_dec_ref(x_182);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
case 1:
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_150, 0);
lean_inc(x_196);
switch (lean_obj_tag(x_196)) {
case 0:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_197 = lean_ctor_get(x_1, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_1, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_12, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_58, 1);
lean_inc(x_200);
lean_dec(x_58);
x_201 = lean_ctor_get(x_104, 1);
lean_inc(x_201);
lean_dec(x_104);
x_202 = lean_ctor_get(x_150, 1);
lean_inc(x_202);
lean_dec(x_150);
x_203 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__1;
x_204 = lean_string_dec_eq(x_202, x_203);
lean_dec(x_202);
if (x_204 == 0)
{
uint8_t x_205; 
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
x_205 = !lean_is_exclusive(x_1);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; size_t x_210; size_t x_211; lean_object* x_212; 
x_206 = lean_ctor_get(x_1, 2);
lean_dec(x_206);
x_207 = lean_ctor_get(x_1, 1);
lean_dec(x_207);
x_208 = lean_ctor_get(x_1, 0);
lean_dec(x_208);
x_209 = lean_array_get_size(x_198);
x_210 = lean_usize_of_nat(x_209);
lean_dec(x_209);
x_211 = 0;
x_212 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5(x_2, x_210, x_211, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_214, 0);
lean_ctor_set(x_1, 2, x_216);
lean_ctor_set(x_214, 0, x_1);
return x_212;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_214, 0);
x_218 = lean_ctor_get(x_214, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_214);
lean_ctor_set(x_1, 2, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_1);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_212, 0, x_219);
return x_212;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_220 = lean_ctor_get(x_212, 0);
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_212);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_224 = x_220;
} else {
 lean_dec_ref(x_220);
 x_224 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_222);
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_1);
lean_ctor_set(x_225, 1, x_223);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_221);
return x_226;
}
}
else
{
uint8_t x_227; 
lean_free_object(x_1);
lean_dec(x_197);
lean_dec(x_12);
x_227 = !lean_is_exclusive(x_212);
if (x_227 == 0)
{
return x_212;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_212, 0);
x_229 = lean_ctor_get(x_212, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_212);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
else
{
lean_object* x_231; size_t x_232; size_t x_233; lean_object* x_234; 
lean_dec(x_1);
x_231 = lean_array_get_size(x_198);
x_232 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_233 = 0;
x_234 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__5(x_2, x_232, x_233, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_240 = x_235;
} else {
 lean_dec_ref(x_235);
 x_240 = lean_box(0);
}
x_241 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_241, 0, x_197);
lean_ctor_set(x_241, 1, x_12);
lean_ctor_set(x_241, 2, x_238);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_239);
if (lean_is_scalar(x_237)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_237;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_236);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_197);
lean_dec(x_12);
x_244 = lean_ctor_get(x_234, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_234, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_246 = x_234;
} else {
 lean_dec_ref(x_234);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
}
else
{
lean_object* x_248; uint8_t x_249; 
lean_dec(x_12);
x_248 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__2;
x_249 = lean_string_dec_eq(x_201, x_248);
if (x_249 == 0)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_1);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; size_t x_259; size_t x_260; lean_object* x_261; 
x_251 = lean_ctor_get(x_1, 2);
lean_dec(x_251);
x_252 = lean_ctor_get(x_1, 1);
lean_dec(x_252);
x_253 = lean_ctor_get(x_1, 0);
lean_dec(x_253);
x_254 = l_Lean_Name_str___override(x_196, x_203);
x_255 = l_Lean_Name_str___override(x_254, x_201);
x_256 = l_Lean_Name_str___override(x_255, x_200);
x_257 = l_Lean_Name_str___override(x_256, x_199);
x_258 = lean_array_get_size(x_198);
x_259 = lean_usize_of_nat(x_258);
lean_dec(x_258);
x_260 = 0;
x_261 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6(x_2, x_259, x_260, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_263, 0);
lean_ctor_set(x_1, 2, x_265);
lean_ctor_set(x_1, 1, x_257);
lean_ctor_set(x_263, 0, x_1);
return x_261;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_263, 0);
x_267 = lean_ctor_get(x_263, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_263);
lean_ctor_set(x_1, 2, x_266);
lean_ctor_set(x_1, 1, x_257);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_1);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_261, 0, x_268);
return x_261;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_269 = lean_ctor_get(x_261, 0);
x_270 = lean_ctor_get(x_261, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_261);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_273 = x_269;
} else {
 lean_dec_ref(x_269);
 x_273 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_271);
lean_ctor_set(x_1, 1, x_257);
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_1);
lean_ctor_set(x_274, 1, x_272);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_270);
return x_275;
}
}
else
{
uint8_t x_276; 
lean_dec(x_257);
lean_free_object(x_1);
lean_dec(x_197);
x_276 = !lean_is_exclusive(x_261);
if (x_276 == 0)
{
return x_261;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_261, 0);
x_278 = lean_ctor_get(x_261, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_261);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; size_t x_285; size_t x_286; lean_object* x_287; 
lean_dec(x_1);
x_280 = l_Lean_Name_str___override(x_196, x_203);
x_281 = l_Lean_Name_str___override(x_280, x_201);
x_282 = l_Lean_Name_str___override(x_281, x_200);
x_283 = l_Lean_Name_str___override(x_282, x_199);
x_284 = lean_array_get_size(x_198);
x_285 = lean_usize_of_nat(x_284);
lean_dec(x_284);
x_286 = 0;
x_287 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__6(x_2, x_285, x_286, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_288, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_293 = x_288;
} else {
 lean_dec_ref(x_288);
 x_293 = lean_box(0);
}
x_294 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_294, 0, x_197);
lean_ctor_set(x_294, 1, x_283);
lean_ctor_set(x_294, 2, x_291);
if (lean_is_scalar(x_293)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_293;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_292);
if (lean_is_scalar(x_290)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_290;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_289);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_283);
lean_dec(x_197);
x_297 = lean_ctor_get(x_287, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_287, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_299 = x_287;
} else {
 lean_dec_ref(x_287);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
}
else
{
lean_object* x_301; uint8_t x_302; 
lean_dec(x_201);
x_301 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__3;
x_302 = lean_string_dec_eq(x_200, x_301);
if (x_302 == 0)
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_1);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; size_t x_312; size_t x_313; lean_object* x_314; 
x_304 = lean_ctor_get(x_1, 2);
lean_dec(x_304);
x_305 = lean_ctor_get(x_1, 1);
lean_dec(x_305);
x_306 = lean_ctor_get(x_1, 0);
lean_dec(x_306);
x_307 = l_Lean_Name_str___override(x_196, x_203);
x_308 = l_Lean_Name_str___override(x_307, x_248);
x_309 = l_Lean_Name_str___override(x_308, x_200);
x_310 = l_Lean_Name_str___override(x_309, x_199);
x_311 = lean_array_get_size(x_198);
x_312 = lean_usize_of_nat(x_311);
lean_dec(x_311);
x_313 = 0;
x_314 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7(x_2, x_312, x_313, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_314) == 0)
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_ctor_get(x_314, 0);
x_317 = !lean_is_exclusive(x_316);
if (x_317 == 0)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_316, 0);
lean_ctor_set(x_1, 2, x_318);
lean_ctor_set(x_1, 1, x_310);
lean_ctor_set(x_316, 0, x_1);
return x_314;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_316, 0);
x_320 = lean_ctor_get(x_316, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_316);
lean_ctor_set(x_1, 2, x_319);
lean_ctor_set(x_1, 1, x_310);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_1);
lean_ctor_set(x_321, 1, x_320);
lean_ctor_set(x_314, 0, x_321);
return x_314;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_322 = lean_ctor_get(x_314, 0);
x_323 = lean_ctor_get(x_314, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_314);
x_324 = lean_ctor_get(x_322, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_326 = x_322;
} else {
 lean_dec_ref(x_322);
 x_326 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_324);
lean_ctor_set(x_1, 1, x_310);
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_1);
lean_ctor_set(x_327, 1, x_325);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_323);
return x_328;
}
}
else
{
uint8_t x_329; 
lean_dec(x_310);
lean_free_object(x_1);
lean_dec(x_197);
x_329 = !lean_is_exclusive(x_314);
if (x_329 == 0)
{
return x_314;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_314, 0);
x_331 = lean_ctor_get(x_314, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_314);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; size_t x_338; size_t x_339; lean_object* x_340; 
lean_dec(x_1);
x_333 = l_Lean_Name_str___override(x_196, x_203);
x_334 = l_Lean_Name_str___override(x_333, x_248);
x_335 = l_Lean_Name_str___override(x_334, x_200);
x_336 = l_Lean_Name_str___override(x_335, x_199);
x_337 = lean_array_get_size(x_198);
x_338 = lean_usize_of_nat(x_337);
lean_dec(x_337);
x_339 = 0;
x_340 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__7(x_2, x_338, x_339, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_341, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_341, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_346 = x_341;
} else {
 lean_dec_ref(x_341);
 x_346 = lean_box(0);
}
x_347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_347, 0, x_197);
lean_ctor_set(x_347, 1, x_336);
lean_ctor_set(x_347, 2, x_344);
if (lean_is_scalar(x_346)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_346;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_345);
if (lean_is_scalar(x_343)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_343;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_342);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_336);
lean_dec(x_197);
x_350 = lean_ctor_get(x_340, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_340, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_352 = x_340;
} else {
 lean_dec_ref(x_340);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
}
else
{
lean_object* x_354; uint8_t x_355; 
lean_dec(x_200);
x_354 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__4;
x_355 = lean_string_dec_eq(x_199, x_354);
if (x_355 == 0)
{
uint8_t x_356; 
x_356 = !lean_is_exclusive(x_1);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; size_t x_365; size_t x_366; lean_object* x_367; 
x_357 = lean_ctor_get(x_1, 2);
lean_dec(x_357);
x_358 = lean_ctor_get(x_1, 1);
lean_dec(x_358);
x_359 = lean_ctor_get(x_1, 0);
lean_dec(x_359);
x_360 = l_Lean_Name_str___override(x_196, x_203);
x_361 = l_Lean_Name_str___override(x_360, x_248);
x_362 = l_Lean_Name_str___override(x_361, x_301);
x_363 = l_Lean_Name_str___override(x_362, x_199);
x_364 = lean_array_get_size(x_198);
x_365 = lean_usize_of_nat(x_364);
lean_dec(x_364);
x_366 = 0;
x_367 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8(x_2, x_365, x_366, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_367) == 0)
{
uint8_t x_368; 
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
lean_object* x_369; uint8_t x_370; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = !lean_is_exclusive(x_369);
if (x_370 == 0)
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_369, 0);
lean_ctor_set(x_1, 2, x_371);
lean_ctor_set(x_1, 1, x_363);
lean_ctor_set(x_369, 0, x_1);
return x_367;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_369, 0);
x_373 = lean_ctor_get(x_369, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_369);
lean_ctor_set(x_1, 2, x_372);
lean_ctor_set(x_1, 1, x_363);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_1);
lean_ctor_set(x_374, 1, x_373);
lean_ctor_set(x_367, 0, x_374);
return x_367;
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_375 = lean_ctor_get(x_367, 0);
x_376 = lean_ctor_get(x_367, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_367);
x_377 = lean_ctor_get(x_375, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_379 = x_375;
} else {
 lean_dec_ref(x_375);
 x_379 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_377);
lean_ctor_set(x_1, 1, x_363);
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_1);
lean_ctor_set(x_380, 1, x_378);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_376);
return x_381;
}
}
else
{
uint8_t x_382; 
lean_dec(x_363);
lean_free_object(x_1);
lean_dec(x_197);
x_382 = !lean_is_exclusive(x_367);
if (x_382 == 0)
{
return x_367;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_367, 0);
x_384 = lean_ctor_get(x_367, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_367);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; size_t x_391; size_t x_392; lean_object* x_393; 
lean_dec(x_1);
x_386 = l_Lean_Name_str___override(x_196, x_203);
x_387 = l_Lean_Name_str___override(x_386, x_248);
x_388 = l_Lean_Name_str___override(x_387, x_301);
x_389 = l_Lean_Name_str___override(x_388, x_199);
x_390 = lean_array_get_size(x_198);
x_391 = lean_usize_of_nat(x_390);
lean_dec(x_390);
x_392 = 0;
x_393 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__8(x_2, x_391, x_392, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
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
x_397 = lean_ctor_get(x_394, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_394, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_399 = x_394;
} else {
 lean_dec_ref(x_394);
 x_399 = lean_box(0);
}
x_400 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_400, 0, x_197);
lean_ctor_set(x_400, 1, x_389);
lean_ctor_set(x_400, 2, x_397);
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_398);
if (lean_is_scalar(x_396)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_396;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_395);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_389);
lean_dec(x_197);
x_403 = lean_ctor_get(x_393, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_393, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_405 = x_393;
} else {
 lean_dec_ref(x_393);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
}
else
{
lean_object* x_407; 
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_inc(x_10);
lean_inc(x_9);
x_407 = l_Lean_Elab_Term_exprToSyntax(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_ctor_get(x_9, 5);
lean_inc(x_410);
lean_dec(x_9);
x_411 = 0;
x_412 = l_Lean_SourceInfo_fromRef(x_410, x_411);
lean_dec(x_410);
x_413 = lean_st_ref_get(x_10, x_409);
lean_dec(x_10);
x_414 = !lean_is_exclusive(x_413);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_415 = lean_ctor_get(x_413, 0);
lean_dec(x_415);
x_416 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7;
lean_inc(x_412);
x_417 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_417, 0, x_412);
lean_ctor_set(x_417, 1, x_416);
x_418 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8;
lean_inc(x_412);
x_419 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_419, 0, x_412);
lean_ctor_set(x_419, 1, x_418);
x_420 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10;
lean_inc(x_412);
x_421 = l_Lean_Syntax_node1(x_412, x_420, x_408);
x_422 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11;
lean_inc(x_412);
x_423 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_423, 0, x_412);
lean_ctor_set(x_423, 1, x_422);
x_424 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6;
x_425 = l_Lean_Syntax_node5(x_412, x_424, x_417, x_1, x_419, x_421, x_423);
x_426 = lean_box(x_411);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
lean_ctor_set(x_413, 0, x_427);
return x_413;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_428 = lean_ctor_get(x_413, 1);
lean_inc(x_428);
lean_dec(x_413);
x_429 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__7;
lean_inc(x_412);
x_430 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_430, 0, x_412);
lean_ctor_set(x_430, 1, x_429);
x_431 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__8;
lean_inc(x_412);
x_432 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_432, 0, x_412);
lean_ctor_set(x_432, 1, x_431);
x_433 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__10;
lean_inc(x_412);
x_434 = l_Lean_Syntax_node1(x_412, x_433, x_408);
x_435 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__11;
lean_inc(x_412);
x_436 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_436, 0, x_412);
lean_ctor_set(x_436, 1, x_435);
x_437 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lambda__1___closed__6;
x_438 = l_Lean_Syntax_node5(x_412, x_437, x_430, x_1, x_432, x_434, x_436);
x_439 = lean_box(x_411);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_428);
return x_441;
}
}
else
{
uint8_t x_442; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_442 = !lean_is_exclusive(x_407);
if (x_442 == 0)
{
return x_407;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_407, 0);
x_444 = lean_ctor_get(x_407, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_407);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_446; 
lean_dec(x_196);
lean_dec(x_150);
lean_dec(x_104);
lean_dec(x_58);
x_446 = !lean_is_exclusive(x_1);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; size_t x_451; size_t x_452; lean_object* x_453; 
x_447 = lean_ctor_get(x_1, 0);
x_448 = lean_ctor_get(x_1, 2);
x_449 = lean_ctor_get(x_1, 1);
lean_dec(x_449);
x_450 = lean_array_get_size(x_448);
x_451 = lean_usize_of_nat(x_450);
lean_dec(x_450);
x_452 = 0;
x_453 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9(x_2, x_451, x_452, x_448, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_453) == 0)
{
uint8_t x_454; 
x_454 = !lean_is_exclusive(x_453);
if (x_454 == 0)
{
lean_object* x_455; uint8_t x_456; 
x_455 = lean_ctor_get(x_453, 0);
x_456 = !lean_is_exclusive(x_455);
if (x_456 == 0)
{
lean_object* x_457; 
x_457 = lean_ctor_get(x_455, 0);
lean_ctor_set(x_1, 2, x_457);
lean_ctor_set(x_455, 0, x_1);
return x_453;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_455, 0);
x_459 = lean_ctor_get(x_455, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_455);
lean_ctor_set(x_1, 2, x_458);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_1);
lean_ctor_set(x_460, 1, x_459);
lean_ctor_set(x_453, 0, x_460);
return x_453;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_461 = lean_ctor_get(x_453, 0);
x_462 = lean_ctor_get(x_453, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_453);
x_463 = lean_ctor_get(x_461, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_461, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_465 = x_461;
} else {
 lean_dec_ref(x_461);
 x_465 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_463);
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_1);
lean_ctor_set(x_466, 1, x_464);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_462);
return x_467;
}
}
else
{
uint8_t x_468; 
lean_free_object(x_1);
lean_dec(x_447);
lean_dec(x_12);
x_468 = !lean_is_exclusive(x_453);
if (x_468 == 0)
{
return x_453;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_453, 0);
x_470 = lean_ctor_get(x_453, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_453);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; size_t x_475; size_t x_476; lean_object* x_477; 
x_472 = lean_ctor_get(x_1, 0);
x_473 = lean_ctor_get(x_1, 2);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_1);
x_474 = lean_array_get_size(x_473);
x_475 = lean_usize_of_nat(x_474);
lean_dec(x_474);
x_476 = 0;
x_477 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__9(x_2, x_475, x_476, x_473, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_480 = x_477;
} else {
 lean_dec_ref(x_477);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_478, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_478, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_483 = x_478;
} else {
 lean_dec_ref(x_478);
 x_483 = lean_box(0);
}
x_484 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_484, 0, x_472);
lean_ctor_set(x_484, 1, x_12);
lean_ctor_set(x_484, 2, x_481);
if (lean_is_scalar(x_483)) {
 x_485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_485 = x_483;
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_482);
if (lean_is_scalar(x_480)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_480;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_479);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_472);
lean_dec(x_12);
x_487 = lean_ctor_get(x_477, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_477, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_489 = x_477;
} else {
 lean_dec_ref(x_477);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
}
default: 
{
uint8_t x_491; 
lean_dec(x_196);
lean_dec(x_150);
lean_dec(x_104);
lean_dec(x_58);
x_491 = !lean_is_exclusive(x_1);
if (x_491 == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; size_t x_496; size_t x_497; lean_object* x_498; 
x_492 = lean_ctor_get(x_1, 0);
x_493 = lean_ctor_get(x_1, 2);
x_494 = lean_ctor_get(x_1, 1);
lean_dec(x_494);
x_495 = lean_array_get_size(x_493);
x_496 = lean_usize_of_nat(x_495);
lean_dec(x_495);
x_497 = 0;
x_498 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10(x_2, x_496, x_497, x_493, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_498) == 0)
{
uint8_t x_499; 
x_499 = !lean_is_exclusive(x_498);
if (x_499 == 0)
{
lean_object* x_500; uint8_t x_501; 
x_500 = lean_ctor_get(x_498, 0);
x_501 = !lean_is_exclusive(x_500);
if (x_501 == 0)
{
lean_object* x_502; 
x_502 = lean_ctor_get(x_500, 0);
lean_ctor_set(x_1, 2, x_502);
lean_ctor_set(x_500, 0, x_1);
return x_498;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_500, 0);
x_504 = lean_ctor_get(x_500, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_500);
lean_ctor_set(x_1, 2, x_503);
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_1);
lean_ctor_set(x_505, 1, x_504);
lean_ctor_set(x_498, 0, x_505);
return x_498;
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_498, 0);
x_507 = lean_ctor_get(x_498, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_498);
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_510 = x_506;
} else {
 lean_dec_ref(x_506);
 x_510 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_508);
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_1);
lean_ctor_set(x_511, 1, x_509);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_507);
return x_512;
}
}
else
{
uint8_t x_513; 
lean_free_object(x_1);
lean_dec(x_492);
lean_dec(x_12);
x_513 = !lean_is_exclusive(x_498);
if (x_513 == 0)
{
return x_498;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_498, 0);
x_515 = lean_ctor_get(x_498, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_498);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; size_t x_520; size_t x_521; lean_object* x_522; 
x_517 = lean_ctor_get(x_1, 0);
x_518 = lean_ctor_get(x_1, 2);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_1);
x_519 = lean_array_get_size(x_518);
x_520 = lean_usize_of_nat(x_519);
lean_dec(x_519);
x_521 = 0;
x_522 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__10(x_2, x_520, x_521, x_518, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_525 = x_522;
} else {
 lean_dec_ref(x_522);
 x_525 = lean_box(0);
}
x_526 = lean_ctor_get(x_523, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_523, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_528 = x_523;
} else {
 lean_dec_ref(x_523);
 x_528 = lean_box(0);
}
x_529 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_529, 0, x_517);
lean_ctor_set(x_529, 1, x_12);
lean_ctor_set(x_529, 2, x_526);
if (lean_is_scalar(x_528)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_528;
}
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_527);
if (lean_is_scalar(x_525)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_525;
}
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_524);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_517);
lean_dec(x_12);
x_532 = lean_ctor_get(x_522, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_522, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_534 = x_522;
} else {
 lean_dec_ref(x_522);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
}
}
}
default: 
{
uint8_t x_536; 
lean_dec(x_150);
lean_dec(x_104);
lean_dec(x_58);
x_536 = !lean_is_exclusive(x_1);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; size_t x_541; size_t x_542; lean_object* x_543; 
x_537 = lean_ctor_get(x_1, 0);
x_538 = lean_ctor_get(x_1, 2);
x_539 = lean_ctor_get(x_1, 1);
lean_dec(x_539);
x_540 = lean_array_get_size(x_538);
x_541 = lean_usize_of_nat(x_540);
lean_dec(x_540);
x_542 = 0;
x_543 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11(x_2, x_541, x_542, x_538, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_543) == 0)
{
uint8_t x_544; 
x_544 = !lean_is_exclusive(x_543);
if (x_544 == 0)
{
lean_object* x_545; uint8_t x_546; 
x_545 = lean_ctor_get(x_543, 0);
x_546 = !lean_is_exclusive(x_545);
if (x_546 == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_545, 0);
lean_ctor_set(x_1, 2, x_547);
lean_ctor_set(x_545, 0, x_1);
return x_543;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_545, 0);
x_549 = lean_ctor_get(x_545, 1);
lean_inc(x_549);
lean_inc(x_548);
lean_dec(x_545);
lean_ctor_set(x_1, 2, x_548);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_1);
lean_ctor_set(x_550, 1, x_549);
lean_ctor_set(x_543, 0, x_550);
return x_543;
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_551 = lean_ctor_get(x_543, 0);
x_552 = lean_ctor_get(x_543, 1);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_543);
x_553 = lean_ctor_get(x_551, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_551, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_555 = x_551;
} else {
 lean_dec_ref(x_551);
 x_555 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_553);
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_1);
lean_ctor_set(x_556, 1, x_554);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_552);
return x_557;
}
}
else
{
uint8_t x_558; 
lean_free_object(x_1);
lean_dec(x_537);
lean_dec(x_12);
x_558 = !lean_is_exclusive(x_543);
if (x_558 == 0)
{
return x_543;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_543, 0);
x_560 = lean_ctor_get(x_543, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_543);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
return x_561;
}
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; size_t x_565; size_t x_566; lean_object* x_567; 
x_562 = lean_ctor_get(x_1, 0);
x_563 = lean_ctor_get(x_1, 2);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_1);
x_564 = lean_array_get_size(x_563);
x_565 = lean_usize_of_nat(x_564);
lean_dec(x_564);
x_566 = 0;
x_567 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__11(x_2, x_565, x_566, x_563, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_570 = x_567;
} else {
 lean_dec_ref(x_567);
 x_570 = lean_box(0);
}
x_571 = lean_ctor_get(x_568, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_568, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_573 = x_568;
} else {
 lean_dec_ref(x_568);
 x_573 = lean_box(0);
}
x_574 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_574, 0, x_562);
lean_ctor_set(x_574, 1, x_12);
lean_ctor_set(x_574, 2, x_571);
if (lean_is_scalar(x_573)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_573;
}
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_572);
if (lean_is_scalar(x_570)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_570;
}
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_569);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_562);
lean_dec(x_12);
x_577 = lean_ctor_get(x_567, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_567, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_579 = x_567;
} else {
 lean_dec_ref(x_567);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_578);
return x_580;
}
}
}
}
}
default: 
{
uint8_t x_581; 
lean_dec(x_104);
lean_dec(x_58);
x_581 = !lean_is_exclusive(x_1);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; size_t x_586; size_t x_587; lean_object* x_588; 
x_582 = lean_ctor_get(x_1, 0);
x_583 = lean_ctor_get(x_1, 2);
x_584 = lean_ctor_get(x_1, 1);
lean_dec(x_584);
x_585 = lean_array_get_size(x_583);
x_586 = lean_usize_of_nat(x_585);
lean_dec(x_585);
x_587 = 0;
x_588 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12(x_2, x_586, x_587, x_583, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_588) == 0)
{
uint8_t x_589; 
x_589 = !lean_is_exclusive(x_588);
if (x_589 == 0)
{
lean_object* x_590; uint8_t x_591; 
x_590 = lean_ctor_get(x_588, 0);
x_591 = !lean_is_exclusive(x_590);
if (x_591 == 0)
{
lean_object* x_592; 
x_592 = lean_ctor_get(x_590, 0);
lean_ctor_set(x_1, 2, x_592);
lean_ctor_set(x_590, 0, x_1);
return x_588;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_590, 0);
x_594 = lean_ctor_get(x_590, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_590);
lean_ctor_set(x_1, 2, x_593);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_1);
lean_ctor_set(x_595, 1, x_594);
lean_ctor_set(x_588, 0, x_595);
return x_588;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_596 = lean_ctor_get(x_588, 0);
x_597 = lean_ctor_get(x_588, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_588);
x_598 = lean_ctor_get(x_596, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_596, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_600 = x_596;
} else {
 lean_dec_ref(x_596);
 x_600 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_598);
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(0, 2, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_1);
lean_ctor_set(x_601, 1, x_599);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_597);
return x_602;
}
}
else
{
uint8_t x_603; 
lean_free_object(x_1);
lean_dec(x_582);
lean_dec(x_12);
x_603 = !lean_is_exclusive(x_588);
if (x_603 == 0)
{
return x_588;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_588, 0);
x_605 = lean_ctor_get(x_588, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_588);
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
return x_606;
}
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; size_t x_610; size_t x_611; lean_object* x_612; 
x_607 = lean_ctor_get(x_1, 0);
x_608 = lean_ctor_get(x_1, 2);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_1);
x_609 = lean_array_get_size(x_608);
x_610 = lean_usize_of_nat(x_609);
lean_dec(x_609);
x_611 = 0;
x_612 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__12(x_2, x_610, x_611, x_608, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_615 = x_612;
} else {
 lean_dec_ref(x_612);
 x_615 = lean_box(0);
}
x_616 = lean_ctor_get(x_613, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_613, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_618 = x_613;
} else {
 lean_dec_ref(x_613);
 x_618 = lean_box(0);
}
x_619 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_619, 0, x_607);
lean_ctor_set(x_619, 1, x_12);
lean_ctor_set(x_619, 2, x_616);
if (lean_is_scalar(x_618)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_618;
}
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_617);
if (lean_is_scalar(x_615)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_615;
}
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_614);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_607);
lean_dec(x_12);
x_622 = lean_ctor_get(x_612, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_612, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_624 = x_612;
} else {
 lean_dec_ref(x_612);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_623);
return x_625;
}
}
}
}
}
default: 
{
uint8_t x_626; 
lean_dec(x_58);
x_626 = !lean_is_exclusive(x_1);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; size_t x_631; size_t x_632; lean_object* x_633; 
x_627 = lean_ctor_get(x_1, 0);
x_628 = lean_ctor_get(x_1, 2);
x_629 = lean_ctor_get(x_1, 1);
lean_dec(x_629);
x_630 = lean_array_get_size(x_628);
x_631 = lean_usize_of_nat(x_630);
lean_dec(x_630);
x_632 = 0;
x_633 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13(x_2, x_631, x_632, x_628, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_633) == 0)
{
uint8_t x_634; 
x_634 = !lean_is_exclusive(x_633);
if (x_634 == 0)
{
lean_object* x_635; uint8_t x_636; 
x_635 = lean_ctor_get(x_633, 0);
x_636 = !lean_is_exclusive(x_635);
if (x_636 == 0)
{
lean_object* x_637; 
x_637 = lean_ctor_get(x_635, 0);
lean_ctor_set(x_1, 2, x_637);
lean_ctor_set(x_635, 0, x_1);
return x_633;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_635, 0);
x_639 = lean_ctor_get(x_635, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_635);
lean_ctor_set(x_1, 2, x_638);
x_640 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_640, 0, x_1);
lean_ctor_set(x_640, 1, x_639);
lean_ctor_set(x_633, 0, x_640);
return x_633;
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_641 = lean_ctor_get(x_633, 0);
x_642 = lean_ctor_get(x_633, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_633);
x_643 = lean_ctor_get(x_641, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_641, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_645 = x_641;
} else {
 lean_dec_ref(x_641);
 x_645 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_643);
if (lean_is_scalar(x_645)) {
 x_646 = lean_alloc_ctor(0, 2, 0);
} else {
 x_646 = x_645;
}
lean_ctor_set(x_646, 0, x_1);
lean_ctor_set(x_646, 1, x_644);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_642);
return x_647;
}
}
else
{
uint8_t x_648; 
lean_free_object(x_1);
lean_dec(x_627);
lean_dec(x_12);
x_648 = !lean_is_exclusive(x_633);
if (x_648 == 0)
{
return x_633;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_633, 0);
x_650 = lean_ctor_get(x_633, 1);
lean_inc(x_650);
lean_inc(x_649);
lean_dec(x_633);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
return x_651;
}
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; size_t x_655; size_t x_656; lean_object* x_657; 
x_652 = lean_ctor_get(x_1, 0);
x_653 = lean_ctor_get(x_1, 2);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_1);
x_654 = lean_array_get_size(x_653);
x_655 = lean_usize_of_nat(x_654);
lean_dec(x_654);
x_656 = 0;
x_657 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__13(x_2, x_655, x_656, x_653, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_660 = x_657;
} else {
 lean_dec_ref(x_657);
 x_660 = lean_box(0);
}
x_661 = lean_ctor_get(x_658, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_658, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_663 = x_658;
} else {
 lean_dec_ref(x_658);
 x_663 = lean_box(0);
}
x_664 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_664, 0, x_652);
lean_ctor_set(x_664, 1, x_12);
lean_ctor_set(x_664, 2, x_661);
if (lean_is_scalar(x_663)) {
 x_665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_665 = x_663;
}
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_662);
if (lean_is_scalar(x_660)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_660;
}
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_659);
return x_666;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_652);
lean_dec(x_12);
x_667 = lean_ctor_get(x_657, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_657, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_669 = x_657;
} else {
 lean_dec_ref(x_657);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_667);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
}
}
}
}
default: 
{
uint8_t x_671; 
x_671 = !lean_is_exclusive(x_1);
if (x_671 == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; size_t x_676; size_t x_677; lean_object* x_678; 
x_672 = lean_ctor_get(x_1, 0);
x_673 = lean_ctor_get(x_1, 2);
x_674 = lean_ctor_get(x_1, 1);
lean_dec(x_674);
x_675 = lean_array_get_size(x_673);
x_676 = lean_usize_of_nat(x_675);
lean_dec(x_675);
x_677 = 0;
x_678 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14(x_2, x_676, x_677, x_673, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_678) == 0)
{
uint8_t x_679; 
x_679 = !lean_is_exclusive(x_678);
if (x_679 == 0)
{
lean_object* x_680; uint8_t x_681; 
x_680 = lean_ctor_get(x_678, 0);
x_681 = !lean_is_exclusive(x_680);
if (x_681 == 0)
{
lean_object* x_682; 
x_682 = lean_ctor_get(x_680, 0);
lean_ctor_set(x_1, 2, x_682);
lean_ctor_set(x_680, 0, x_1);
return x_678;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_680, 0);
x_684 = lean_ctor_get(x_680, 1);
lean_inc(x_684);
lean_inc(x_683);
lean_dec(x_680);
lean_ctor_set(x_1, 2, x_683);
x_685 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_685, 0, x_1);
lean_ctor_set(x_685, 1, x_684);
lean_ctor_set(x_678, 0, x_685);
return x_678;
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_686 = lean_ctor_get(x_678, 0);
x_687 = lean_ctor_get(x_678, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_678);
x_688 = lean_ctor_get(x_686, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_686, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_690 = x_686;
} else {
 lean_dec_ref(x_686);
 x_690 = lean_box(0);
}
lean_ctor_set(x_1, 2, x_688);
if (lean_is_scalar(x_690)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_690;
}
lean_ctor_set(x_691, 0, x_1);
lean_ctor_set(x_691, 1, x_689);
x_692 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_692, 0, x_691);
lean_ctor_set(x_692, 1, x_687);
return x_692;
}
}
else
{
uint8_t x_693; 
lean_free_object(x_1);
lean_dec(x_672);
lean_dec(x_12);
x_693 = !lean_is_exclusive(x_678);
if (x_693 == 0)
{
return x_678;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_694 = lean_ctor_get(x_678, 0);
x_695 = lean_ctor_get(x_678, 1);
lean_inc(x_695);
lean_inc(x_694);
lean_dec(x_678);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
return x_696;
}
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; size_t x_700; size_t x_701; lean_object* x_702; 
x_697 = lean_ctor_get(x_1, 0);
x_698 = lean_ctor_get(x_1, 2);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_1);
x_699 = lean_array_get_size(x_698);
x_700 = lean_usize_of_nat(x_699);
lean_dec(x_699);
x_701 = 0;
x_702 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_annotateFirstHoleWithType_go___spec__14(x_2, x_700, x_701, x_698, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_705 = x_702;
} else {
 lean_dec_ref(x_702);
 x_705 = lean_box(0);
}
x_706 = lean_ctor_get(x_703, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_703, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_708 = x_703;
} else {
 lean_dec_ref(x_703);
 x_708 = lean_box(0);
}
x_709 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_709, 0, x_697);
lean_ctor_set(x_709, 1, x_12);
lean_ctor_set(x_709, 2, x_706);
if (lean_is_scalar(x_708)) {
 x_710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_710 = x_708;
}
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_707);
if (lean_is_scalar(x_705)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_705;
}
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_704);
return x_711;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
lean_dec(x_697);
lean_dec(x_12);
x_712 = lean_ctor_get(x_702, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_702, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_714 = x_702;
} else {
 lean_dec_ref(x_702);
 x_714 = lean_box(0);
}
if (lean_is_scalar(x_714)) {
 x_715 = lean_alloc_ctor(1, 2, 0);
} else {
 x_715 = x_714;
}
lean_ctor_set(x_715, 0, x_712);
lean_ctor_set(x_715, 1, x_713);
return x_715;
}
}
}
}
}
else
{
uint8_t x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_716 = 0;
x_717 = lean_box(x_716);
x_718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_718, 0, x_1);
lean_ctor_set(x_718, 1, x_717);
x_719 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_11);
return x_719;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_get_size(x_10);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Lean_Elab_Term_elabCalcSteps___closed__1;
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabCalcSteps___spec__2(x_10, x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = l_Lean_Elab_Term_elabCalcSteps___closed__5;
x_22 = l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l_Lean_Elab_Term_elabCalcSteps___closed__5;
x_26 = l_panic___at_Lean_Elab_Term_elabCalcSteps___spec__3(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_16, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
l_Lean_Elab_Term_mkCalcTrans___closed__16 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__16);
l_Lean_Elab_Term_mkCalcTrans___closed__17 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__17);
l_Lean_Elab_Term_mkCalcTrans___closed__18 = _init_l_Lean_Elab_Term_mkCalcTrans___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_mkCalcTrans___closed__18);
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
