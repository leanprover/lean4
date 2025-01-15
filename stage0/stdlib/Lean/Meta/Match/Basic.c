// Lean compiler output
// Module: Lean.Meta.Match.Basic
// Imports: Lean.Meta.Check Lean.Meta.CollectFVars Lean.Meta.Match.MatcherInfo Lean.Meta.Match.CaseArraySizes
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
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__4;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_toMessageData___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__2;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__3;
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__4;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_examplesToMessageData___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Meta_Match_instInhabitedPattern___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__6;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__4;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_instInhabitedAlt___closed__1;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__2;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__1;
lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object*);
uint8_t l_List_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Match_instInhabitedProblem___closed__1;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__16;
lean_object* l_Lean_mkInaccessible(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isNamedPattern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inaccessible_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_toMessageData___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_toPattern___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_toPattern___closed__3;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__1;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__10;
static lean_object* l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__2;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__12;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object*);
lean_object* l_Lean_LocalDecl_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__5;
static lean_object* l_Lean_Meta_Match_toPattern___closed__1;
lean_object* l_Lean_Meta_isMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___closed__1;
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__17;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object*);
static lean_object* l_Lean_Meta_Match_instInhabitedPattern___closed__1;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__7;
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__5;
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__5;
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__2;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__1;
static lean_object* l_Lean_Meta_Match_mkNamedPattern___closed__1;
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_toPattern___closed__5;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__13;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__3;
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__1;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__4;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__7;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__2;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedAlt;
static lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Problem_toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_varsToUnderscore___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__3;
static lean_object* l_Lean_Meta_Match_toPattern___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkNamedPattern___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_toPattern___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Problem_toMessageData___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedPattern;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__3;
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_counterExamplesToMessageData___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedProblem;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__15;
static lean_object* _init_l_Lean_Meta_Match_mkNamedPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namedPattern", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkNamedPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_mkNamedPattern___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkNamedPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_mk(x_12);
x_14 = l_Lean_Meta_Match_mkNamedPattern___closed__2;
x_15 = l_Lean_Meta_mkAppM(x_14, x_13, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isNamedPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Lean_Expr_consumeMData(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_3);
x_5 = lean_unsigned_to_nat(4u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_9 = l_Lean_Expr_consumeMData(x_8);
lean_dec(x_8);
x_10 = l_Lean_Meta_Match_mkNamedPattern___closed__2;
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_isNamedPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Lean_Expr_consumeMData(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_3);
x_5 = lean_unsigned_to_nat(4u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Expr_getAppFn(x_2);
x_9 = l_Lean_Expr_consumeMData(x_8);
lean_dec(x_8);
x_10 = l_Lean_Meta_Match_mkNamedPattern___closed__2;
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_isNamedPattern_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_instInhabitedPattern___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedPattern___closed__2;
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_7 = l_Lean_Meta_Match_Pattern_toMessageData(x_4);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_1 = x_8;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_Match_Pattern_toMessageData(x_10);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_1 = x_15;
x_2 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_toMessageData___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Match_Pattern_toMessageData(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Match_Pattern_toMessageData(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".(", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__13;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_MessageData_ofExpr(x_2);
x_4 = l_Lean_Meta_Match_Pattern_toMessageData___closed__2;
x_5 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Expr_fvar___override(x_8);
x_10 = l_Lean_MessageData_ofExpr(x_9);
return x_10;
}
case 2:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_MessageData_ofName(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_MessageData_ofName(x_14);
x_16 = l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_Match_Pattern_toMessageData___closed__9;
lean_inc(x_11);
x_21 = l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1(x_20, x_11);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_11, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_11, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_19);
x_25 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_21);
x_28 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 3:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_MessageData_ofExpr(x_30);
return x_31;
}
case 4:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_toMessageData___spec__2(x_33, x_35);
x_37 = l_Lean_Meta_Match_Pattern_toMessageData___closed__14;
x_38 = l_Lean_MessageData_joinSep(x_36, x_37);
x_39 = l_Lean_Meta_Match_Pattern_toMessageData___closed__11;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_39);
x_40 = l_Lean_Meta_Match_Pattern_toMessageData___closed__16;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_toMessageData___spec__2(x_42, x_43);
x_45 = l_Lean_Meta_Match_Pattern_toMessageData___closed__14;
x_46 = l_Lean_MessageData_joinSep(x_44, x_45);
x_47 = l_Lean_Meta_Match_Pattern_toMessageData___closed__11;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Meta_Match_Pattern_toMessageData___closed__16;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_dec(x_1);
x_53 = l_Lean_Expr_fvar___override(x_51);
x_54 = l_Lean_MessageData_ofExpr(x_53);
x_55 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Meta_Match_Pattern_toMessageData___closed__18;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_Match_Pattern_toMessageData(x_52);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = l_List_reverse___rarg(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_15);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_16;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_1, x_22, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_3);
x_2 = x_23;
x_3 = x_27;
x_8 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = l_List_reverse___rarg(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_15);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_16;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_1, x_22, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_3);
x_2 = x_23;
x_3 = x_27;
x_8 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_mkInaccessible(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Expr_fvar___override(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__1(x_1, x_19, x_20, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Expr_const___override(x_16, x_17);
x_25 = l_List_appendTR___rarg(x_18, x_23);
x_26 = lean_array_mk(x_25);
x_27 = l_Lean_mkAppN(x_24, x_26);
lean_dec(x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = l_Lean_Expr_const___override(x_16, x_17);
x_31 = l_List_appendTR___rarg(x_18, x_28);
x_32 = lean_array_mk(x_31);
x_33 = l_Lean_mkAppN(x_30, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 3:
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
return x_40;
}
case 4:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_44 = l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__2(x_1, x_42, x_43, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_mkArrayLit(x_41, x_45, x_3, x_4, x_5, x_6, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
default: 
{
if (x_1 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_dec(x_2);
x_2 = x_52;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_57 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_1, x_55, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Expr_fvar___override(x_54);
x_61 = l_Lean_Expr_fvar___override(x_56);
x_62 = l_Lean_Meta_Match_mkNamedPattern(x_60, x_61, x_58, x_3, x_4, x_5, x_6, x_59);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
return x_57;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_57, 0);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_57);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_List_mapM_loop___at_Lean_Meta_Match_Pattern_toExpr_visit___spec__2(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_Match_Pattern_toExpr(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Meta_FVarSubst_apply(x_1, x_6);
lean_dec(x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_FVarSubst_apply(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Meta_FVarSubst_apply(x_1, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_10, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
return x_2;
}
else
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_13, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
case 2:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_box(0);
lean_inc(x_1);
x_22 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__1(x_1, x_19, x_21);
x_23 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__2(x_1, x_20, x_21);
lean_ctor_set(x_2, 3, x_23);
lean_ctor_set(x_2, 2, x_22);
return x_2;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_28 = lean_box(0);
lean_inc(x_1);
x_29 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__1(x_1, x_26, x_28);
x_30 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__2(x_1, x_27, x_28);
x_31 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
return x_31;
}
}
case 3:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = l_Lean_Meta_FVarSubst_apply(x_1, x_33);
lean_dec(x_33);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Lean_Meta_FVarSubst_apply(x_1, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
case 4:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_41 = l_Lean_Meta_FVarSubst_apply(x_1, x_39);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__3(x_1, x_40, x_42);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_2);
lean_inc(x_1);
x_46 = l_Lean_Meta_FVarSubst_apply(x_1, x_44);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_applyFVarSubst___spec__3(x_1, x_45, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
default: 
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_2);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_51, x_1);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_52);
lean_ctor_set(x_2, 1, x_55);
return x_2;
}
else
{
lean_dec(x_54);
lean_free_object(x_2);
lean_dec(x_53);
lean_dec(x_51);
x_2 = x_52;
goto _start;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = lean_ctor_get(x_2, 1);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_2);
x_60 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_57, x_1);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_58);
x_62 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_59);
return x_62;
}
else
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
x_2 = x_58;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = l_Lean_Meta_FVarSubst_insert(x_4, x_1, x_2);
x_6 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_hasExprMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hasExprMVar___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_hasExprMVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Pattern_hasExprMVar___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
lean_dec(x_1);
x_2 = 0;
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Meta_Match_Pattern_hasExprMVar___closed__1;
x_6 = l_List_any___rarg(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_Match_Pattern_hasExprMVar___closed__2;
x_8 = l_List_any___rarg(x_4, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 1;
return x_9;
}
}
case 4:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Expr_hasExprMVar(x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Meta_Match_Pattern_hasExprMVar___closed__2;
x_14 = l_List_any___rarg(x_11, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 1;
return x_15;
}
}
case 5:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_1 = x_16;
goto _start;
}
default: 
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Expr_hasExprMVar(x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_Pattern_hasExprMVar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Expr_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_11;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_Match_Pattern_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_11;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_st_ref_take(x_2, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_CollectFVars_State_add(x_10, x_8);
x_13 = lean_st_ref_set(x_2, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__1(x_20, x_2, x_3, x_4, x_5, x_6, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__2(x_21, x_2, x_3, x_4, x_5, x_6, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_Expr_collectFVars(x_25, x_2, x_3, x_4, x_5, x_6, x_7);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__2(x_26, x_2, x_3, x_4, x_5, x_6, x_28);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_st_ref_take(x_2, x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_CollectFVars_State_add(x_34, x_30);
x_37 = l_Lean_CollectFVars_State_add(x_36, x_32);
x_38 = lean_st_ref_set(x_2, x_37, x_35);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_1 = x_31;
x_7 = x_39;
goto _start;
}
default: 
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_Lean_Expr_collectFVars(x_41, x_2, x_3, x_4, x_5, x_6, x_7);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at_Lean_Meta_Match_Pattern_collectFVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_Pattern_collectFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_11, x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_17, x_3, x_4, x_5, x_6, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_18;
x_2 = x_22;
x_7 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_Lean_Meta_Match_instantiatePatternMVars(x_11, x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l_Lean_Meta_Match_instantiatePatternMVars(x_17, x_3, x_4, x_5, x_6, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_18;
x_2 = x_22;
x_7 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_1, 0, x_11);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_1, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_15, x_2, x_3, x_4, x_5, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
case 1:
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
case 2:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
x_26 = lean_box(0);
x_27 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__1(x_24, x_26, x_2, x_3, x_4, x_5, x_6);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(x_25, x_26, x_2, x_3, x_4, x_5, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_1, 3, x_32);
lean_ctor_set(x_1, 2, x_28);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_1, 3, x_33);
lean_ctor_set(x_1, 2, x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_ctor_get(x_1, 2);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__1(x_38, x_40, x_2, x_3, x_4, x_5, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(x_39, x_40, x_2, x_3, x_4, x_5, x_43);
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
x_48 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_45);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
case 3:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_51, x_2, x_3, x_4, x_5, x_6);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_1, 0, x_54);
lean_ctor_set(x_52, 0, x_1);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_1, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
lean_dec(x_1);
x_59 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_58, x_2, x_3, x_4, x_5, x_6);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_60);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
case 4:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = lean_ctor_get(x_1, 1);
x_68 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_66, x_2, x_3, x_4, x_5, x_6);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_box(0);
x_72 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(x_67, x_71, x_2, x_3, x_4, x_5, x_70);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_ctor_set(x_1, 1, x_74);
lean_ctor_set(x_1, 0, x_69);
lean_ctor_set(x_72, 0, x_1);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_72);
lean_ctor_set(x_1, 1, x_75);
lean_ctor_set(x_1, 0, x_69);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_1);
x_80 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_78, x_2, x_3, x_4, x_5, x_6);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_box(0);
x_84 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(x_79, x_83, x_2, x_3, x_4, x_5, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
default: 
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_1);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_1, 1);
x_92 = l_Lean_Meta_Match_instantiatePatternMVars(x_91, x_2, x_3, x_4, x_5, x_6);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_ctor_set(x_1, 1, x_94);
lean_ctor_set(x_92, 0, x_1);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_92);
lean_ctor_set(x_1, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_98 = lean_ctor_get(x_1, 0);
x_99 = lean_ctor_get(x_1, 1);
x_100 = lean_ctor_get(x_1, 2);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_1);
x_101 = l_Lean_Meta_Match_instantiatePatternMVars(x_99, x_2, x_3, x_4, x_5, x_6);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_102);
lean_ctor_set(x_105, 2, x_100);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Match_instantiatePatternMVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_LocalDecl_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_11;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_Match_Pattern_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_11;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at_Lean_Meta_Match_AltLHS_collectFVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_AltLHS_collectFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 3);
x_9 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_1, 3, x_11);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_1, 3, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_21 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_18, x_2, x_3, x_4, x_5, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*4 + 1, x_20);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_28, x_2, x_3, x_4, x_5, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_29, x_2, x_3, x_4, x_5, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_1, 4, x_35);
lean_ctor_set(x_1, 3, x_31);
lean_ctor_set(x_33, 0, x_1);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_1, 4, x_36);
lean_ctor_set(x_1, 3, x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_ctor_get(x_1, 3);
x_43 = lean_ctor_get(x_1, 4);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
x_46 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_42, x_2, x_3, x_4, x_5, x_6);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_43, x_2, x_3, x_4, x_5, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_53, 2, x_41);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_44);
lean_ctor_set_uint8(x_53, sizeof(void*)*5 + 1, x_45);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_Lean_instantiateLocalDeclMVars___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(x_11, x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l_Lean_instantiateLocalDeclMVars___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(x_17, x_3, x_4, x_5, x_6, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_18;
x_2 = x_22;
x_7 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_box(0);
x_11 = l_List_mapM_loop___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__2(x_8, x_10, x_2, x_3, x_4, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(x_9, x_10, x_2, x_3, x_4, x_5, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 2, x_16);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_1, 2, x_17);
lean_ctor_set(x_1, 1, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = l_List_mapM_loop___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__2(x_21, x_23, x_2, x_3, x_4, x_5, x_6);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_mapM_loop___at_Lean_Meta_Match_instantiatePatternMVars___spec__2(x_22, x_23, x_2, x_3, x_4, x_5, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateLocalDeclMVars___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Match_instantiateAltLHSMVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Match_instInhabitedPattern___closed__1;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedAlt___closed__1;
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":(", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_LocalDecl_toExpr(x_5);
x_8 = l_Lean_MessageData_ofExpr(x_7);
x_9 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_LocalDecl_type(x_5);
lean_dec(x_5);
x_14 = l_Lean_MessageData_ofExpr(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_17);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l_Lean_LocalDecl_toExpr(x_19);
x_22 = l_Lean_MessageData_ofExpr(x_21);
x_23 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
x_28 = l_Lean_MessageData_ofExpr(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
x_1 = x_20;
x_2 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  | ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ≋ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 0, x_1);
x_20 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_20);
x_21 = l_Lean_MessageData_ofExpr(x_18);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_ofExpr(x_19);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_1);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
x_5 = x_17;
x_6 = x_27;
x_7 = lean_box(0);
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
lean_inc(x_1);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_6);
x_33 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_32);
x_34 = l_Lean_MessageData_ofExpr(x_30);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_ofExpr(x_31);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_1);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_1);
x_5 = x_29;
x_6 = x_40;
x_7 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_5, 0);
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_5);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(7, 2, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 7);
}
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_6);
x_48 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__2;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_ofExpr(x_44);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_MessageData_ofExpr(x_45);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_1);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_1);
x_5 = x_43;
x_6 = x_56;
x_7 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__4___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_10 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3(x_1, x_2, x_3, x_2, x_2, x_4, lean_box(0), x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" |- ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Alt_toMessageData___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" => ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Alt_toMessageData___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1(x_7, x_8);
x_10 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__2(x_9, x_8);
x_11 = l_Lean_MessageData_ofList(x_10);
x_12 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_Match_Alt_toMessageData___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = l_List_mapTR_loop___at_Lean_Meta_Match_Pattern_toMessageData___spec__2(x_16, x_8);
x_18 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__2(x_17, x_8);
x_19 = l_Lean_MessageData_ofList(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_Match_Alt_toMessageData___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = l_Lean_MessageData_ofExpr(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_ctor_get(x_1, 5);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_toMessageData___lambda__1___boxed), 9, 4);
lean_closure_set(x_29, 0, x_12);
lean_closure_set(x_29, 1, x_27);
lean_closure_set(x_29, 2, x_28);
lean_closure_set(x_29, 3, x_26);
x_30 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__4___rarg(x_7, x_29, x_2, x_3, x_4, x_5, x_6);
return x_30;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Match_Alt_toMessageData___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_9);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_12);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
lean_inc(x_1);
x_17 = l_Lean_Meta_FVarSubst_apply(x_1, x_15);
lean_dec(x_15);
lean_inc(x_1);
x_18 = l_Lean_Meta_FVarSubst_apply(x_1, x_16);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_19);
{
lean_object* _tmp_1 = x_14;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
lean_inc(x_1);
x_26 = l_Lean_Meta_FVarSubst_apply(x_1, x_23);
lean_dec(x_23);
lean_inc(x_1);
x_27 = l_Lean_Meta_FVarSubst_apply(x_1, x_24);
lean_dec(x_24);
if (lean_is_scalar(x_25)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_25;
}
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
x_2 = x_22;
x_3 = x_29;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = lean_ctor_get(x_2, 5);
lean_inc(x_1);
x_8 = l_Lean_Meta_FVarSubst_apply(x_1, x_4);
lean_dec(x_4);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__1(x_1, x_5, x_9);
lean_inc(x_1);
x_11 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__2(x_1, x_6, x_9);
x_12 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__3(x_1, x_7, x_9);
lean_ctor_set(x_2, 5, x_12);
lean_ctor_set(x_2, 4, x_11);
lean_ctor_set(x_2, 3, x_10);
lean_ctor_set(x_2, 2, x_8);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
x_17 = lean_ctor_get(x_2, 4);
x_18 = lean_ctor_get(x_2, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_19 = l_Lean_Meta_FVarSubst_apply(x_1, x_15);
lean_dec(x_15);
x_20 = lean_box(0);
lean_inc(x_1);
x_21 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__1(x_1, x_16, x_20);
lean_inc(x_1);
x_22 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__2(x_1, x_17, x_20);
x_23 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_applyFVarSubst___spec__3(x_1, x_18, x_20);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_LocalDecl_fvarId(x_6);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l_Lean_LocalDecl_fvarId(x_12);
x_15 = lean_name_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_9 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Meta_Match_Pattern_replaceFVarId(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_Match_Pattern_replaceFVarId(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
x_12 = l_Lean_Expr_replaceFVarId(x_10, x_1, x_2);
lean_dec(x_10);
lean_inc(x_1);
x_13 = l_Lean_Expr_replaceFVarId(x_11, x_1, x_2);
lean_dec(x_11);
lean_ctor_set(x_7, 1, x_13);
lean_ctor_set(x_7, 0, x_12);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
lean_inc(x_1);
x_18 = l_Lean_Expr_replaceFVarId(x_16, x_1, x_2);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_Expr_replaceFVarId(x_17, x_1, x_2);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_20);
{
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
lean_inc(x_1);
x_27 = l_Lean_Expr_replaceFVarId(x_24, x_1, x_2);
lean_dec(x_24);
lean_inc(x_1);
x_28 = l_Lean_Expr_replaceFVarId(x_25, x_1, x_2);
lean_dec(x_25);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
x_3 = x_23;
x_4 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 4);
x_8 = lean_ctor_get(x_3, 5);
lean_inc(x_1);
x_9 = l_Lean_Expr_replaceFVarId(x_5, x_1, x_2);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = l_List_filterTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__1(x_1, x_6, x_10);
lean_inc(x_1);
x_12 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__2(x_1, x_2, x_11, x_10);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__3(x_1, x_2, x_7, x_10);
x_14 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__4(x_1, x_2, x_8, x_10);
lean_dec(x_2);
lean_ctor_set(x_3, 5, x_14);
lean_ctor_set(x_3, 4, x_13);
lean_ctor_set(x_3, 3, x_12);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_ctor_get(x_3, 4);
x_20 = lean_ctor_get(x_3, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_1);
x_21 = l_Lean_Expr_replaceFVarId(x_17, x_1, x_2);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = l_List_filterTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__1(x_1, x_18, x_22);
lean_inc(x_1);
x_24 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__2(x_1, x_2, x_23, x_22);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__3(x_1, x_2, x_19, x_22);
x_26 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__4(x_1, x_2, x_20, x_22);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set(x_27, 5, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_replaceFVarId___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_LocalDecl_fvarId(x_2);
x_4 = lean_name_eq(x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_isLocalDecl___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_List_any___rarg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Match_Alt_isLocalDecl___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Match_Alt_isLocalDecl(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_10);
x_11 = l_Lean_throwError___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*12);
x_24 = lean_ctor_get(x_5, 11);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_26 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_15);
lean_ctor_set(x_27, 4, x_16);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*12, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*12 + 1, x_25);
x_28 = l_Lean_throwError___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__2(x_2, x_3, x_4, x_27, x_6, x_7);
lean_dec(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_10);
x_11 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*12);
x_24 = lean_ctor_get(x_5, 11);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_26 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_15);
lean_ctor_set(x_27, 4, x_16);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*12, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*12 + 1, x_25);
x_28 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_2, x_3, x_4, x_27, x_6, x_7);
lean_dec(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Match_Alt_replaceFVarId(x_1, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type mismatch during dependent match-elimination at pattern variable '", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' with type", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nexpected type", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_3, 0);
x_17 = l_Lean_LocalDecl_fvarId(x_4);
x_18 = l_Lean_Expr_fvar___override(x_17);
x_19 = l_Lean_MessageData_ofExpr(x_18);
x_20 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__2;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_20);
x_21 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_15);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_indentExpr(x_14);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3(x_16, x_30, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_ctor_get(x_3, 0);
x_35 = l_Lean_LocalDecl_fvarId(x_4);
x_36 = l_Lean_Expr_fvar___override(x_35);
x_37 = l_Lean_MessageData_ofExpr(x_36);
x_38 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_indentExpr(x_33);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_indentExpr(x_32);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3(x_34, x_49, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_10);
if (x_51 == 0)
{
return x_10;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_10, 0);
x_53 = lean_ctor_get(x_10, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_10);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown free pattern variable", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_isLocalDecl___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_List_find_x3f___rarg(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__2;
x_14 = l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__1(x_12, x_13, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_type(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
lean_inc(x_19);
x_20 = l_Lean_Meta_isExprDefEqGuarded(x_19, x_17, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_3);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___boxed), 9, 4);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_19);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__4___rarg(x_10, x_24, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1(x_1, x_2, x_3, x_26, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_box(0);
x_35 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1(x_1, x_2, x_3, x_34, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_name_eq(x_5, x_1);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_free_object(x_3);
lean_dec(x_5);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_name_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_dec(x_7);
lean_inc(x_2);
return x_2;
}
}
}
case 2:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__1(x_1, x_2, x_11, x_12);
lean_ctor_set(x_3, 1, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__1(x_1, x_2, x_15, x_16);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
case 4:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_box(0);
x_22 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__2(x_1, x_2, x_20, x_21);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__2(x_1, x_2, x_23, x_24);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
default: 
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_replaceFVarId___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_FVarSubst_get(x_1, x_4);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; 
lean_dec(x_5);
lean_free_object(x_2);
x_7 = lean_box(1);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Meta_FVarSubst_get(x_1, x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(1);
return x_12;
}
}
}
case 2:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__1(x_1, x_14, x_15);
lean_ctor_set(x_2, 1, x_16);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__1(x_1, x_18, x_19);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
case 4:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_box(0);
x_25 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__2(x_1, x_23, x_24);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__2(x_1, x_26, x_27);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
default: 
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_applyFVarSubst___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_varsToUnderscore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Match_Example_varsToUnderscore(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Match_Example_varsToUnderscore(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(1);
return x_2;
}
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_varsToUnderscore___spec__1(x_4, x_5);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_varsToUnderscore___spec__1(x_8, x_9);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
case 4:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_box(0);
x_15 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_varsToUnderscore___spec__1(x_13, x_14);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_varsToUnderscore___spec__1(x_16, x_17);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
default: 
{
return x_1;
}
}
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
x_7 = l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Meta_Match_Example_toMessageData(x_5);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_2 = x_11;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_Match_Example_toMessageData(x_13);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_1);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
x_2 = x_20;
x_3 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_Example_toMessageData___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Match_Example_toMessageData(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Match_Example_toMessageData(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Example_toMessageData___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Example_toMessageData___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Example_toMessageData___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Example_toMessageData___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Expr_fvar___override(x_2);
x_4 = l_Lean_MessageData_ofExpr(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Example_toMessageData___closed__3;
return x_5;
}
case 2:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
x_10 = l_Lean_MessageData_ofExpr(x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = 0;
x_15 = l_Lean_MessageData_ofConstName(x_12, x_14);
x_16 = l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_16);
x_17 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_Match_Pattern_toMessageData___closed__9;
lean_inc(x_6);
x_20 = l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1(x_17, x_19, x_6);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_6, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_6, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_6, 0, x_18);
x_24 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_20);
x_27 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = 0;
x_31 = l_Lean_MessageData_ofConstName(x_29, x_30);
x_32 = l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_Match_Pattern_toMessageData___closed__9;
lean_inc(x_6);
x_37 = l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1(x_34, x_36, x_6);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_38 = x_6;
} else {
 lean_dec_ref(x_6);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(7, 2, 0);
} else {
 x_39 = x_38;
 lean_ctor_set_tag(x_39, 7);
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
case 3:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_MessageData_ofExpr(x_42);
return x_43;
}
default: 
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = l_List_mapTR_loop___at_Lean_Meta_Match_Example_toMessageData___spec__2(x_44, x_45);
x_47 = l_Lean_MessageData_ofList(x_46);
x_48 = l_Lean_Meta_Match_Example_toMessageData___closed__6;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_examplesToMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Match_Example_varsToUnderscore(x_5);
x_8 = l_Lean_Meta_Match_Example_toMessageData(x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Lean_Meta_Match_Example_varsToUnderscore(x_10);
x_13 = l_Lean_Meta_Match_Example_toMessageData(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_Lean_Meta_Match_examplesToMessageData___spec__1(x_1, x_2);
x_4 = l_Lean_Meta_Match_Pattern_toMessageData___closed__14;
x_5 = l_Lean_MessageData_joinSep(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedProblem___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedProblem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedProblem___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_withGoalOf___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Problem_toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Meta_Match_Alt_toMessageData(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Meta_Match_Alt_toMessageData(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_22;
x_2 = x_26;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_30 = x_23;
} else {
 lean_dec_ref(x_23);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_Problem_toMessageData___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_13 = lean_infer_type(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_MessageData_ofExpr(x_11);
x_17 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_MessageData_ofExpr(x_14);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_24);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_26; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_30);
x_32 = lean_infer_type(x_30, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_MessageData_ofExpr(x_30);
x_36 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_MessageData_ofExpr(x_33);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
x_1 = x_31;
x_2 = x_44;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_32, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_48 = x_32;
} else {
 lean_dec_ref(x_32);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("remaining variables: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nalternatives:", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nexamples:", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = l_List_mapM_loop___at_Lean_Meta_Match_Problem_toMessageData___spec__1(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_2);
x_13 = l_List_mapM_loop___at_Lean_Meta_Match_Problem_toMessageData___spec__2(x_12, x_2, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__2(x_15, x_2);
x_17 = l_Lean_MessageData_ofList(x_16);
x_18 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__5;
x_23 = l_Lean_MessageData_joinSep(x_10, x_22);
x_24 = l_Lean_indentD(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__7;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_ctor_get(x_3, 3);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lean_Meta_Match_examplesToMessageData(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__9;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_13, 0, x_32);
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__2(x_33, x_2);
x_36 = l_Lean_MessageData_ofList(x_35);
x_37 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__2;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__5;
x_42 = l_Lean_MessageData_joinSep(x_10, x_41);
x_43 = l_Lean_indentD(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__7;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_ctor_get(x_3, 3);
lean_inc(x_47);
lean_dec(x_3);
x_48 = l_Lean_Meta_Match_examplesToMessageData(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__9;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_34);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_9);
if (x_57 == 0)
{
return x_9;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_9, 0);
x_59 = lean_ctor_get(x_9, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_9);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Problem_toMessageData___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
x_10 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_examplesToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Match_counterExamplesToMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Match_examplesToMessageData(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Match_examplesToMessageData(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_Lean_Meta_Match_counterExamplesToMessageData___spec__1(x_1, x_2);
x_4 = l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__5;
x_5 = l_Lean_MessageData_joinSep(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_Match_toPattern(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Match_toPattern___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Meta_Match_toPattern(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Meta_Match_toPattern(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_22;
x_2 = x_26;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_30 = x_23;
} else {
 lean_dec_ref(x_23);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_extract___rarg(x_2, x_11, x_10);
x_13 = lean_array_get_size(x_2);
x_14 = l_Array_extract___rarg(x_2, x_10, x_13);
lean_dec(x_13);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2(x_15, x_16, x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_array_to_list(x_12);
x_23 = lean_array_to_list(x_19);
x_24 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_array_to_list(x_12);
x_30 = lean_array_to_list(x_25);
x_31 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected pattern", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_toPattern___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected occurrence of auxiliary declaration 'namedPattern'", 61, 61);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_toPattern___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_inaccessible_x3f(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Expr_arrayLit_x3f(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_isNamedPattern_x3f(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Meta_isMatchValue(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = l_Lean_Expr_isFVar(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_expr_eqv(x_18, x_1);
if (x_20 == 0)
{
lean_dec(x_1);
x_1 = x_18;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_5, x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Environment_find_x3f(x_29, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_31 = l_Lean_indentExpr(x_1);
x_32 = l_Lean_Meta_Match_toPattern___closed__2;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_31);
lean_ctor_set(x_25, 0, x_32);
x_33 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_34, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
if (lean_obj_tag(x_36) == 6)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_38);
x_40 = l_Lean_Meta_Match_toPattern___closed__3;
lean_inc(x_39);
x_41 = lean_mk_array(x_39, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
lean_inc(x_1);
x_44 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_41, x_43);
x_45 = lean_array_get_size(x_44);
x_46 = lean_ctor_get(x_37, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 4);
lean_inc(x_47);
x_48 = lean_nat_add(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
x_49 = lean_nat_dec_eq(x_45, x_48);
lean_dec(x_48);
lean_dec(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_24);
x_50 = l_Lean_indentExpr(x_1);
x_51 = l_Lean_Meta_Match_toPattern___closed__2;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_50);
lean_ctor_set(x_25, 0, x_51);
x_52 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_25);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_53, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_25);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = l_Lean_Meta_Match_toPattern___lambda__1(x_37, x_44, x_24, x_59, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_44);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_36);
lean_dec(x_24);
x_61 = l_Lean_indentExpr(x_1);
x_62 = l_Lean_Meta_Match_toPattern___closed__2;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_61);
lean_ctor_set(x_25, 0, x_62);
x_63 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_25);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_64, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Environment_find_x3f(x_68, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_24);
x_70 = l_Lean_indentExpr(x_1);
x_71 = l_Lean_Meta_Match_toPattern___closed__2;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_74, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
lean_dec(x_69);
if (lean_obj_tag(x_76) == 6)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_78);
x_80 = l_Lean_Meta_Match_toPattern___closed__3;
lean_inc(x_79);
x_81 = lean_mk_array(x_79, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_79, x_82);
lean_dec(x_79);
lean_inc(x_1);
x_84 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_81, x_83);
x_85 = lean_array_get_size(x_84);
x_86 = lean_ctor_get(x_77, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_77, 4);
lean_inc(x_87);
x_88 = lean_nat_add(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
x_89 = lean_nat_dec_eq(x_85, x_88);
lean_dec(x_88);
lean_dec(x_85);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_84);
lean_dec(x_77);
lean_dec(x_24);
x_90 = l_Lean_indentExpr(x_1);
x_91 = l_Lean_Meta_Match_toPattern___closed__2;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_94, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
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
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_1);
x_100 = lean_box(0);
x_101 = l_Lean_Meta_Match_toPattern___lambda__1(x_77, x_84, x_24, x_100, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_84);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_76);
lean_dec(x_24);
x_102 = l_Lean_indentExpr(x_1);
x_103 = l_Lean_Meta_Match_toPattern___closed__2;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_106, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_22);
x_108 = l_Lean_indentExpr(x_1);
x_109 = l_Lean_Meta_Match_toPattern___closed__2;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_112, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_17);
if (x_114 == 0)
{
return x_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_10, 0, x_119);
return x_10;
}
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_10, 1);
lean_inc(x_120);
lean_dec(x_10);
x_121 = l_Lean_Expr_isFVar(x_1);
if (x_121 == 0)
{
lean_object* x_122; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_122 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_expr_eqv(x_123, x_1);
if (x_125 == 0)
{
lean_dec(x_1);
x_1 = x_123;
x_6 = x_124;
goto _start;
}
else
{
lean_object* x_127; 
lean_dec(x_123);
x_127 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_127) == 4)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_get(x_5, x_124);
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
lean_dec(x_131);
x_135 = l_Lean_Environment_find_x3f(x_134, x_128);
lean_dec(x_128);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_129);
x_136 = l_Lean_indentExpr(x_1);
x_137 = l_Lean_Meta_Match_toPattern___closed__2;
if (lean_is_scalar(x_133)) {
 x_138 = lean_alloc_ctor(7, 2, 0);
} else {
 x_138 = x_133;
 lean_ctor_set_tag(x_138, 7);
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_140, x_2, x_3, x_4, x_5, x_132);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_141;
}
else
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_135, 0);
lean_inc(x_142);
lean_dec(x_135);
if (lean_obj_tag(x_142) == 6)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_unsigned_to_nat(0u);
x_145 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_144);
x_146 = l_Lean_Meta_Match_toPattern___closed__3;
lean_inc(x_145);
x_147 = lean_mk_array(x_145, x_146);
x_148 = lean_unsigned_to_nat(1u);
x_149 = lean_nat_sub(x_145, x_148);
lean_dec(x_145);
lean_inc(x_1);
x_150 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_147, x_149);
x_151 = lean_array_get_size(x_150);
x_152 = lean_ctor_get(x_143, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_143, 4);
lean_inc(x_153);
x_154 = lean_nat_add(x_152, x_153);
lean_dec(x_153);
lean_dec(x_152);
x_155 = lean_nat_dec_eq(x_151, x_154);
lean_dec(x_154);
lean_dec(x_151);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_150);
lean_dec(x_143);
lean_dec(x_129);
x_156 = l_Lean_indentExpr(x_1);
x_157 = l_Lean_Meta_Match_toPattern___closed__2;
if (lean_is_scalar(x_133)) {
 x_158 = lean_alloc_ctor(7, 2, 0);
} else {
 x_158 = x_133;
 lean_ctor_set_tag(x_158, 7);
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_160, x_2, x_3, x_4, x_5, x_132);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_133);
lean_dec(x_1);
x_166 = lean_box(0);
x_167 = l_Lean_Meta_Match_toPattern___lambda__1(x_143, x_150, x_129, x_166, x_2, x_3, x_4, x_5, x_132);
lean_dec(x_150);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_142);
lean_dec(x_129);
x_168 = l_Lean_indentExpr(x_1);
x_169 = l_Lean_Meta_Match_toPattern___closed__2;
if (lean_is_scalar(x_133)) {
 x_170 = lean_alloc_ctor(7, 2, 0);
} else {
 x_170 = x_133;
 lean_ctor_set_tag(x_170, 7);
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_172, x_2, x_3, x_4, x_5, x_132);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_127);
x_174 = l_Lean_indentExpr(x_1);
x_175 = l_Lean_Meta_Match_toPattern___closed__2;
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
x_177 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_178, x_2, x_3, x_4, x_5, x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_122, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_122, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_182 = x_122;
} else {
 lean_dec_ref(x_122);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_120);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_187 = !lean_is_exclusive(x_10);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_10, 0);
lean_dec(x_188);
x_189 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_189, 0, x_1);
lean_ctor_set(x_10, 0, x_189);
return x_10;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_10, 1);
lean_inc(x_190);
lean_dec(x_10);
x_191 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_191, 0, x_1);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_10);
if (x_193 == 0)
{
return x_10;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_10, 0);
x_195 = lean_ctor_get(x_10, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_10);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_1);
x_197 = lean_ctor_get(x_9, 0);
lean_inc(x_197);
lean_dec(x_9);
x_198 = lean_unsigned_to_nat(0u);
x_199 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_197, x_198);
x_200 = lean_unsigned_to_nat(2u);
x_201 = lean_nat_sub(x_199, x_200);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_nat_sub(x_201, x_202);
lean_dec(x_201);
x_204 = l_Lean_Expr_getRevArg_x21(x_197, x_203);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_205 = l_Lean_Meta_Match_toPattern(x_204, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_ctor_get(x_205, 1);
x_209 = lean_nat_sub(x_199, x_202);
x_210 = lean_nat_sub(x_209, x_202);
lean_dec(x_209);
x_211 = l_Lean_Expr_getRevArg_x21(x_197, x_210);
if (lean_obj_tag(x_211) == 1)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_unsigned_to_nat(3u);
x_214 = lean_nat_sub(x_199, x_213);
lean_dec(x_199);
x_215 = lean_nat_sub(x_214, x_202);
lean_dec(x_214);
x_216 = l_Lean_Expr_getRevArg_x21(x_197, x_215);
lean_dec(x_197);
if (lean_obj_tag(x_216) == 1)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_218, 0, x_212);
lean_ctor_set(x_218, 1, x_207);
lean_ctor_set(x_218, 2, x_217);
lean_ctor_set(x_205, 0, x_218);
return x_205;
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_216);
lean_dec(x_212);
lean_free_object(x_205);
lean_dec(x_207);
x_219 = l_Lean_Meta_Match_toPattern___closed__5;
x_220 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_219, x_2, x_3, x_4, x_5, x_208);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_211);
lean_free_object(x_205);
lean_dec(x_207);
lean_dec(x_199);
lean_dec(x_197);
x_221 = l_Lean_Meta_Match_toPattern___closed__5;
x_222 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_221, x_2, x_3, x_4, x_5, x_208);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_205, 0);
x_224 = lean_ctor_get(x_205, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_205);
x_225 = lean_nat_sub(x_199, x_202);
x_226 = lean_nat_sub(x_225, x_202);
lean_dec(x_225);
x_227 = l_Lean_Expr_getRevArg_x21(x_197, x_226);
if (lean_obj_tag(x_227) == 1)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_unsigned_to_nat(3u);
x_230 = lean_nat_sub(x_199, x_229);
lean_dec(x_199);
x_231 = lean_nat_sub(x_230, x_202);
lean_dec(x_230);
x_232 = l_Lean_Expr_getRevArg_x21(x_197, x_231);
lean_dec(x_197);
if (lean_obj_tag(x_232) == 1)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_234, 0, x_228);
lean_ctor_set(x_234, 1, x_223);
lean_ctor_set(x_234, 2, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_224);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_232);
lean_dec(x_228);
lean_dec(x_223);
x_236 = l_Lean_Meta_Match_toPattern___closed__5;
x_237 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_236, x_2, x_3, x_4, x_5, x_224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_227);
lean_dec(x_223);
lean_dec(x_199);
lean_dec(x_197);
x_238 = l_Lean_Meta_Match_toPattern___closed__5;
x_239 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_238, x_2, x_3, x_4, x_5, x_224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_239;
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_240 = !lean_is_exclusive(x_205);
if (x_240 == 0)
{
return x_205;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_205, 0);
x_242 = lean_ctor_get(x_205, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_205);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
}
else
{
lean_object* x_244; uint8_t x_245; 
lean_dec(x_1);
x_244 = lean_ctor_get(x_8, 0);
lean_inc(x_244);
lean_dec(x_8);
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_244, 0);
x_247 = lean_ctor_get(x_244, 1);
x_248 = lean_box(0);
x_249 = l_List_mapM_loop___at_Lean_Meta_Match_toPattern___spec__3(x_247, x_248, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_249) == 0)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_249, 0);
lean_ctor_set_tag(x_244, 4);
lean_ctor_set(x_244, 1, x_251);
lean_ctor_set(x_249, 0, x_244);
return x_249;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_249, 0);
x_253 = lean_ctor_get(x_249, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_249);
lean_ctor_set_tag(x_244, 4);
lean_ctor_set(x_244, 1, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_244);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
else
{
uint8_t x_255; 
lean_free_object(x_244);
lean_dec(x_246);
x_255 = !lean_is_exclusive(x_249);
if (x_255 == 0)
{
return x_249;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_249, 0);
x_257 = lean_ctor_get(x_249, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_249);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_244, 0);
x_260 = lean_ctor_get(x_244, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_244);
x_261 = lean_box(0);
x_262 = l_List_mapM_loop___at_Lean_Meta_Match_toPattern___spec__3(x_260, x_261, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_266, 0, x_259);
lean_ctor_set(x_266, 1, x_263);
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_265;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_259);
x_268 = lean_ctor_get(x_262, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_262, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_270 = x_262;
} else {
 lean_dec_ref(x_262);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_7);
if (x_272 == 0)
{
lean_object* x_273; 
lean_ctor_set_tag(x_7, 0);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_7);
lean_ctor_set(x_273, 1, x_6);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_7, 0);
lean_inc(x_274);
lean_dec(x_7);
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_274);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_6);
return x_276;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Match_toPattern___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Match_toPattern___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseArraySizes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Match_mkNamedPattern___closed__1 = _init_l_Lean_Meta_Match_mkNamedPattern___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkNamedPattern___closed__1);
l_Lean_Meta_Match_mkNamedPattern___closed__2 = _init_l_Lean_Meta_Match_mkNamedPattern___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkNamedPattern___closed__2);
l_Lean_Meta_Match_instInhabitedPattern___closed__1 = _init_l_Lean_Meta_Match_instInhabitedPattern___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern___closed__1);
l_Lean_Meta_Match_instInhabitedPattern___closed__2 = _init_l_Lean_Meta_Match_instInhabitedPattern___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern___closed__2);
l_Lean_Meta_Match_instInhabitedPattern = _init_l_Lean_Meta_Match_instInhabitedPattern();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern);
l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__1 = _init_l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__1);
l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__2 = _init_l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__2();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__2);
l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__3 = _init_l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__3();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Match_Pattern_toMessageData___spec__1___closed__3);
l_Lean_Meta_Match_Pattern_toMessageData___closed__1 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__1);
l_Lean_Meta_Match_Pattern_toMessageData___closed__2 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__2);
l_Lean_Meta_Match_Pattern_toMessageData___closed__3 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
l_Lean_Meta_Match_Pattern_toMessageData___closed__4 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__4);
l_Lean_Meta_Match_Pattern_toMessageData___closed__5 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__5);
l_Lean_Meta_Match_Pattern_toMessageData___closed__6 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__6);
l_Lean_Meta_Match_Pattern_toMessageData___closed__7 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__7);
l_Lean_Meta_Match_Pattern_toMessageData___closed__8 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__8);
l_Lean_Meta_Match_Pattern_toMessageData___closed__9 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__9();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__9);
l_Lean_Meta_Match_Pattern_toMessageData___closed__10 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__10();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__10);
l_Lean_Meta_Match_Pattern_toMessageData___closed__11 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__11);
l_Lean_Meta_Match_Pattern_toMessageData___closed__12 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__12();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__12);
l_Lean_Meta_Match_Pattern_toMessageData___closed__13 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__13);
l_Lean_Meta_Match_Pattern_toMessageData___closed__14 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__14();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__14);
l_Lean_Meta_Match_Pattern_toMessageData___closed__15 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__15);
l_Lean_Meta_Match_Pattern_toMessageData___closed__16 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__16();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__16);
l_Lean_Meta_Match_Pattern_toMessageData___closed__17 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__17();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__17);
l_Lean_Meta_Match_Pattern_toMessageData___closed__18 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__18();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__18);
l_Lean_Meta_Match_Pattern_hasExprMVar___closed__1 = _init_l_Lean_Meta_Match_Pattern_hasExprMVar___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_hasExprMVar___closed__1);
l_Lean_Meta_Match_Pattern_hasExprMVar___closed__2 = _init_l_Lean_Meta_Match_Pattern_hasExprMVar___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_hasExprMVar___closed__2);
l_Lean_Meta_Match_instInhabitedAlt___closed__1 = _init_l_Lean_Meta_Match_instInhabitedAlt___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt___closed__1);
l_Lean_Meta_Match_instInhabitedAlt = _init_l_Lean_Meta_Match_instInhabitedAlt();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt);
l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__1 = _init_l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__1);
l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2 = _init_l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__1___closed__2);
l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__1);
l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__2);
l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__3 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__3);
l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__4 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Match_Alt_toMessageData___spec__3___closed__4);
l_Lean_Meta_Match_Alt_toMessageData___closed__1 = _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Alt_toMessageData___closed__1);
l_Lean_Meta_Match_Alt_toMessageData___closed__2 = _init_l_Lean_Meta_Match_Alt_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Alt_toMessageData___closed__2);
l_Lean_Meta_Match_Alt_toMessageData___closed__3 = _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_Alt_toMessageData___closed__3);
l_Lean_Meta_Match_Alt_toMessageData___closed__4 = _init_l_Lean_Meta_Match_Alt_toMessageData___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_Alt_toMessageData___closed__4);
l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__1 = _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__1);
l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__2 = _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__2);
l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__3 = _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__3);
l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__4 = _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__4);
l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__5 = _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__5);
l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__6 = _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__2___closed__6);
l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__1 = _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__1);
l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__2 = _init_l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__2);
l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1 = _init_l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1);
l_Lean_Meta_Match_Example_toMessageData___closed__1 = _init_l_Lean_Meta_Match_Example_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Example_toMessageData___closed__1);
l_Lean_Meta_Match_Example_toMessageData___closed__2 = _init_l_Lean_Meta_Match_Example_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Example_toMessageData___closed__2);
l_Lean_Meta_Match_Example_toMessageData___closed__3 = _init_l_Lean_Meta_Match_Example_toMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_Example_toMessageData___closed__3);
l_Lean_Meta_Match_Example_toMessageData___closed__4 = _init_l_Lean_Meta_Match_Example_toMessageData___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_Example_toMessageData___closed__4);
l_Lean_Meta_Match_Example_toMessageData___closed__5 = _init_l_Lean_Meta_Match_Example_toMessageData___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_Example_toMessageData___closed__5);
l_Lean_Meta_Match_Example_toMessageData___closed__6 = _init_l_Lean_Meta_Match_Example_toMessageData___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_Example_toMessageData___closed__6);
l_Lean_Meta_Match_instInhabitedProblem___closed__1 = _init_l_Lean_Meta_Match_instInhabitedProblem___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedProblem___closed__1);
l_Lean_Meta_Match_instInhabitedProblem = _init_l_Lean_Meta_Match_instInhabitedProblem();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedProblem);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__1 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__1);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__2 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__2);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__3 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__3);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__4 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__4);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__5 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__5);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__6 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__6);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__7 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__7);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__8 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__8);
l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__9 = _init_l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lambda__1___closed__9);
l_Lean_Meta_Match_toPattern___closed__1 = _init_l_Lean_Meta_Match_toPattern___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__1);
l_Lean_Meta_Match_toPattern___closed__2 = _init_l_Lean_Meta_Match_toPattern___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__2);
l_Lean_Meta_Match_toPattern___closed__3 = _init_l_Lean_Meta_Match_toPattern___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__3);
l_Lean_Meta_Match_toPattern___closed__4 = _init_l_Lean_Meta_Match_toPattern___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__4);
l_Lean_Meta_Match_toPattern___closed__5 = _init_l_Lean_Meta_Match_toPattern___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
