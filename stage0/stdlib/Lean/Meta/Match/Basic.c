// Lean compiler output
// Module: Lean.Meta.Match.Basic
// Imports: public import Lean.Meta.CollectFVars public import Lean.Meta.Match.CaseArraySizes
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
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedAltLHS_default;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkNamedPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_instInhabitedProblem_default___closed__1;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBase;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1;
static lean_object* l_Lean_Meta_Match_instInhabitedAlt_default___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
static lean_object* l_Lean_Meta_Match_instInhabitedPattern_default___closed__3;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
extern lean_object* l_Lean_instInhabitedMVarId_default;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_instInhabitedPattern_default___closed__0;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__2;
lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6;
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__1;
static lean_object* l_Lean_Meta_Match_instInhabitedProblem_default___closed__0;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedPattern_default;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__5;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherResult_ctorIdx(lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedAlt_default;
static lean_object* l_Lean_Meta_Match_instInhabitedPattern_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__14;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_mkInaccessible(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedAltLHS;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isNamedPattern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inaccessible_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object*);
static lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_ctorIdx(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkNamedPattern___closed__0;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Meta_Match_toPattern___closed__3;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__10;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__12;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object*);
lean_object* l_Lean_LocalDecl_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1;
static lean_object* l_Lean_Meta_Match_toPattern___closed__1;
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__1;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedProblem_default;
static lean_object* l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__5;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__2;
static lean_object* l_Lean_Meta_Match_mkNamedPattern___closed__1;
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2;
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__13;
static lean_object* l_Lean_Meta_Match_instInhabitedPattern_default___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__0;
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__3;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_ctorIdx(lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__7;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__0;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedAlt;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
static lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__8;
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__3;
static lean_object* l_Lean_Meta_Match_toPattern___closed__0;
static lean_object* l_Lean_Meta_Match_toPattern___closed__2;
static lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkNamedPattern___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_toPattern___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_congrEqn1ThmSuffix;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedPattern;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedProblem;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__15;
static lean_object* _init_l_Lean_Meta_Match_mkNamedPattern___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namedPattern", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkNamedPattern___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkNamedPattern___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkNamedPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkNamedPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Meta_Match_mkNamedPattern___closed__1;
x_10 = l_Lean_Meta_Match_mkNamedPattern___closed__2;
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_array_push(x_11, x_3);
x_13 = lean_array_push(x_12, x_2);
x_14 = l_Lean_Meta_mkAppM(x_9, x_13, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkNamedPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_mkNamedPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isNamedPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Expr_consumeMData(x_1);
x_3 = l_Lean_Expr_getAppNumArgs(x_2);
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Expr_getAppFn(x_2);
lean_dec_ref(x_2);
x_7 = l_Lean_Expr_consumeMData(x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_Meta_Match_mkNamedPattern___closed__1;
x_9 = l_Lean_Expr_isConstOf(x_7, x_8);
lean_dec_ref(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_isNamedPattern(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = l_Lean_Expr_consumeMData(x_1);
x_7 = l_Lean_Expr_getAppNumArgs(x_2);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
x_3 = x_9;
goto block_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Expr_getAppFn(x_2);
x_11 = l_Lean_Expr_consumeMData(x_10);
lean_dec_ref(x_10);
x_12 = l_Lean_Meta_Match_mkNamedPattern___closed__1;
x_13 = l_Lean_Expr_isConstOf(x_11, x_12);
lean_dec_ref(x_11);
x_3 = x_13;
goto block_6;
}
block_6:
{
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isNamedPattern_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_isNamedPattern_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_Pattern_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_apply_3(x_2, x_13, x_14, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_apply_1(x_2, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Match_Pattern_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Pattern_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_instInhabitedPattern_default___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_instInhabitedPattern_default___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_instInhabitedPattern_default___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedPattern_default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedPattern_default;
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2;
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
x_12 = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".(", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__10;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Pattern_toMessageData___closed__14;
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
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Meta_Match_Pattern_toMessageData___closed__1;
x_4 = l_Lean_MessageData_ofExpr(x_2);
x_5 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
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
lean_dec_ref(x_1);
x_9 = l_Lean_mkFVar(x_8);
x_10 = l_Lean_MessageData_ofExpr(x_9);
return x_10;
}
case 2:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = l_Lean_MessageData_ofName(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Lean_Meta_Match_Pattern_toMessageData___closed__5;
x_16 = l_Lean_MessageData_ofName(x_14);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
x_19 = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(x_18, x_11);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
case 3:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_23);
lean_dec_ref(x_1);
x_24 = l_Lean_MessageData_ofExpr(x_23);
return x_24;
}
case 4:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 0);
lean_dec(x_27);
x_28 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_29 = lean_box(0);
x_30 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(x_26, x_29);
x_31 = l_Lean_Meta_Match_Pattern_toMessageData___closed__11;
x_32 = l_Lean_MessageData_joinSep(x_30, x_31);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_28);
x_33 = l_Lean_Meta_Match_Pattern_toMessageData___closed__13;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
x_37 = lean_box(0);
x_38 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(x_35, x_37);
x_39 = l_Lean_Meta_Match_Pattern_toMessageData___closed__11;
x_40 = l_Lean_MessageData_joinSep(x_38, x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_Match_Pattern_toMessageData___closed__13;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
default: 
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_1);
x_46 = l_Lean_mkFVar(x_44);
x_47 = l_Lean_MessageData_ofExpr(x_46);
x_48 = l_Lean_Meta_Match_Pattern_toMessageData___closed__15;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_Match_Pattern_toMessageData(x_45);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = l_List_reverse___redArg(x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
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
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_14 = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(x_1, x_12, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_15);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_22 = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(x_1, x_20, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
x_2 = x_21;
x_3 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_27 = x_22;
} else {
 lean_dec_ref(x_22);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (x_1 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_Lean_mkInaccessible(x_12);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_mkInaccessible(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
case 1:
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = l_Lean_mkFVar(x_18);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_mkFVar(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_dec_ref(x_2);
x_27 = lean_box(0);
x_28 = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(x_1, x_26, x_27, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_mkConst(x_23, x_24);
x_32 = l_List_appendTR___redArg(x_25, x_30);
x_33 = lean_array_mk(x_32);
x_34 = l_Lean_mkAppN(x_31, x_33);
lean_dec_ref(x_33);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = l_Lean_mkConst(x_23, x_24);
x_37 = l_List_appendTR___redArg(x_25, x_35);
x_38 = lean_array_mk(x_37);
x_39 = l_Lean_mkAppN(x_36, x_38);
lean_dec_ref(x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
case 3:
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_ctor_set_tag(x_2, 0);
return x_2;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
case 4:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec_ref(x_2);
x_49 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_50 = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(x_1, x_48, x_49, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_Meta_mkArrayLit(x_47, x_51, x_3, x_4, x_5, x_6);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec_ref(x_47);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
default: 
{
if (x_1 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_56);
lean_dec_ref(x_2);
x_2 = x_56;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_dec_ref(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_61 = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(x_1, x_59, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_mkFVar(x_58);
x_64 = l_Lean_mkFVar(x_60);
x_65 = l_Lean_Meta_Match_mkNamedPattern(x_63, x_64, x_62, x_3, x_4, x_5, x_6);
return x_65;
}
else
{
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(x_2, x_1, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_Match_Pattern_toExpr(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
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
lean_dec_ref(x_4);
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
lean_dec_ref(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_Lean_Meta_FVarSubst_find_x3f(x_1, x_9);
lean_dec(x_1);
if (lean_obj_tag(x_10) == 0)
{
return x_2;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec_ref(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
case 2:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
x_19 = lean_box(0);
lean_inc(x_1);
x_20 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(x_1, x_17, x_19);
x_21 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(x_1, x_18, x_19);
lean_ctor_set(x_2, 3, x_21);
lean_ctor_set(x_2, 2, x_20);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_26 = lean_box(0);
lean_inc(x_1);
x_27 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(x_1, x_24, x_26);
x_28 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(x_1, x_25, x_26);
x_29 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
return x_29;
}
}
case 3:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = l_Lean_Meta_FVarSubst_apply(x_1, x_31);
lean_dec_ref(x_31);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_Lean_Meta_FVarSubst_apply(x_1, x_33);
lean_dec_ref(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
case 4:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_39 = l_Lean_Meta_FVarSubst_apply(x_1, x_37);
lean_dec_ref(x_37);
x_40 = lean_box(0);
x_41 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(x_1, x_38, x_40);
lean_ctor_set(x_2, 1, x_41);
lean_ctor_set(x_2, 0, x_39);
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
lean_inc(x_1);
x_44 = l_Lean_Meta_FVarSubst_apply(x_1, x_42);
lean_dec_ref(x_42);
x_45 = lean_box(0);
x_46 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(x_1, x_43, x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
default: 
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_ctor_get(x_2, 1);
x_51 = lean_ctor_get(x_2, 2);
x_52 = l_Lean_Meta_FVarSubst_find_x3f(x_1, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_50);
lean_ctor_set(x_2, 1, x_53);
return x_2;
}
else
{
lean_dec_ref(x_52);
lean_free_object(x_2);
lean_dec(x_51);
lean_dec(x_49);
x_2 = x_50;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_2);
x_58 = l_Lean_Meta_FVarSubst_find_x3f(x_1, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_56);
x_60 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_57);
return x_60;
}
else
{
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_55);
x_2 = x_56;
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
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasExprMVar(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Expr_hasExprMVar(x_2);
lean_dec_ref(x_2);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Pattern_hasExprMVar___lam__0___boxed), 1, 0);
x_7 = l_List_any___redArg(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Pattern_hasExprMVar___boxed), 1, 0);
x_9 = l_List_any___redArg(x_5, x_8);
return x_9;
}
else
{
lean_dec(x_5);
return x_7;
}
}
case 3:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = l_Lean_Expr_hasExprMVar(x_10);
lean_dec_ref(x_10);
return x_11;
}
case 5:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_1 = x_12;
goto _start;
}
case 4:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = l_Lean_Expr_hasExprMVar(x_14);
lean_dec_ref(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Pattern_hasExprMVar___boxed), 1, 0);
x_18 = l_List_any___redArg(x_15, x_17);
return x_18;
}
else
{
lean_dec(x_15);
return x_16;
}
}
default: 
{
uint8_t x_19; 
lean_dec_ref(x_1);
x_19 = 0;
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_Pattern_hasExprMVar___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_Expr_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_dec_ref(x_12);
x_1 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_Meta_Match_Pattern_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_dec_ref(x_12);
x_1 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_st_ref_take(x_2);
x_11 = l_Lean_CollectFVars_State_add(x_10, x_9);
x_12 = lean_st_ref_set(x_2, x_11);
x_13 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_st_ref_take(x_2);
x_16 = l_Lean_CollectFVars_State_add(x_15, x_14);
x_17 = lean_st_ref_set(x_2, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
x_23 = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(x_21, x_2, x_3, x_4, x_5, x_6);
return x_23;
}
else
{
lean_dec(x_21);
return x_22;
}
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = l_Lean_Expr_collectFVars(x_24, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(x_25, x_2, x_3, x_4, x_5, x_6);
return x_27;
}
else
{
lean_dec(x_25);
return x_26;
}
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
lean_dec_ref(x_1);
x_31 = lean_st_ref_take(x_2);
x_32 = l_Lean_CollectFVars_State_add(x_31, x_28);
x_33 = l_Lean_CollectFVars_State_add(x_32, x_30);
x_34 = lean_st_ref_set(x_2, x_33);
x_1 = x_29;
goto _start;
}
default: 
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_1);
x_37 = l_Lean_Expr_collectFVars(x_36, x_2, x_3, x_4, x_5, x_6);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_Pattern_collectFVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_11, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_16, x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_17;
x_2 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_Lean_Meta_Match_instantiatePatternMVars(x_11, x_3, x_4, x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = l_Lean_Meta_Match_instantiatePatternMVars(x_16, x_3, x_4, x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_17;
x_2 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_8, x_3);
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
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_1, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
case 3:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_21, x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_1, 0, x_24);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_1, 0, x_25);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_27, x_3);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_29);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
case 2:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
x_36 = lean_box(0);
x_37 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(x_34, x_36, x_2, x_3, x_4, x_5);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(x_35, x_36, x_2, x_3, x_4, x_5);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_38);
lean_ctor_set(x_39, 0, x_1);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_1, 3, x_42);
lean_ctor_set(x_1, 2, x_38);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_1);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 2);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(x_46, x_48, x_2, x_3, x_4, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(x_47, x_48, x_2, x_3, x_4, x_5);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_52);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
case 5:
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_1);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_1, 1);
x_58 = l_Lean_Meta_Match_instantiatePatternMVars(x_57, x_2, x_3, x_4, x_5);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_58, 0, x_1);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
lean_ctor_set(x_1, 1, x_61);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_1);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
x_65 = lean_ctor_get(x_1, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_66 = l_Lean_Meta_Match_instantiatePatternMVars(x_64, x_2, x_3, x_4, x_5);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_65);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 4:
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_1);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_ctor_get(x_1, 1);
x_74 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_72, x_3);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_box(0);
x_77 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(x_73, x_76, x_2, x_3, x_4, x_5);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_ctor_set(x_1, 1, x_79);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set(x_77, 0, x_1);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
lean_ctor_set(x_1, 1, x_80);
lean_ctor_set(x_1, 0, x_75);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_1);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_1);
x_84 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_82, x_3);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_box(0);
x_87 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(x_83, x_86, x_2, x_3, x_4, x_5);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
default: 
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_1);
return x_92;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Match_instantiatePatternMVars(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_AltLHS_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAltLHS_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAltLHS() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedAltLHS_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_LocalDecl_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_dec_ref(x_12);
x_1 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_Meta_Match_Pattern_collectFVars(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_dec_ref(x_12);
x_1 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(x_9, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_AltLHS_collectFVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_ctor_set(x_1, 3, x_8);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_1, 3, x_9);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_17 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_14, x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_19 = x_17;
} else {
 lean_dec_ref(x_17);
 x_19 = lean_box(0);
}
x_20 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*4 + 1, x_16);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_1, 3);
x_24 = lean_ctor_get(x_1, 4);
x_25 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_23, x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_24, x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_1, 4, x_29);
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_1, 4, x_30);
lean_ctor_set(x_1, 3, x_26);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_1);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
x_36 = lean_ctor_get(x_1, 4);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_39 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_35, x_2);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(x_36, x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*5, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*5 + 1, x_38);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(x_11, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(x_16, x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_17;
x_2 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_box(0);
x_11 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(x_8, x_10, x_2, x_3, x_4, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(x_9, x_10, x_2, x_3, x_4, x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_1, 2, x_15);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_1, 2, x_16);
lean_ctor_set(x_1, 1, x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(x_19, x_21, x_2, x_3, x_4, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(x_20, x_21, x_2, x_3, x_4, x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_25);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Match_instantiateAltLHSMVars(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_Alt_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_instInhabitedPattern_default___closed__2;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedAlt_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedAlt_default;
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":(", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_7 = l_Lean_LocalDecl_toExpr(x_5);
x_8 = l_Lean_MessageData_ofExpr(x_7);
x_9 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_LocalDecl_type(x_5);
lean_dec(x_5);
x_12 = l_Lean_MessageData_ofExpr(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_15);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_17);
x_19 = l_Lean_LocalDecl_toExpr(x_17);
x_20 = l_Lean_MessageData_ofExpr(x_19);
x_21 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_LocalDecl_type(x_17);
lean_dec(x_17);
x_24 = l_Lean_MessageData_ofExpr(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
x_1 = x_18;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  | ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ≋ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__1;
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_2);
x_12 = l_Lean_MessageData_ofExpr(x_9);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_12);
x_13 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__3;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_MessageData_ofExpr(x_10);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_8;
x_2 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__1;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_MessageData_ofExpr(x_19);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_22);
x_24 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__3;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_ofExpr(x_20);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_1 = x_18;
x_2 = x_27;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
x_34 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__1;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(7, 2, 0);
} else {
 x_35 = x_33;
 lean_ctor_set_tag(x_35, 7);
}
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_MessageData_ofExpr(x_31);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__3;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_MessageData_ofExpr(x_32);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_1 = x_30;
x_2 = x_41;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg(x_2, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" |- ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Alt_toMessageData___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" => ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Alt_toMessageData___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_box(0);
lean_inc(x_8);
x_12 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(x_8, x_11);
x_13 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(x_12, x_11);
x_14 = l_Lean_MessageData_ofList(x_13);
x_15 = l_Lean_Meta_Match_Alt_toMessageData___closed__1;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(x_9, x_11);
x_18 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(x_17, x_11);
x_19 = l_Lean_MessageData_ofList(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_Match_Alt_toMessageData___closed__3;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_MessageData_ofExpr(x_7);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed), 7, 2);
lean_closure_set(x_25, 0, x_10);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___redArg(x_8, x_25, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_Alt_toMessageData___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Match_Alt_toMessageData(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
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
lean_dec_ref(x_4);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(x_1, x_5, x_9);
lean_inc(x_1);
x_11 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(x_1, x_6, x_9);
x_12 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(x_1, x_7, x_9);
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
lean_dec_ref(x_15);
x_20 = lean_box(0);
lean_inc(x_1);
x_21 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(x_1, x_16, x_20);
lean_inc(x_1);
x_22 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(x_1, x_17, x_20);
x_23 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(x_1, x_18, x_20);
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
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
x_9 = l_Lean_instBEqFVarId_beq(x_8, x_1);
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
x_15 = l_Lean_instBEqFVarId_beq(x_14, x_1);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_List_reverse___redArg(x_4);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_5 = l_List_reverse___redArg(x_4);
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
lean_inc_ref(x_2);
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
lean_inc_ref(x_2);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_List_reverse___redArg(x_4);
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
lean_dec_ref(x_5);
x_10 = lean_box(0);
x_11 = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(x_1, x_6, x_10);
lean_inc(x_1);
x_12 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(x_1, x_2, x_11, x_10);
lean_inc_ref(x_2);
lean_inc(x_1);
x_13 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(x_1, x_2, x_7, x_10);
x_14 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(x_1, x_2, x_8, x_10);
lean_dec_ref(x_2);
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
lean_dec_ref(x_17);
x_22 = lean_box(0);
x_23 = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(x_1, x_18, x_22);
lean_inc(x_1);
x_24 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(x_1, x_2, x_23, x_22);
lean_inc_ref(x_2);
lean_inc(x_1);
x_25 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(x_1, x_2, x_19, x_22);
x_26 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(x_1, x_2, x_20, x_22);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_LocalDecl_fvarId(x_2);
x_4 = l_Lean_instBEqFVarId_beq(x_3, x_1);
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
lean_dec_ref(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_isLocalDecl___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_List_any___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Match_Alt_isLocalDecl___lam__0(x_1, x_2);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_Example_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Match_Example_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Example_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___redArg(x_4);
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_dec_ref(x_3);
lean_inc(x_2);
return x_2;
}
}
case 2:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(x_1, x_2, x_7, x_8);
lean_ctor_set(x_3, 1, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(x_1, x_2, x_11, x_12);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
case 4:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(x_1, x_2, x_16, x_17);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(x_1, x_2, x_19, x_20);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
default: 
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
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
lean_dec_ref(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_5);
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
lean_dec_ref(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_9);
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
x_16 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(x_1, x_14, x_15);
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
x_20 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(x_1, x_18, x_19);
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
x_25 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(x_1, x_23, x_24);
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
x_28 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(x_1, x_26, x_27);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
lean_dec_ref(x_1);
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
x_6 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(x_4, x_5);
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
x_10 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(x_8, x_9);
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
x_15 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(x_13, x_14);
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
x_18 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(x_16, x_17);
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
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_7 = l_Lean_Meta_Match_Example_toMessageData(x_4);
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
x_12 = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_Match_Example_toMessageData(x_10);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Example_toMessageData___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Example_toMessageData___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Example_toMessageData___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Example_toMessageData___closed__4;
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
lean_dec_ref(x_1);
x_3 = l_Lean_mkFVar(x_2);
x_4 = l_Lean_MessageData_ofExpr(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_Example_toMessageData___closed__2;
return x_5;
}
case 2:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = l_Lean_MessageData_ofExpr(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_inc(x_6);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_Meta_Match_Pattern_toMessageData___closed__5;
x_15 = 0;
x_16 = l_Lean_MessageData_ofConstName(x_12, x_15);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
x_17 = l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
x_18 = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(x_17, x_6);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Lean_Meta_Match_Pattern_toMessageData___closed__5;
x_24 = 0;
x_25 = l_Lean_MessageData_ofConstName(x_22, x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
x_28 = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(x_27, x_6);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
case 3:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_1);
x_33 = l_Lean_MessageData_ofExpr(x_32);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec_ref(x_1);
x_35 = l_Lean_Meta_Match_Example_toMessageData___closed__5;
x_36 = lean_box(0);
x_37 = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(x_34, x_36);
x_38 = l_Lean_MessageData_ofList(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
x_3 = l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(x_1, x_2);
x_4 = l_Lean_Meta_Match_Pattern_toMessageData___closed__11;
x_5 = l_Lean_MessageData_joinSep(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_Problem_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedProblem_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedMVarId_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedProblem_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_instInhabitedProblem_default___closed__0;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedProblem_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedProblem_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedProblem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_instInhabitedProblem_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_withGoalOf___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_withGoalOf___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_withGoalOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
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
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = l_Lean_Meta_Match_Alt_toMessageData(x_11, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_21 = l_Lean_Meta_Match_Alt_toMessageData(x_19, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_1 = x_20;
x_2 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
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
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_11);
x_13 = lean_infer_type(x_11, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_MessageData_ofExpr(x_11);
x_16 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofExpr(x_14);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_21);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
uint8_t x_23; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_26);
x_28 = lean_infer_type(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_MessageData_ofExpr(x_26);
x_31 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_ofExpr(x_29);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
x_1 = x_27;
x_2 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_40 = x_28;
} else {
 lean_dec_ref(x_28);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("remaining variables: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nalternatives:", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nexamples:", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_2);
x_10 = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(x_1, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_2);
x_12 = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(x_3, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1;
x_16 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(x_14, x_2);
x_17 = l_Lean_MessageData_ofList(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4;
x_22 = l_Lean_MessageData_joinSep(x_11, x_21);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_Match_examplesToMessageData(x_4);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__8;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1;
x_33 = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(x_31, x_2);
x_34 = l_Lean_MessageData_ofList(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4;
x_39 = l_Lean_MessageData_joinSep(x_11, x_38);
x_40 = l_Lean_indentD(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_Match_examplesToMessageData(x_4);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__8;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
return x_12;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_12, 0);
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_10);
if (x_52 == 0)
{
return x_10;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_10, 0);
lean_inc(x_53);
lean_dec(x_10);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_box(0);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed), 9, 4);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_9);
x_12 = l_Lean_Meta_Match_withGoalOf___redArg(x_1, x_11, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Match_Problem_toMessageData___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Match_Problem_toMessageData(x_1, x_2, x_3, x_4, x_5);
return x_7;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
x_3 = l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(x_1, x_2);
x_4 = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4;
x_5 = l_Lean_MessageData_joinSep(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherResult_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Match_MatcherResult_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_12 = l_Lean_Meta_Match_toPattern(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
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
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = l_Lean_Meta_Match_toPattern(x_11, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_21 = l_Lean_Meta_Match_toPattern(x_19, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_1 = x_20;
x_2 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected pattern", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_toPattern___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected occurrence of auxiliary declaration 'namedPattern'", 61, 61);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_toPattern___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_17; 
x_17 = l_Lean_inaccessible_x3f(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Expr_arrayLit_x3f(x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Match_isNamedPattern_x3f(x_1);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Expr_getAppNumArgs(x_20);
x_23 = lean_nat_sub(x_22, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = l_Lean_Expr_getRevArg_x21(x_20, x_25);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_27 = l_Lean_Meta_Match_toPattern(x_26, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_27, 0);
x_37 = lean_nat_sub(x_22, x_24);
x_38 = lean_nat_sub(x_37, x_24);
lean_dec(x_37);
x_39 = l_Lean_Expr_getRevArg_x21(x_20, x_38);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_sub(x_22, x_41);
lean_dec(x_22);
x_43 = lean_nat_sub(x_42, x_24);
lean_dec(x_42);
x_44 = l_Lean_Expr_getRevArg_x21(x_20, x_43);
lean_dec(x_20);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_29);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_27, 0, x_46);
return x_27;
}
else
{
lean_dec_ref(x_44);
lean_dec(x_40);
lean_free_object(x_27);
lean_dec(x_29);
x_30 = x_2;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
goto block_36;
}
}
else
{
lean_dec_ref(x_39);
lean_free_object(x_27);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_20);
x_30 = x_2;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
goto block_36;
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Meta_Match_toPattern___closed__3;
x_35 = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(x_34, x_30, x_31, x_32, x_33);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
return x_35;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_27, 0);
lean_inc(x_47);
lean_dec(x_27);
x_55 = lean_nat_sub(x_22, x_24);
x_56 = lean_nat_sub(x_55, x_24);
lean_dec(x_55);
x_57 = l_Lean_Expr_getRevArg_x21(x_20, x_56);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_sub(x_22, x_59);
lean_dec(x_22);
x_61 = lean_nat_sub(x_60, x_24);
lean_dec(x_60);
x_62 = l_Lean_Expr_getRevArg_x21(x_20, x_61);
lean_dec(x_20);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_47);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_dec_ref(x_62);
lean_dec(x_58);
lean_dec(x_47);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
goto block_54;
}
}
else
{
lean_dec_ref(x_57);
lean_dec(x_47);
lean_dec(x_22);
lean_dec(x_20);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
goto block_54;
}
block_54:
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_Meta_Match_toPattern___closed__3;
x_53 = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(x_52, x_48, x_49, x_50, x_51);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
return x_53;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_27;
}
}
else
{
lean_object* x_66; 
lean_dec(x_19);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_66 = l_Lean_Meta_isMatchValue(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isFVar(x_1);
if (x_70 == 0)
{
lean_object* x_71; 
lean_free_object(x_66);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_71 = lean_whnf(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = lean_expr_eqv(x_72, x_1);
if (x_73 == 0)
{
lean_dec_ref(x_1);
x_1 = x_72;
goto _start;
}
else
{
if (x_70 == 0)
{
lean_object* x_75; 
lean_dec(x_72);
x_75 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_75) == 4)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_st_ref_get(x_5);
x_79 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_79);
lean_dec_ref(x_78);
x_80 = l_Lean_Environment_find_x3f(x_79, x_76, x_70);
if (lean_obj_tag(x_80) == 0)
{
lean_dec(x_77);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
if (lean_obj_tag(x_81) == 6)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_82, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 4);
lean_inc(x_85);
lean_dec_ref(x_82);
x_86 = l_Lean_Meta_Match_toPattern___closed__4;
x_87 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_87);
x_88 = lean_mk_array(x_87, x_86);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_87, x_89);
lean_dec(x_87);
lean_inc_ref(x_1);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_88, x_90);
x_122 = lean_array_get_size(x_91);
x_123 = lean_nat_add(x_84, x_85);
lean_dec(x_85);
x_124 = lean_nat_dec_eq(x_122, x_123);
lean_dec(x_123);
lean_dec(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec_ref(x_91);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_77);
x_125 = l_Lean_Meta_Match_toPattern___closed__1;
x_126 = l_Lean_indentExpr(x_1);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(x_127, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
return x_128;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
else
{
lean_dec_ref(x_1);
x_92 = x_2;
x_93 = x_3;
x_94 = x_4;
x_95 = x_5;
x_96 = lean_box(0);
goto block_121;
}
block_121:
{
lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; 
x_97 = lean_array_get_size(x_91);
lean_inc(x_84);
x_98 = l_Array_extract___redArg(x_91, x_84, x_97);
x_99 = lean_array_size(x_98);
x_100 = 0;
x_101 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(x_99, x_100, x_98, x_92, x_93, x_94, x_95);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_83, 0);
lean_inc(x_104);
lean_dec_ref(x_83);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_Array_extract___redArg(x_91, x_105, x_84);
lean_dec_ref(x_91);
x_107 = lean_array_to_list(x_106);
x_108 = lean_array_to_list(x_103);
x_109 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_77);
lean_ctor_set(x_109, 2, x_107);
lean_ctor_set(x_109, 3, x_108);
lean_ctor_set(x_101, 0, x_109);
return x_101;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_101, 0);
lean_inc(x_110);
lean_dec(x_101);
x_111 = lean_ctor_get(x_83, 0);
lean_inc(x_111);
lean_dec_ref(x_83);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Array_extract___redArg(x_91, x_112, x_84);
lean_dec_ref(x_91);
x_114 = lean_array_to_list(x_113);
x_115 = lean_array_to_list(x_110);
x_116 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_77);
lean_ctor_set(x_116, 2, x_114);
lean_ctor_set(x_116, 3, x_115);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_dec_ref(x_91);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_77);
x_118 = !lean_is_exclusive(x_101);
if (x_118 == 0)
{
return x_101;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_101, 0);
lean_inc(x_119);
lean_dec(x_101);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
else
{
lean_dec(x_81);
lean_dec(x_77);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_dec_ref(x_75);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec_ref(x_1);
x_1 = x_72;
goto _start;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_71);
if (x_133 == 0)
{
return x_71;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_71, 0);
lean_inc(x_134);
lean_dec(x_71);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_136 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec_ref(x_1);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_66, 0, x_137);
return x_66;
}
}
else
{
lean_object* x_138; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_1);
lean_ctor_set(x_66, 0, x_138);
return x_66;
}
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_66, 0);
lean_inc(x_139);
lean_dec(x_66);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Expr_isFVar(x_1);
if (x_141 == 0)
{
lean_object* x_142; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_142 = lean_whnf(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_expr_eqv(x_143, x_1);
if (x_144 == 0)
{
lean_dec_ref(x_1);
x_1 = x_143;
goto _start;
}
else
{
if (x_141 == 0)
{
lean_object* x_146; 
lean_dec(x_143);
x_146 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_146) == 4)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = lean_st_ref_get(x_5);
x_150 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_150);
lean_dec_ref(x_149);
x_151 = l_Lean_Environment_find_x3f(x_150, x_147, x_141);
if (lean_obj_tag(x_151) == 0)
{
lean_dec(x_148);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
if (lean_obj_tag(x_152) == 6)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc_ref(x_153);
lean_dec_ref(x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_153, 3);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 4);
lean_inc(x_156);
lean_dec_ref(x_153);
x_157 = l_Lean_Meta_Match_toPattern___closed__4;
x_158 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_158);
x_159 = lean_mk_array(x_158, x_157);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_sub(x_158, x_160);
lean_dec(x_158);
lean_inc_ref(x_1);
x_162 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_159, x_161);
x_186 = lean_array_get_size(x_162);
x_187 = lean_nat_add(x_155, x_156);
lean_dec(x_156);
x_188 = lean_nat_dec_eq(x_186, x_187);
lean_dec(x_187);
lean_dec(x_186);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec_ref(x_162);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_148);
x_189 = l_Lean_Meta_Match_toPattern___closed__1;
x_190 = l_Lean_indentExpr(x_1);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(x_191, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
return x_195;
}
else
{
lean_dec_ref(x_1);
x_163 = x_2;
x_164 = x_3;
x_165 = x_4;
x_166 = x_5;
x_167 = lean_box(0);
goto block_185;
}
block_185:
{
lean_object* x_168; lean_object* x_169; size_t x_170; size_t x_171; lean_object* x_172; 
x_168 = lean_array_get_size(x_162);
lean_inc(x_155);
x_169 = l_Array_extract___redArg(x_162, x_155, x_168);
x_170 = lean_array_size(x_169);
x_171 = 0;
x_172 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(x_170, x_171, x_169, x_163, x_164, x_165, x_166);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_154, 0);
lean_inc(x_175);
lean_dec_ref(x_154);
x_176 = lean_unsigned_to_nat(0u);
x_177 = l_Array_extract___redArg(x_162, x_176, x_155);
lean_dec_ref(x_162);
x_178 = lean_array_to_list(x_177);
x_179 = lean_array_to_list(x_173);
x_180 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_148);
lean_ctor_set(x_180, 2, x_178);
lean_ctor_set(x_180, 3, x_179);
if (lean_is_scalar(x_174)) {
 x_181 = lean_alloc_ctor(0, 1, 0);
} else {
 x_181 = x_174;
}
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec_ref(x_162);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_148);
x_182 = lean_ctor_get(x_172, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_183 = x_172;
} else {
 lean_dec_ref(x_172);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
}
else
{
lean_dec(x_152);
lean_dec(x_148);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_dec_ref(x_146);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec_ref(x_1);
x_1 = x_143;
goto _start;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_142, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_198 = x_142;
} else {
 lean_dec_ref(x_142);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 1, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_200 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec_ref(x_1);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_203 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_203, 0, x_1);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_205 = !lean_is_exclusive(x_66);
if (x_205 == 0)
{
return x_66;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_66, 0);
lean_inc(x_206);
lean_dec(x_66);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
}
}
else
{
lean_object* x_208; uint8_t x_209; 
lean_dec_ref(x_1);
x_208 = lean_ctor_get(x_18, 0);
lean_inc(x_208);
lean_dec_ref(x_18);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_208, 0);
x_211 = lean_ctor_get(x_208, 1);
x_212 = lean_box(0);
x_213 = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(x_211, x_212, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_213, 0);
lean_ctor_set_tag(x_208, 4);
lean_ctor_set(x_208, 1, x_215);
lean_ctor_set(x_213, 0, x_208);
return x_213;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_213, 0);
lean_inc(x_216);
lean_dec(x_213);
lean_ctor_set_tag(x_208, 4);
lean_ctor_set(x_208, 1, x_216);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_208);
return x_217;
}
}
else
{
uint8_t x_218; 
lean_free_object(x_208);
lean_dec(x_210);
x_218 = !lean_is_exclusive(x_213);
if (x_218 == 0)
{
return x_213;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_213, 0);
lean_inc(x_219);
lean_dec(x_213);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_208, 0);
x_222 = lean_ctor_get(x_208, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_208);
x_223 = lean_box(0);
x_224 = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(x_222, x_223, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_227, 0, x_221);
lean_ctor_set(x_227, 1, x_225);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 1, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_221);
x_229 = lean_ctor_get(x_224, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_230 = x_224;
} else {
 lean_dec_ref(x_224);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_229);
return x_231;
}
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_232 = !lean_is_exclusive(x_17);
if (x_232 == 0)
{
lean_object* x_233; 
lean_ctor_set_tag(x_17, 0);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_17);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_17, 0);
lean_inc(x_234);
lean_dec(x_17);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Meta_Match_toPattern___closed__1;
x_13 = l_Lean_indentExpr(x_1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(x_14, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Match_toPattern(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr_eq", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_congrEqnThmSuffixBase() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr_eq_", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr_eq_1", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_congrEqn1ThmSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_dec(x_5);
return x_10;
}
else
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_3, x_5);
x_12 = 48;
x_13 = lean_uint32_dec_le(x_12, x_11);
if (x_13 == 0)
{
if (x_13 == 0)
{
x_6 = x_1;
goto block_9;
}
else
{
x_6 = x_2;
goto block_9;
}
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 57;
x_15 = lean_uint32_dec_le(x_11, x_14);
if (x_15 == 0)
{
x_6 = x_1;
goto block_9;
}
else
{
x_6 = x_2;
goto block_9;
}
}
}
block_9:
{
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_3, x_5);
lean_dec(x_5);
x_5 = x_7;
goto _start;
}
else
{
lean_dec(x_5);
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0;
x_3 = l_String_isPrefixOf(x_2, x_1);
if (x_3 == 0)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(9u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_nextn(x_7, x_4, x_5);
lean_dec_ref(x_7);
x_9 = lean_string_utf8_extract(x_1, x_8, x_6);
lean_dec(x_6);
lean_dec(x_8);
lean_dec_ref(x_1);
x_10 = lean_string_utf8_byte_size(x_9);
x_11 = lean_nat_dec_eq(x_10, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_String_anyAux___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(x_3, x_11, x_9, x_10, x_5);
lean_dec(x_10);
lean_dec_ref(x_9);
if (x_12 == 0)
{
return x_3;
}
else
{
return x_11;
}
}
else
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = 0;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l_String_anyAux___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseArraySizes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Match_mkNamedPattern___closed__0 = _init_l_Lean_Meta_Match_mkNamedPattern___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_mkNamedPattern___closed__0);
l_Lean_Meta_Match_mkNamedPattern___closed__1 = _init_l_Lean_Meta_Match_mkNamedPattern___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkNamedPattern___closed__1);
l_Lean_Meta_Match_mkNamedPattern___closed__2 = _init_l_Lean_Meta_Match_mkNamedPattern___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkNamedPattern___closed__2);
l_Lean_Meta_Match_instInhabitedPattern_default___closed__0 = _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern_default___closed__0);
l_Lean_Meta_Match_instInhabitedPattern_default___closed__1 = _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern_default___closed__1);
l_Lean_Meta_Match_instInhabitedPattern_default___closed__2 = _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2);
l_Lean_Meta_Match_instInhabitedPattern_default___closed__3 = _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern_default___closed__3);
l_Lean_Meta_Match_instInhabitedPattern_default = _init_l_Lean_Meta_Match_instInhabitedPattern_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern_default);
l_Lean_Meta_Match_instInhabitedPattern = _init_l_Lean_Meta_Match_instInhabitedPattern();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern);
l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0 = _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0();
lean_mark_persistent(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0);
l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1 = _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1();
lean_mark_persistent(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1);
l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2 = _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2();
lean_mark_persistent(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2);
l_Lean_Meta_Match_Pattern_toMessageData___closed__0 = _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_Pattern_toMessageData___closed__0);
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
l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0 = _init_l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0);
l_Lean_Meta_Match_instInhabitedAltLHS_default = _init_l_Lean_Meta_Match_instInhabitedAltLHS_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAltLHS_default);
l_Lean_Meta_Match_instInhabitedAltLHS = _init_l_Lean_Meta_Match_instInhabitedAltLHS();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAltLHS);
l_Lean_Meta_Match_instInhabitedAlt_default___closed__0 = _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt_default___closed__0);
l_Lean_Meta_Match_instInhabitedAlt_default = _init_l_Lean_Meta_Match_instInhabitedAlt_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt_default);
l_Lean_Meta_Match_instInhabitedAlt = _init_l_Lean_Meta_Match_instInhabitedAlt();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt);
l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__0 = _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__0();
lean_mark_persistent(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__0);
l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1 = _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0___closed__1);
l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__0);
l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__1);
l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__2);
l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___redArg___closed__3);
l_Lean_Meta_Match_Alt_toMessageData___closed__0 = _init_l_Lean_Meta_Match_Alt_toMessageData___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_Alt_toMessageData___closed__0);
l_Lean_Meta_Match_Alt_toMessageData___closed__1 = _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Alt_toMessageData___closed__1);
l_Lean_Meta_Match_Alt_toMessageData___closed__2 = _init_l_Lean_Meta_Match_Alt_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Alt_toMessageData___closed__2);
l_Lean_Meta_Match_Alt_toMessageData___closed__3 = _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_Alt_toMessageData___closed__3);
l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0 = _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0();
lean_mark_persistent(l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0);
l_Lean_Meta_Match_Example_toMessageData___closed__0 = _init_l_Lean_Meta_Match_Example_toMessageData___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_Example_toMessageData___closed__0);
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
l_Lean_Meta_Match_instInhabitedProblem_default___closed__0 = _init_l_Lean_Meta_Match_instInhabitedProblem_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedProblem_default___closed__0);
l_Lean_Meta_Match_instInhabitedProblem_default___closed__1 = _init_l_Lean_Meta_Match_instInhabitedProblem_default___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedProblem_default___closed__1);
l_Lean_Meta_Match_instInhabitedProblem_default = _init_l_Lean_Meta_Match_instInhabitedProblem_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedProblem_default);
l_Lean_Meta_Match_instInhabitedProblem = _init_l_Lean_Meta_Match_instInhabitedProblem();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedProblem);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__7 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__7);
l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__8 = _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__8();
lean_mark_persistent(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__8);
l_Lean_Meta_Match_toPattern___closed__0 = _init_l_Lean_Meta_Match_toPattern___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__0);
l_Lean_Meta_Match_toPattern___closed__1 = _init_l_Lean_Meta_Match_toPattern___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__1);
l_Lean_Meta_Match_toPattern___closed__2 = _init_l_Lean_Meta_Match_toPattern___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__2);
l_Lean_Meta_Match_toPattern___closed__3 = _init_l_Lean_Meta_Match_toPattern___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__3);
l_Lean_Meta_Match_toPattern___closed__4 = _init_l_Lean_Meta_Match_toPattern___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_toPattern___closed__4);
l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0 = _init_l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0);
l_Lean_Meta_Match_congrEqnThmSuffixBase = _init_l_Lean_Meta_Match_congrEqnThmSuffixBase();
lean_mark_persistent(l_Lean_Meta_Match_congrEqnThmSuffixBase);
l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0 = _init_l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0);
l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix = _init_l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix();
lean_mark_persistent(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix);
l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0 = _init_l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0();
lean_mark_persistent(l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0);
l_Lean_Meta_Match_congrEqn1ThmSuffix = _init_l_Lean_Meta_Match_congrEqn1ThmSuffix();
lean_mark_persistent(l_Lean_Meta_Match_congrEqn1ThmSuffix);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
