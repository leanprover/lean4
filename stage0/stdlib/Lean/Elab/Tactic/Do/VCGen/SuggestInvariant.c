// Lean compiler output
// Module: Lean.Elab.Tactic.Do.VCGen.SuggestInvariant
// Imports: public import Lean.Elab.Tactic.Basic public import Lean.Meta.Tactic.Simp.Types import Lean.Meta.Tactic.Simp.Main import Lean.Elab.Tactic.Do.ProofMode.MGoal import Std.Tactic.Do import Init.Data.Array.Mem
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_eraseQuoteMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ULift"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "down"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 162, 24, 1, 186, 170, 9, 57)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__1_value),LEAN_SCALAR_PTR_LITERAL(8, 0, 133, 161, 22, 18, 91, 229)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_toAssertion(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "MGoalEntails"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 32, 213, 253, 69, 208, 115, 14)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(203, 9, 83, 52, 40, 85, 31, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(86, 181, 97, 38, 147, 213, 38, 7)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_success_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_notAnInvariantUse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_notAnInvariantUse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_unknownInvariantUse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_unknownInvariantUse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "snd"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 40, 163, 84, 60, 49, 151, 224)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Cursor"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(171, 26, 51, 126, 183, 221, 138, 175)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 108, 132, 55, 147, 41, 48, 106)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 145, 1, 190, 19, 10, 144, 159)}};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 97, 27, 109, 96, 85, 230, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 97, 84, 180, 109, 220, 63, 60)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ExceptConds"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(72, 205, 41, 157, 129, 142, 231, 99)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(146, 91, 82, 196, 249, 72, 203, 194)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 33, 255, 249, 3, 79, 124, 43)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(240, 66, 120, 132, 230, 141, 174, 69)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(226, 139, 39, 26, 105, 135, 247, 193)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "prefix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(230, 205, 224, 142, 140, 162, 83, 182)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__12_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 183, 133, 62, 214, 202, 136, 98)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "termPost⟨_,,⟩"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 45, 176, 130, 225, 239, 187, 245)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "post⟨"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__16_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__20_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ExceptConds.false"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 147, 12, 12, 50, 62, 178, 236)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(80, 174, 198, 53, 67, 44, 24, 11)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ExceptConds.true"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 147, 12, 12, 50, 62, 178, 236)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(251, 220, 146, 174, 153, 82, 100, 162)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letMuts"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 50, 229, 239, 254, 134, 162, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCtorEq"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 230, 128, 19, 70, 224, 61, 3)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "term_⇓\?_=>_"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⇓\?"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 10, .m_data = "term_⇓_=>_"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⇓"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Invariant.withEarlyReturnNewDo"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "withEarlyReturnNewDo"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__5_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "onReturn"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 190, 22, 214, 80, 62, 154)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "onContinue"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15_value),LEAN_SCALAR_PTR_LITERAL(244, 55, 172, 124, 26, 216, 105, 59)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "onExcept"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18_value),LEAN_SCALAR_PTR_LITERAL(203, 51, 246, 190, 226, 223, 149, 102)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__21_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mleave"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 47, 148, 137, 18, 118, 104, 201)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Expected invariant type, got "};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Invariant"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 189, 77, 192, 11, 129, 81, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "xs"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5_value),LEAN_SCALAR_PTR_LITERAL(152, 88, 60, 86, 131, 35, 117, 108)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(171, 26, 51, 126, 183, 221, 138, 175)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel(lean_object* v_expr_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__2));
v___x_8_ = lean_unsigned_to_nat(2u);
v___x_9_ = l_Lean_Expr_isAppOfArity(v_expr_6_, v___x_7_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_11_ = lean_box(0);
v___x_12_ = l_Lean_Expr_getAppFn(v_expr_6_);
v___x_13_ = l_Lean_Expr_constLevels_x21(v___x_12_);
lean_dec_ref(v___x_12_);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = l_List_get_x21Internal___redArg(v___x_11_, v___x_13_, v___x_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___boxed(lean_object* v_expr_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel(v_expr_17_);
lean_dec_ref(v_expr_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_toAssertion(lean_object* v_lvl_19_, lean_object* v_prop_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_21_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel___closed__2));
v___x_22_ = lean_unsigned_to_nat(2u);
v___x_23_ = l_Lean_Expr_isAppOfArity(v_prop_20_, v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_inc(v_lvl_19_);
v___x_24_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_19_);
v___x_25_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_lvl_19_, v___x_24_, v_prop_20_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_lvl_19_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = l_Lean_Expr_getAppNumArgs(v_prop_20_);
v___x_28_ = lean_nat_sub(v___x_27_, v___x_26_);
lean_dec(v___x_27_);
v___x_29_ = lean_nat_sub(v___x_28_, v___x_26_);
lean_dec(v___x_28_);
v___x_30_ = l_Lean_Expr_getRevArg_x21(v_prop_20_, v___x_29_);
lean_dec_ref(v_prop_20_);
return v___x_30_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v_dummy_32_; 
v___x_31_ = lean_box(0);
v_dummy_32_ = l_Lean_Expr_sort___override(v___x_31_);
return v_dummy_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(lean_object* v_type_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___x_74_; lean_object* v_dummy_75_; lean_object* v_nargs_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v_a_80_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_74_ = lean_box(0);
v_dummy_75_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0);
v_nargs_76_ = l_Lean_Expr_getAppNumArgs(v_type_49_);
lean_inc(v_nargs_76_);
v___x_77_ = lean_mk_array(v_nargs_76_, v_dummy_75_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_sub(v_nargs_76_, v___x_78_);
lean_inc(v___x_79_);
lean_inc_ref(v_type_49_);
v_a_80_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_49_, v___x_77_, v___x_79_);
v___x_103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5));
v___x_104_ = l_Lean_Expr_isAppOf(v_type_49_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8));
v___x_106_ = l_Lean_Expr_isAppOf(v_type_49_, v___x_105_);
if (v___x_106_ == 0)
{
lean_dec_ref(v_a_80_);
lean_dec(v___x_79_);
lean_dec(v_nargs_76_);
goto v___jp_61_;
}
else
{
goto v___jp_81_;
}
}
else
{
goto v___jp_81_;
}
v___jp_52_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
lean_inc_n(v___y_54_, 2);
v___x_55_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_toAssertion(v___y_54_, v___y_53_);
v___x_56_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_toAssertion(v___y_54_, v_type_49_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___y_54_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
v___jp_61_:
{
lean_object* v_lctx_62_; lean_object* v___x_63_; 
v_lctx_62_ = lean_ctor_get(v_a_50_, 2);
v___x_63_ = l_Lean_LocalContext_lastDecl(v_lctx_62_);
if (lean_obj_tag(v___x_63_) == 1)
{
lean_object* v_val_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_val_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v___x_63_, 1);
v___x_65_ = l_Lean_LocalDecl_type(v_val_64_);
lean_dec(v_val_64_);
v___x_66_ = l_Lean_Expr_consumeMData(v___x_65_);
lean_dec_ref(v___x_65_);
v___x_67_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel(v_type_49_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v___x_68_; 
v___x_68_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel(v___x_66_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
v___y_53_ = v___x_66_;
v___y_54_ = v___x_69_;
goto v___jp_52_;
}
else
{
lean_object* v_val_70_; 
v_val_70_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_val_70_);
lean_dec_ref_known(v___x_68_, 1);
v___y_53_ = v___x_66_;
v___y_54_ = v_val_70_;
goto v___jp_52_;
}
}
else
{
lean_object* v_val_71_; 
v_val_71_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_val_71_);
lean_dec_ref_known(v___x_67_, 1);
v___y_53_ = v___x_66_;
v___y_54_ = v_val_71_;
goto v___jp_52_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v___x_63_);
lean_dec_ref(v_type_49_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
v___jp_81_:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = lean_array_get_size(v_a_80_);
v___x_84_ = lean_nat_dec_lt(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_dec_ref(v_a_80_);
lean_dec(v___x_79_);
lean_dec(v_nargs_76_);
goto v___jp_61_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_85_ = l_Lean_Expr_getAppFn(v_type_49_);
v___x_86_ = l_Lean_Expr_constLevels_x21(v___x_85_);
lean_dec_ref(v___x_85_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = l_List_get_x21Internal___redArg(v___x_74_, v___x_86_, v___x_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_nat_sub(v___x_79_, v___x_78_);
lean_dec(v___x_79_);
v___x_90_ = l_Lean_Expr_getRevArg_x21(v_type_49_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(3u);
v___x_92_ = l_Array_toSubarray___redArg(v_a_80_, v___x_91_, v___x_83_);
v___x_93_ = l_Subarray_copy___redArg(v___x_92_);
lean_inc_ref(v___x_93_);
v___x_94_ = l_Lean_Expr_beta(v___x_90_, v___x_93_);
v___x_95_ = lean_nat_sub(v_nargs_76_, v___x_82_);
lean_dec(v_nargs_76_);
v___x_96_ = lean_nat_sub(v___x_95_, v___x_78_);
lean_dec(v___x_95_);
v___x_97_ = l_Lean_Expr_getRevArg_x21(v_type_49_, v___x_96_);
lean_dec_ref(v_type_49_);
v___x_98_ = l_Lean_Expr_beta(v___x_97_, v___x_93_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_94_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_88_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___boxed(lean_object* v_type_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(v_type_107_, v_a_108_);
lean_dec_ref(v_a_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget(lean_object* v_type_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(v_type_111_, v_a_112_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed(lean_object* v_type_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget(v_type_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl(lean_object* v_x_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_tag_nat(v_x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl___boxed(lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___impl(v_x_127_);
lean_dec(v_x_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(lean_object* v_t_129_, lean_object* v_k_130_){
_start:
{
if (lean_obj_tag(v_t_129_) == 0)
{
lean_object* v_invariantUse_131_; lean_object* v___x_132_; 
v_invariantUse_131_ = lean_ctor_get(v_t_129_, 0);
lean_inc_ref(v_invariantUse_131_);
lean_dec_ref_known(v_t_129_, 1);
v___x_132_ = lean_apply_1(v_k_130_, v_invariantUse_131_);
return v___x_132_;
}
else
{
lean_dec(v_t_129_);
return v_k_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim(lean_object* v_motive_133_, lean_object* v_ctorIdx_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_k_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_135_, v_k_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___boxed(lean_object* v_motive_139_, lean_object* v_ctorIdx_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_k_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim(v_motive_139_, v_ctorIdx_140_, v_t_141_, v_h_142_, v_k_143_);
lean_dec(v_ctorIdx_140_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_success_elim___redArg(lean_object* v_t_145_, lean_object* v_success_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_145_, v_success_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_success_elim(lean_object* v_motive_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_success_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_149_, v_success_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_notAnInvariantUse_elim___redArg(lean_object* v_t_153_, lean_object* v_notAnInvariantUse_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_153_, v_notAnInvariantUse_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_notAnInvariantUse_elim(lean_object* v_motive_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_notAnInvariantUse_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_157_, v_notAnInvariantUse_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_unknownInvariantUse_elim___redArg(lean_object* v_t_161_, lean_object* v_unknownInvariantUse_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_161_, v_unknownInvariantUse_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_unknownInvariantUse_elim(lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_unknownInvariantUse_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_165_, v_unknownInvariantUse_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(lean_object* v_a_174_){
_start:
{
lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_201_; 
v_fst_175_ = lean_ctor_get(v_a_174_, 0);
v_snd_176_ = lean_ctor_get(v_a_174_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_a_174_);
if (v_isSharedCheck_201_ == 0)
{
v___x_178_ = v_a_174_;
v_isShared_179_ = v_isSharedCheck_201_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snd_176_);
lean_inc(v_fst_175_);
lean_dec(v_a_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_201_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_180_ = lean_unsigned_to_nat(4u);
v___x_181_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_182_ = l_Lean_Expr_isAppOfArity(v_fst_175_, v___x_181_, v___x_180_);
if (v___x_182_ == 0)
{
lean_object* v___x_184_; 
if (v_isShared_179_ == 0)
{
v___x_184_ = v___x_178_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_fst_175_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_snd_176_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_186_ = lean_unsigned_to_nat(2u);
v___x_187_ = lean_unsigned_to_nat(3u);
v___x_188_ = l_Lean_Expr_getAppNumArgs(v_fst_175_);
v___x_189_ = lean_nat_sub(v___x_188_, v___x_186_);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_sub(v___x_189_, v___x_190_);
lean_dec(v___x_189_);
v___x_192_ = l_Lean_Expr_getRevArg_x21(v_fst_175_, v___x_191_);
v___x_193_ = lean_array_push(v_snd_176_, v___x_192_);
v___x_194_ = lean_nat_sub(v___x_188_, v___x_187_);
lean_dec(v___x_188_);
v___x_195_ = lean_nat_sub(v___x_194_, v___x_190_);
lean_dec(v___x_194_);
v___x_196_ = l_Lean_Expr_getRevArg_x21(v_fst_175_, v___x_195_);
lean_dec(v_fst_175_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_193_);
lean_ctor_set(v___x_178_, 0, v___x_196_);
v___x_198_ = v___x_178_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_193_);
v___x_198_ = v_reuseFailAlloc_200_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
v_a_174_ = v___x_198_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(lean_object* v_inv_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_snd_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_249_; 
v_snd_210_ = lean_ctor_get(v_a_209_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_a_209_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v_a_209_, 0);
lean_dec(v_unused_250_);
v___x_212_ = v_a_209_;
v_isShared_213_ = v_isSharedCheck_249_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_snd_210_);
lean_dec(v_a_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_249_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_248_; 
v_fst_214_ = lean_ctor_get(v_snd_210_, 0);
v_snd_215_ = lean_ctor_get(v_snd_210_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_snd_210_);
if (v_isSharedCheck_248_ == 0)
{
v___x_217_ = v_snd_210_;
v_isShared_218_ = v_isSharedCheck_248_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_inc(v_fst_214_);
lean_dec(v_snd_210_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_248_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = lean_box(0);
lean_inc(v_inv_208_);
v___x_220_ = l_Lean_mkMVar(v_inv_208_);
v___x_221_ = lean_expr_eqv(v_fst_214_, v___x_220_);
lean_dec_ref(v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_222_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_223_ = lean_unsigned_to_nat(4u);
v___x_224_ = l_Lean_Expr_isAppOfArity(v_fst_214_, v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_227_; 
lean_dec(v_inv_208_);
v___x_225_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__2));
if (v_isShared_218_ == 0)
{
v___x_227_ = v___x_217_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_fst_214_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_snd_215_);
v___x_227_ = v_reuseFailAlloc_231_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_227_);
lean_ctor_set(v___x_212_, 0, v___x_225_);
v___x_229_ = v___x_212_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_snd_215_, v___x_232_);
lean_dec(v_snd_215_);
v___x_234_ = l_Lean_Expr_getRevArg_x21(v_fst_214_, v___x_232_);
lean_dec(v_fst_214_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_233_);
lean_ctor_set(v___x_217_, 0, v___x_234_);
v___x_236_ = v___x_217_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_233_);
v___x_236_ = v_reuseFailAlloc_241_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_236_);
lean_ctor_set(v___x_212_, 0, v___x_219_);
v___x_238_ = v___x_212_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
v_a_209_ = v___x_238_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_243_; 
lean_dec(v_inv_208_);
if (v_isShared_218_ == 0)
{
v___x_243_ = v___x_217_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_fst_214_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_snd_215_);
v___x_243_ = v_reuseFailAlloc_247_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_245_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_243_);
lean_ctor_set(v___x_212_, 0, v___x_219_);
v___x_245_ = v___x_212_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(lean_object* v_assertion_263_, lean_object* v_inv_264_){
_start:
{
lean_object* v_assertion_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_assertion_265_ = l_Lean_Expr_consumeMData(v_assertion_263_);
v___x_266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1));
v___x_267_ = l_Lean_Expr_isAppOf(v_assertion_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec_ref(v_assertion_265_);
lean_dec(v_inv_264_);
v___x_268_ = lean_box(1);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_head_274_; lean_object* v_conditionIdx_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_fst_280_; 
v___x_269_ = lean_unsigned_to_nat(2u);
v___x_270_ = l_Lean_Expr_getAppNumArgs(v_assertion_265_);
v___x_271_ = lean_nat_sub(v___x_270_, v___x_269_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_sub(v___x_271_, v___x_272_);
lean_dec(v___x_271_);
v_head_274_ = l_Lean_Expr_getRevArg_x21(v_assertion_265_, v___x_273_);
v_conditionIdx_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_head_274_);
lean_ctor_set(v___x_277_, 1, v_conditionIdx_275_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(v_inv_264_, v___x_278_);
v_fst_280_ = lean_ctor_get(v___x_279_, 0);
if (lean_obj_tag(v_fst_280_) == 0)
{
lean_object* v_snd_281_; lean_object* v_dummy_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_snd_281_ = lean_ctor_get(v___x_279_, 1);
lean_inc(v_snd_281_);
lean_dec_ref(v___x_279_);
v_dummy_282_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0);
lean_inc(v___x_270_);
v___x_283_ = lean_mk_array(v___x_270_, v_dummy_282_);
v___x_284_ = lean_nat_sub(v___x_270_, v___x_272_);
lean_dec(v___x_270_);
v___x_285_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_assertion_265_, v___x_283_, v___x_284_);
v___x_286_ = lean_array_get_size(v___x_285_);
v___x_287_ = lean_unsigned_to_nat(4u);
v___x_288_ = lean_nat_dec_lt(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_289_ = l_Lean_instInhabitedExpr;
v___x_290_ = lean_unsigned_to_nat(3u);
v___x_291_ = lean_array_get_borrowed(v___x_289_, v___x_285_, v___x_290_);
v___x_292_ = l_Lean_Expr_cleanupAnnotations(v___x_291_);
v___x_293_ = l_Lean_Expr_isApp(v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_294_ = lean_box(2);
return v___x_294_;
}
else
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_292_);
v___x_296_ = l_Lean_Expr_isApp(v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref(v___x_295_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_297_ = lean_box(2);
return v___x_297_;
}
else
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
v___x_299_ = l_Lean_Expr_isApp(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v___x_298_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_300_ = lean_box(2);
return v___x_300_;
}
else
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_298_);
lean_dec_ref(v___x_298_);
v___x_302_ = l_Lean_Expr_isApp(v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_301_);
lean_dec_ref(v___x_295_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_303_ = lean_box(2);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_301_);
lean_dec_ref(v___x_301_);
v___x_305_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_306_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_305_);
lean_dec_ref(v___x_304_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_dec_ref(v___x_295_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_307_ = lean_box(2);
return v___x_307_;
}
else
{
lean_object* v_arg_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_arg_308_ = lean_ctor_get(v___x_295_, 1);
lean_inc_ref(v_arg_308_);
lean_dec_ref(v___x_295_);
v___x_309_ = l_Lean_Expr_cleanupAnnotations(v_arg_308_);
lean_dec_ref(v_arg_308_);
v___x_310_ = l_Lean_Expr_isApp(v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec_ref(v___x_309_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_311_ = lean_box(2);
return v___x_311_;
}
else
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_309_);
lean_dec_ref(v___x_309_);
v___x_313_ = l_Lean_Expr_isApp(v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_314_ = lean_box(2);
return v___x_314_;
}
else
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = l_Lean_Expr_appFnCleanup___redArg(v___x_312_);
v___x_316_ = l_Lean_Expr_isApp(v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec_ref(v___x_315_);
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_317_ = lean_box(2);
return v___x_317_;
}
else
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_315_);
v___x_319_ = l_Lean_Expr_isApp(v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec_ref(v___x_318_);
lean_dec_ref(v___x_315_);
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_320_ = lean_box(2);
return v___x_320_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_318_);
lean_dec_ref(v___x_318_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v___x_321_);
lean_dec_ref(v___x_315_);
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_323_ = lean_box(2);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
lean_dec_ref(v___x_321_);
v___x_325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4));
v___x_326_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_325_);
lean_dec_ref(v___x_324_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_dec_ref(v___x_315_);
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_327_ = lean_box(2);
return v___x_327_;
}
else
{
lean_object* v_snd_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_347_; 
v_snd_328_ = lean_ctor_get(v_snd_281_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_snd_281_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_snd_281_, 0);
lean_dec(v_unused_348_);
v___x_330_ = v_snd_281_;
v_isShared_331_ = v_isSharedCheck_347_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_snd_328_);
lean_dec(v_snd_281_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_347_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_arg_332_; lean_object* v_arg_333_; lean_object* v_arg_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v_arg_332_ = lean_ctor_get(v___x_292_, 1);
lean_inc_ref_n(v_arg_332_, 2);
lean_dec_ref(v___x_292_);
v_arg_333_ = lean_ctor_get(v___x_312_, 1);
lean_inc_ref(v_arg_333_);
lean_dec_ref(v___x_312_);
v_arg_334_ = lean_ctor_get(v___x_315_, 1);
lean_inc_ref(v_arg_334_);
lean_dec_ref(v___x_315_);
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_335_);
lean_ctor_set(v___x_330_, 0, v_arg_332_);
v___x_337_ = v___x_330_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_arg_332_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_346_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_338_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(v___x_337_);
v_fst_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_fst_339_);
v_snd_340_ = lean_ctor_get(v___x_338_, 1);
lean_inc(v_snd_340_);
lean_dec_ref(v___x_338_);
v___x_341_ = l_Array_toSubarray___redArg(v___x_285_, v___x_287_, v___x_286_);
v___x_342_ = lean_array_push(v_snd_340_, v_fst_339_);
v___x_343_ = l_Subarray_copy___redArg(v___x_341_);
v___x_344_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_344_, 0, v_snd_328_);
lean_ctor_set(v___x_344_, 1, v_arg_334_);
lean_ctor_set(v___x_344_, 2, v_arg_333_);
lean_ctor_set(v___x_344_, 3, v___x_342_);
lean_ctor_set(v___x_344_, 4, v_arg_332_);
lean_ctor_set(v___x_344_, 5, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_349_; 
lean_dec_ref(v___x_285_);
lean_dec(v_snd_281_);
v___x_349_ = lean_box(1);
return v___x_349_;
}
}
else
{
lean_object* v_val_350_; 
lean_inc_ref(v_fst_280_);
lean_dec_ref(v___x_279_);
lean_dec(v___x_270_);
lean_dec_ref(v_assertion_265_);
v_val_350_ = lean_ctor_get(v_fst_280_, 0);
lean_inc(v_val_350_);
lean_dec_ref_known(v_fst_280_, 1);
return v_val_350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___boxed(lean_object* v_assertion_351_, lean_object* v_inv_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_assertion_351_, v_inv_352_);
lean_dec_ref(v_assertion_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0(lean_object* v_inv_354_, lean_object* v_inst_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(v_inv_354_, v_a_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1(lean_object* v_inst_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(v_a_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(lean_object* v_e_361_, lean_object* v___y_362_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_Expr_hasMVar(v_e_361_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v_e_361_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; lean_object* v_mctx_367_; lean_object* v___x_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_371_; lean_object* v_cache_372_; lean_object* v_zetaDeltaFVarIds_373_; lean_object* v_postponed_374_; lean_object* v_diag_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_384_; 
v___x_366_ = lean_st_ref_get(v___y_362_);
v_mctx_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_mctx_367_);
lean_dec(v___x_366_);
v___x_368_ = l_Lean_instantiateMVarsCore(v_mctx_367_, v_e_361_);
v_fst_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_snd_370_);
lean_dec_ref(v___x_368_);
v___x_371_ = lean_st_ref_take(v___y_362_);
v_cache_372_ = lean_ctor_get(v___x_371_, 1);
v_zetaDeltaFVarIds_373_ = lean_ctor_get(v___x_371_, 2);
v_postponed_374_ = lean_ctor_get(v___x_371_, 3);
v_diag_375_ = lean_ctor_get(v___x_371_, 4);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v___x_371_, 0);
lean_dec(v_unused_385_);
v___x_377_ = v___x_371_;
v_isShared_378_ = v_isSharedCheck_384_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_diag_375_);
lean_inc(v_postponed_374_);
lean_inc(v_zetaDeltaFVarIds_373_);
lean_inc(v_cache_372_);
lean_dec(v___x_371_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_384_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v_snd_370_);
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_snd_370_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_cache_372_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_zetaDeltaFVarIds_373_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_postponed_374_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_diag_375_);
v___x_380_ = v_reuseFailAlloc_383_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_st_ref_put(v___y_362_, v___x_380_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_fst_369_);
return v___x_382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg___boxed(lean_object* v_e_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_e_386_, v___y_387_);
lean_dec(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_object* v_e_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_e_390_, v___y_392_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___boxed(lean_object* v_e_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(v_e_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(lean_object* v_mvarId_404_, lean_object* v_x_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_404_, v_x_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_a_420_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_411_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_411_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg___boxed(lean_object* v_mvarId_428_, lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_mvarId_428_, v_x_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(lean_object* v_00_u03b1_436_, lean_object* v_mvarId_437_, lean_object* v_x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_mvarId_437_, v_x_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___boxed(lean_object* v_00_u03b1_445_, lean_object* v_mvarId_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(v_00_u03b1_445_, v_mvarId_446_, v_x_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object* v_inv_471_, lean_object* v_as_472_, size_t v_sz_473_, size_t v_i_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_a_482_; uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec(v_inv_471_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_b_475_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_a_490_; lean_object* v___x_491_; 
lean_dec_ref(v_b_475_);
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v___x_489_ = l_Lean_instInhabitedExpr;
v_a_490_ = lean_array_uget_borrowed(v_as_472_, v_i_474_);
lean_inc(v_a_490_);
v___x_491_ = l_Lean_MVarId_getType(v_a_490_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_492_, v___y_477_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = l_Lean_Expr_consumeMData(v_a_494_);
lean_dec(v_a_494_);
v___x_496_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_496_, 0, v___x_495_);
lean_inc(v_a_490_);
v___x_497_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_490_, v___x_496_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_523_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_523_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_523_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_523_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
if (lean_obj_tag(v_a_498_) == 1)
{
lean_object* v_val_502_; lean_object* v_snd_503_; lean_object* v_snd_504_; lean_object* v___x_505_; 
v_val_502_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_val_502_);
lean_dec_ref_known(v_a_498_, 1);
v_snd_503_ = lean_ctor_get(v_val_502_, 1);
lean_inc(v_snd_503_);
lean_dec(v_val_502_);
v_snd_504_ = lean_ctor_get(v_snd_503_, 1);
lean_inc(v_snd_504_);
lean_dec(v_snd_503_);
lean_inc(v_inv_471_);
v___x_505_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_504_, v_inv_471_);
lean_dec(v_snd_504_);
switch(lean_obj_tag(v___x_505_))
{
case 0:
{
lean_object* v_invariantUse_506_; lean_object* v_cursorSuffix_507_; lean_object* v_letMuts_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_invariantUse_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc_ref(v_invariantUse_506_);
lean_dec_ref_known(v___x_505_, 1);
v_cursorSuffix_507_ = lean_ctor_get(v_invariantUse_506_, 2);
lean_inc_ref(v_cursorSuffix_507_);
v_letMuts_508_ = lean_ctor_get(v_invariantUse_506_, 3);
lean_inc_ref(v_letMuts_508_);
lean_dec_ref(v_invariantUse_506_);
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_510_ = l_Lean_Expr_isAppOf(v_cursorSuffix_507_, v___x_509_);
lean_dec_ref(v_cursorSuffix_507_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_array_get(v___x_489_, v_letMuts_508_, v___x_511_);
lean_dec_ref(v_letMuts_508_);
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5));
v___x_514_ = l_Lean_Expr_isAppOf(v___x_512_, v___x_513_);
lean_dec(v___x_512_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_517_; 
lean_dec(v_inv_471_);
v___x_515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_515_);
v___x_517_ = v___x_500_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
else
{
lean_del_object(v___x_500_);
v_a_482_ = v___x_488_;
goto v___jp_481_;
}
}
else
{
lean_dec_ref(v_letMuts_508_);
lean_del_object(v___x_500_);
v_a_482_ = v___x_488_;
goto v___jp_481_;
}
}
case 1:
{
lean_del_object(v___x_500_);
v_a_482_ = v___x_488_;
goto v___jp_481_;
}
default: 
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec(v_inv_471_);
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_519_);
v___x_521_ = v___x_500_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_del_object(v___x_500_);
lean_dec(v_a_498_);
v_a_482_ = v___x_488_;
goto v___jp_481_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_inv_471_);
v_a_524_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_497_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_497_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_inv_471_);
v_a_532_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_493_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_493_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_inv_471_);
v_a_540_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_491_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_491_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
v___jp_481_:
{
size_t v___x_483_; size_t v___x_484_; 
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_add(v_i_474_, v___x_483_);
lean_inc_ref(v_a_482_);
v_i_474_ = v___x_484_;
v_b_475_ = v_a_482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object* v_inv_548_, lean_object* v_as_549_, lean_object* v_sz_550_, lean_object* v_i_551_, lean_object* v_b_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_550_);
lean_dec(v_sz_550_);
v_i_boxed_559_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_548_, v_as_549_, v_sz_boxed_558_, v_i_boxed_559_, v_b_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec_ref(v_as_549_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object* v_vcs_565_, lean_object* v_inv_566_, lean_object* v_letMutsTy_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0));
v___x_580_ = l_Lean_Expr_isAppOf(v_letMutsTy_567_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v_inv_566_);
goto v___jp_573_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = l_Lean_Expr_getAppNumArgs(v_letMutsTy_567_);
v___x_582_ = lean_unsigned_to_nat(2u);
v___x_583_ = lean_nat_dec_lt(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_sub(v___x_581_, v___x_584_);
lean_dec(v___x_581_);
lean_inc(v___x_585_);
v___x_586_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_567_, v___x_585_);
v___x_587_ = l_Lean_Expr_cleanupAnnotations(v___x_586_);
lean_dec_ref(v___x_586_);
v___x_588_ = l_Lean_Expr_isApp(v___x_587_);
if (v___x_588_ == 0)
{
lean_dec_ref(v___x_587_);
lean_dec(v___x_585_);
lean_dec(v_inv_566_);
goto v___jp_576_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = l_Lean_Expr_appFnCleanup___redArg(v___x_587_);
v___x_590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1));
v___x_591_ = l_Lean_Expr_isConstOf(v___x_589_, v___x_590_);
lean_dec_ref(v___x_589_);
if (v___x_591_ == 0)
{
lean_dec_ref(v___x_587_);
lean_dec(v___x_585_);
lean_dec(v_inv_566_);
goto v___jp_576_;
}
else
{
lean_object* v_arg_592_; lean_object* v___x_593_; lean_object* v_00_u03c3_594_; lean_object* v___x_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; 
v_arg_592_ = lean_ctor_get(v___x_587_, 1);
lean_inc_ref(v_arg_592_);
lean_dec_ref(v___x_587_);
v___x_593_ = lean_nat_sub(v___x_585_, v___x_584_);
lean_dec(v___x_585_);
v_00_u03c3_594_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_567_, v___x_593_);
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v_sz_596_ = lean_array_size(v_vcs_565_);
v___x_597_ = ((size_t)0ULL);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_566_, v_vcs_565_, v_sz_596_, v___x_597_, v___x_595_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_620_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_620_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_620_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_620_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_fst_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_618_; 
v_fst_603_ = lean_ctor_get(v_a_599_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_a_599_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_a_599_, 1);
lean_dec(v_unused_619_);
v___x_605_ = v_a_599_;
v_isShared_606_ = v_isSharedCheck_618_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_fst_603_);
lean_dec(v_a_599_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_618_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
if (lean_obj_tag(v_fst_603_) == 0)
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v_00_u03c3_594_);
lean_ctor_set(v___x_605_, 0, v_arg_592_);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_arg_592_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_00_u03c3_594_);
v___x_608_ = v_reuseFailAlloc_613_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_609_);
v___x_611_ = v___x_601_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_object* v_val_614_; lean_object* v___x_616_; 
lean_del_object(v___x_605_);
lean_dec_ref(v_00_u03c3_594_);
lean_dec_ref(v_arg_592_);
v_val_614_ = lean_ctor_get(v_fst_603_, 0);
lean_inc(v_val_614_);
lean_dec_ref_known(v_fst_603_, 1);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_val_614_);
v___x_616_ = v___x_601_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_val_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_00_u03c3_594_);
lean_dec_ref(v_arg_592_);
v_a_621_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_598_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_598_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
else
{
lean_dec(v___x_581_);
lean_dec(v_inv_566_);
goto v___jp_573_;
}
}
v___jp_573_:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(0);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
v___jp_576_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object* v_vcs_629_, lean_object* v_inv_630_, lean_object* v_letMutsTy_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_vcs_629_, v_inv_630_, v_letMutsTy_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec_ref(v_letMutsTy_631_);
lean_dec_ref(v_vcs_629_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__8(lean_object* v_dontRevert_638_, lean_object* v_as_639_, size_t v_i_640_, size_t v_stop_641_, lean_object* v_b_642_){
_start:
{
lean_object* v___y_644_; uint8_t v___x_648_; 
v___x_648_ = lean_usize_dec_eq(v_i_640_, v_stop_641_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_array_uget_borrowed(v_as_639_, v_i_640_);
lean_inc_ref(v_dontRevert_638_);
lean_inc(v___x_649_);
v___x_650_ = lean_apply_1(v_dontRevert_638_, v___x_649_);
v___x_651_ = lean_unbox(v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_inc(v___x_649_);
v___x_652_ = lean_array_push(v_b_642_, v___x_649_);
v___y_644_ = v___x_652_;
goto v___jp_643_;
}
else
{
v___y_644_ = v_b_642_;
goto v___jp_643_;
}
}
else
{
lean_dec_ref(v_dontRevert_638_);
return v_b_642_;
}
v___jp_643_:
{
size_t v___x_645_; size_t v___x_646_; 
v___x_645_ = ((size_t)1ULL);
v___x_646_ = lean_usize_add(v_i_640_, v___x_645_);
v_i_640_ = v___x_646_;
v_b_642_ = v___y_644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__8___boxed(lean_object* v_dontRevert_653_, lean_object* v_as_654_, lean_object* v_i_655_, lean_object* v_stop_656_, lean_object* v_b_657_){
_start:
{
size_t v_i_boxed_658_; size_t v_stop_boxed_659_; lean_object* v_res_660_; 
v_i_boxed_658_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_stop_boxed_659_ = lean_unbox_usize(v_stop_656_);
lean_dec(v_stop_656_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__8(v_dontRevert_653_, v_as_654_, v_i_boxed_658_, v_stop_boxed_659_, v_b_657_);
lean_dec_ref(v_as_654_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t v_sz_661_, size_t v_i_662_, lean_object* v_bs_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = lean_usize_dec_lt(v_i_662_, v_sz_661_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v_bs_663_);
return v___x_670_;
}
else
{
lean_object* v_v_671_; lean_object* v___x_672_; lean_object* v_bs_x27_673_; lean_object* v___x_674_; 
v_v_671_ = lean_array_uget(v_bs_663_, v_i_662_);
v___x_672_ = lean_unsigned_to_nat(0u);
v_bs_x27_673_ = lean_array_uset(v_bs_663_, v_i_662_, v___x_672_);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
v___x_674_ = lean_infer_type(v_v_671_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_add(v_i_662_, v___x_676_);
v___x_678_ = lean_array_uset(v_bs_x27_673_, v_i_662_, v_a_675_);
v_i_662_ = v___x_677_;
v_bs_663_ = v___x_678_;
goto _start;
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v_bs_x27_673_);
v_a_680_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_674_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_674_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object* v_sz_688_, lean_object* v_i_689_, lean_object* v_bs_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
size_t v_sz_boxed_696_; size_t v_i_boxed_697_; lean_object* v_res_698_; 
v_sz_boxed_696_ = lean_unbox_usize(v_sz_688_);
lean_dec(v_sz_688_);
v_i_boxed_697_ = lean_unbox_usize(v_i_689_);
lean_dec(v_i_689_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_boxed_696_, v_i_boxed_697_, v_bs_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_as_699_, size_t v_i_700_, size_t v_stop_701_, lean_object* v_b_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_eq(v_i_700_, v_stop_701_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; size_t v___x_707_; size_t v___x_708_; 
v___x_704_ = lean_array_uget_borrowed(v_as_699_, v_i_700_);
v___x_705_ = l_Lean_Expr_fvarId_x21(v___x_704_);
v___x_706_ = l_Lean_FVarIdSet_insert(v_b_702_, v___x_705_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_700_, v___x_707_);
v_i_700_ = v___x_708_;
v_b_702_ = v___x_706_;
goto _start;
}
else
{
return v_b_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_as_710_, lean_object* v_i_711_, lean_object* v_stop_712_, lean_object* v_b_713_){
_start:
{
size_t v_i_boxed_714_; size_t v_stop_boxed_715_; lean_object* v_res_716_; 
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_stop_boxed_715_ = lean_unbox_usize(v_stop_712_);
lean_dec(v_stop_712_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_as_710_, v_i_boxed_714_, v_stop_boxed_715_, v_b_713_);
lean_dec_ref(v_as_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_717_, lean_object* v_as_718_, size_t v_i_719_, size_t v_stop_720_, lean_object* v_b_721_){
_start:
{
lean_object* v___y_723_; uint8_t v___x_727_; 
v___x_727_ = lean_usize_dec_eq(v_i_719_, v_stop_720_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_728_ = lean_array_uget_borrowed(v_as_718_, v_i_719_);
v___x_729_ = l_Lean_Expr_fvarId_x21(v___x_728_);
lean_inc_ref(v_dontRevert_717_);
v___x_730_ = lean_apply_1(v_dontRevert_717_, v___x_729_);
v___x_731_ = lean_unbox(v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_inc(v___x_728_);
v___x_732_ = lean_array_push(v_b_721_, v___x_728_);
v___y_723_ = v___x_732_;
goto v___jp_722_;
}
else
{
v___y_723_ = v_b_721_;
goto v___jp_722_;
}
}
else
{
lean_dec_ref(v_dontRevert_717_);
return v_b_721_;
}
v___jp_722_:
{
size_t v___x_724_; size_t v___x_725_; 
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_719_, v___x_724_);
v_i_719_ = v___x_725_;
v_b_721_ = v___y_723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_733_, lean_object* v_as_734_, lean_object* v_i_735_, lean_object* v_stop_736_, lean_object* v_b_737_){
_start:
{
size_t v_i_boxed_738_; size_t v_stop_boxed_739_; lean_object* v_res_740_; 
v_i_boxed_738_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_stop_boxed_739_ = lean_unbox_usize(v_stop_736_);
lean_dec(v_stop_736_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_733_, v_as_734_, v_i_boxed_738_, v_stop_boxed_739_, v_b_737_);
lean_dec_ref(v_as_734_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_741_, size_t v_i_742_, size_t v_stop_743_, lean_object* v_b_744_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = lean_usize_dec_eq(v_i_742_, v_stop_743_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; size_t v___x_748_; size_t v___x_749_; 
v___x_746_ = lean_array_uget_borrowed(v_as_741_, v_i_742_);
lean_inc(v___x_746_);
v___x_747_ = l_Lean_collectFVars(v_b_744_, v___x_746_);
v___x_748_ = ((size_t)1ULL);
v___x_749_ = lean_usize_add(v_i_742_, v___x_748_);
v_i_742_ = v___x_749_;
v_b_744_ = v___x_747_;
goto _start;
}
else
{
return v_b_744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_751_, lean_object* v_i_752_, lean_object* v_stop_753_, lean_object* v_b_754_){
_start:
{
size_t v_i_boxed_755_; size_t v_stop_boxed_756_; lean_object* v_res_757_; 
v_i_boxed_755_ = lean_unbox_usize(v_i_752_);
lean_dec(v_i_752_);
v_stop_boxed_756_ = lean_unbox_usize(v_stop_753_);
lean_dec(v_stop_753_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_751_, v_i_boxed_755_, v_stop_boxed_756_, v_b_754_);
lean_dec_ref(v_as_751_);
return v_res_757_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___redArg(lean_object* v_k_758_, lean_object* v_t_759_){
_start:
{
if (lean_obj_tag(v_t_759_) == 0)
{
lean_object* v_k_760_; lean_object* v_l_761_; lean_object* v_r_762_; uint8_t v___x_763_; 
v_k_760_ = lean_ctor_get(v_t_759_, 1);
v_l_761_ = lean_ctor_get(v_t_759_, 3);
v_r_762_ = lean_ctor_get(v_t_759_, 4);
v___x_763_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_758_, v_k_760_);
switch(v___x_763_)
{
case 0:
{
v_t_759_ = v_l_761_;
goto _start;
}
case 1:
{
uint8_t v___x_765_; 
v___x_765_ = 1;
return v___x_765_;
}
default: 
{
v_t_759_ = v_r_762_;
goto _start;
}
}
}
else
{
uint8_t v___x_767_; 
v___x_767_ = 0;
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___redArg___boxed(lean_object* v_k_768_, lean_object* v_t_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___redArg(v_k_768_, v_t_769_);
lean_dec(v_t_769_);
lean_dec(v_k_768_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v___y_772_, lean_object* v_dontRevert_773_, lean_object* v_as_774_, size_t v_i_775_, size_t v_stop_776_, lean_object* v_b_777_){
_start:
{
lean_object* v___y_779_; uint8_t v___x_783_; 
v___x_783_ = lean_usize_dec_eq(v_i_775_, v_stop_776_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_array_uget_borrowed(v_as_774_, v_i_775_);
v___x_785_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___redArg(v___x_784_, v___y_772_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; uint8_t v___x_787_; 
lean_inc_ref(v_dontRevert_773_);
lean_inc(v___x_784_);
v___x_786_ = lean_apply_1(v_dontRevert_773_, v___x_784_);
v___x_787_ = lean_unbox(v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_inc(v___x_784_);
v___x_788_ = lean_array_push(v_b_777_, v___x_784_);
v___y_779_ = v___x_788_;
goto v___jp_778_;
}
else
{
v___y_779_ = v_b_777_;
goto v___jp_778_;
}
}
else
{
v___y_779_ = v_b_777_;
goto v___jp_778_;
}
}
else
{
lean_dec_ref(v_dontRevert_773_);
return v_b_777_;
}
v___jp_778_:
{
size_t v___x_780_; size_t v___x_781_; 
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_775_, v___x_780_);
v_i_775_ = v___x_781_;
v_b_777_ = v___y_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v___y_789_, lean_object* v_dontRevert_790_, lean_object* v_as_791_, lean_object* v_i_792_, lean_object* v_stop_793_, lean_object* v_b_794_){
_start:
{
size_t v_i_boxed_795_; size_t v_stop_boxed_796_; lean_object* v_res_797_; 
v_i_boxed_795_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_stop_boxed_796_ = lean_unbox_usize(v_stop_793_);
lean_dec(v_stop_793_);
v_res_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___y_789_, v_dontRevert_790_, v_as_791_, v_i_boxed_795_, v_stop_boxed_796_, v_b_794_);
lean_dec_ref(v_as_791_);
lean_dec(v___y_789_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t v_sz_798_, size_t v_i_799_, lean_object* v_bs_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = lean_usize_dec_lt(v_i_799_, v_sz_798_);
if (v___x_801_ == 0)
{
return v_bs_800_;
}
else
{
lean_object* v_v_802_; lean_object* v___x_803_; lean_object* v_bs_x27_804_; lean_object* v___x_805_; size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v_v_802_ = lean_array_uget(v_bs_800_, v_i_799_);
v___x_803_ = lean_unsigned_to_nat(0u);
v_bs_x27_804_ = lean_array_uset(v_bs_800_, v_i_799_, v___x_803_);
v___x_805_ = l_Lean_mkFVar(v_v_802_);
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_add(v_i_799_, v___x_806_);
v___x_808_ = lean_array_uset(v_bs_x27_804_, v_i_799_, v___x_805_);
v_i_799_ = v___x_807_;
v_bs_800_ = v___x_808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object* v_sz_810_, lean_object* v_i_811_, lean_object* v_bs_812_){
_start:
{
size_t v_sz_boxed_813_; size_t v_i_boxed_814_; lean_object* v_res_815_; 
v_sz_boxed_813_ = lean_unbox_usize(v_sz_810_);
lean_dec(v_sz_810_);
v_i_boxed_814_ = lean_unbox_usize(v_i_811_);
lean_dec(v_i_811_);
v_res_815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_boxed_813_, v_i_boxed_814_, v_bs_812_);
return v_res_815_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__0));
v___x_819_ = lean_box(1);
v___x_820_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_819_, v___x_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg(lean_object* v_dontRevert_821_, lean_object* v_a_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; size_t v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___x_840_; lean_object* v___x_841_; size_t v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___x_852_; lean_object* v___y_854_; size_t v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_box(1);
v___x_841_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__0));
v___x_852_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1);
v___x_862_ = 0;
v___x_863_ = 1;
lean_inc_ref(v_a_822_);
v___x_864_ = l_Lean_Meta_collectForwardDeps(v_a_822_, v___x_862_, v___x_863_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_897_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_897_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_897_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_897_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___y_870_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_array_get_size(v_a_865_);
v___x_893_ = lean_nat_dec_lt(v___x_828_, v___x_892_);
if (v___x_893_ == 0)
{
lean_dec(v_a_865_);
v___y_870_ = v___x_841_;
goto v___jp_869_;
}
else
{
size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; 
v___x_894_ = ((size_t)0ULL);
v___x_895_ = lean_usize_of_nat(v___x_892_);
lean_inc_ref(v_dontRevert_821_);
v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_821_, v_a_865_, v___x_894_, v___x_895_, v___x_841_);
lean_dec(v_a_865_);
v___y_870_ = v___x_896_;
goto v___jp_869_;
}
v___jp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_array_get_size(v___y_870_);
v___x_872_ = lean_array_get_size(v_a_822_);
lean_dec_ref(v_a_822_);
v___x_873_ = lean_nat_dec_eq(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; 
lean_del_object(v___x_867_);
v_sz_874_ = lean_array_size(v___y_870_);
v___x_875_ = ((size_t)0ULL);
lean_inc_ref(v___y_870_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_874_, v___x_875_, v___y_870_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; uint8_t v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = lean_nat_dec_lt(v___x_828_, v___x_871_);
if (v___x_878_ == 0)
{
v___y_854_ = v_a_877_;
v___y_855_ = v___x_875_;
v___y_856_ = v___y_870_;
v___y_857_ = v___x_840_;
goto v___jp_853_;
}
else
{
size_t v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_usize_of_nat(v___x_871_);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v___y_870_, v___x_875_, v___x_879_, v___x_840_);
v___y_854_ = v_a_877_;
v___y_855_ = v___x_875_;
v___y_856_ = v___y_870_;
v___y_857_ = v___x_880_;
goto v___jp_853_;
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v___y_870_);
lean_dec_ref(v_dontRevert_821_);
v_a_881_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_876_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec_ref(v_dontRevert_821_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___y_870_);
v___x_890_ = v___x_867_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___y_870_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_822_);
lean_dec_ref(v_dontRevert_821_);
return v___x_864_;
}
v___jp_829_:
{
size_t v_sz_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_sz_833_ = lean_array_size(v___y_832_);
lean_inc_ref(v___y_832_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_833_, v___y_830_, v___y_832_);
v___x_835_ = l_Array_append___redArg(v___y_831_, v___x_834_);
lean_dec_ref(v___x_834_);
v___x_836_ = lean_array_get_size(v___y_832_);
lean_dec_ref(v___y_832_);
v___x_837_ = lean_nat_dec_eq(v___x_836_, v___x_828_);
if (v___x_837_ == 0)
{
v_a_822_ = v___x_835_;
goto _start;
}
else
{
lean_object* v___x_839_; 
lean_dec_ref(v_dontRevert_821_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_835_);
return v___x_839_;
}
}
v___jp_842_:
{
lean_object* v_fvarIds_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_fvarIds_847_ = lean_ctor_get(v___y_846_, 2);
lean_inc_ref(v_fvarIds_847_);
lean_dec_ref(v___y_846_);
v___x_848_ = lean_array_get_size(v_fvarIds_847_);
v___x_849_ = lean_nat_dec_lt(v___x_828_, v___x_848_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_fvarIds_847_);
lean_dec(v___y_845_);
v___y_830_ = v___y_843_;
v___y_831_ = v___y_844_;
v___y_832_ = v___x_841_;
goto v___jp_829_;
}
else
{
size_t v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_usize_of_nat(v___x_848_);
lean_inc_ref(v_dontRevert_821_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___y_845_, v_dontRevert_821_, v_fvarIds_847_, v___y_843_, v___x_850_, v___x_841_);
lean_dec_ref(v_fvarIds_847_);
lean_dec(v___y_845_);
v___y_830_ = v___y_843_;
v___y_831_ = v___y_844_;
v___y_832_ = v___x_851_;
goto v___jp_829_;
}
}
v___jp_853_:
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_array_get_size(v___y_854_);
v___x_859_ = lean_nat_dec_lt(v___x_828_, v___x_858_);
if (v___x_859_ == 0)
{
lean_dec_ref(v___y_854_);
v___y_843_ = v___y_855_;
v___y_844_ = v___y_856_;
v___y_845_ = v___y_857_;
v___y_846_ = v___x_852_;
goto v___jp_842_;
}
else
{
size_t v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_usize_of_nat(v___x_858_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v___y_854_, v___y_855_, v___x_860_, v___x_852_);
lean_dec_ref(v___y_854_);
v___y_843_ = v___y_855_;
v___y_844_ = v___y_856_;
v___y_845_ = v___y_857_;
v___y_846_ = v___x_861_;
goto v___jp_842_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___boxed(lean_object* v_dontRevert_898_, lean_object* v_a_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg(v_dontRevert_898_, v_a_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_906_, lean_object* v_dontRevert_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___y_914_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_fvarIds_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__0));
v___x_921_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg___closed__1);
v___x_922_ = l_Lean_collectFVars(v___x_921_, v_e_906_);
v_fvarIds_923_ = lean_ctor_get(v___x_922_, 2);
lean_inc_ref(v_fvarIds_923_);
lean_dec_ref(v___x_922_);
v___x_924_ = lean_array_get_size(v_fvarIds_923_);
v___x_925_ = lean_nat_dec_lt(v___x_919_, v___x_924_);
if (v___x_925_ == 0)
{
lean_dec_ref(v_fvarIds_923_);
v___y_914_ = v___x_920_;
goto v___jp_913_;
}
else
{
size_t v___x_926_; size_t v___x_927_; lean_object* v___x_928_; 
v___x_926_ = ((size_t)0ULL);
v___x_927_ = lean_usize_of_nat(v___x_924_);
lean_inc_ref(v_dontRevert_907_);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__8(v_dontRevert_907_, v_fvarIds_923_, v___x_926_, v___x_927_, v___x_920_);
lean_dec_ref(v_fvarIds_923_);
v___y_914_ = v___x_928_;
goto v___jp_913_;
}
v___jp_913_:
{
size_t v_sz_915_; size_t v___x_916_; lean_object* v_xs_917_; lean_object* v___x_918_; 
v_sz_915_ = lean_array_size(v___y_914_);
v___x_916_ = ((size_t)0ULL);
v_xs_917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_915_, v___x_916_, v___y_914_);
v___x_918_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg(v_dontRevert_907_, v_xs_917_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_929_, lean_object* v_dontRevert_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_929_, v_dontRevert_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_936_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object* v_00_u03b2_937_, lean_object* v_k_938_, lean_object* v_t_939_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___redArg(v_k_938_, v_t_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object* v_00_u03b2_941_, lean_object* v_k_942_, lean_object* v_t_943_){
_start:
{
uint8_t v_res_944_; lean_object* v_r_945_; 
v_res_944_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_00_u03b2_941_, v_k_942_, v_t_943_);
lean_dec(v_t_943_);
lean_dec(v_k_942_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7(lean_object* v_dontRevert_946_, lean_object* v_inst_947_, lean_object* v_a_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___redArg(v_dontRevert_946_, v_a_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7___boxed(lean_object* v_dontRevert_955_, lean_object* v_inst_956_, lean_object* v_a_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__7(v_dontRevert_955_, v_inst_956_, v_a_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_970_, lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v_i_973_, lean_object* v_a_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_zero_980_; uint8_t v_isZero_981_; 
v_zero_980_ = lean_unsigned_to_nat(0u);
v_isZero_981_ = lean_nat_dec_eq(v_i_973_, v_zero_980_);
if (v_isZero_981_ == 1)
{
lean_object* v___x_982_; 
lean_dec(v_i_973_);
lean_dec(v___x_972_);
lean_dec_ref(v___x_971_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_a_974_);
return v___x_982_;
}
else
{
lean_object* v_one_983_; lean_object* v_n_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_one_983_ = lean_unsigned_to_nat(1u);
v_n_984_ = lean_nat_sub(v_i_973_, v_one_983_);
lean_dec(v_i_973_);
v___x_985_ = lean_array_fget_borrowed(v_a_970_, v_n_984_);
lean_inc_ref(v___x_971_);
v___x_986_ = l_Lean_LocalContext_getFVar_x21(v___x_971_, v___x_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_userName_987_; lean_object* v_type_988_; uint8_t v_bi_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_userName_987_ = lean_ctor_get(v___x_986_, 2);
lean_inc(v_userName_987_);
v_type_988_ = lean_ctor_get(v___x_986_, 3);
lean_inc_ref(v_type_988_);
v_bi_989_ = lean_ctor_get_uint8(v___x_986_, sizeof(void*)*4);
lean_dec_ref_known(v___x_986_, 4);
v___x_990_ = l_Lean_Expr_headBeta(v_type_988_);
v___x_991_ = lean_expr_abstract_range(v___x_990_, v_n_984_, v_a_970_);
lean_dec_ref(v___x_990_);
lean_inc_ref(v___x_991_);
v___x_992_ = l_Lean_Meta_getLevel(v___x_991_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_995_ = lean_box(0);
lean_inc_n(v___x_972_, 2);
v___x_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_972_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_997_, 0, v_a_993_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_mkConst(v___x_994_, v___x_997_);
v___x_999_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_972_);
lean_inc_ref(v___x_991_);
v___x_1000_ = l_Lean_mkLambda(v_userName_987_, v_bi_989_, v___x_991_, v_a_974_);
v___x_1001_ = l_Lean_mkApp3(v___x_998_, v___x_991_, v___x_999_, v___x_1000_);
v_i_973_ = v_n_984_;
v_a_974_ = v___x_1001_;
goto _start;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v___x_991_);
lean_dec(v_userName_987_);
lean_dec(v_n_984_);
lean_dec_ref(v_a_974_);
lean_dec(v___x_972_);
lean_dec_ref(v___x_971_);
v_a_1003_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_992_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_992_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
uint8_t v_nondep_1011_; 
v_nondep_1011_ = lean_ctor_get_uint8(v___x_986_, sizeof(void*)*5);
if (v_nondep_1011_ == 0)
{
lean_object* v_userName_1012_; lean_object* v_type_1013_; lean_object* v_value_1014_; uint8_t v___x_1015_; 
v_userName_1012_ = lean_ctor_get(v___x_986_, 2);
lean_inc(v_userName_1012_);
v_type_1013_ = lean_ctor_get(v___x_986_, 3);
lean_inc_ref(v_type_1013_);
v_value_1014_ = lean_ctor_get(v___x_986_, 4);
lean_inc_ref(v_value_1014_);
lean_dec_ref_known(v___x_986_, 5);
v___x_1015_ = lean_expr_has_loose_bvar(v_a_974_, v_zero_980_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
lean_dec_ref(v_value_1014_);
lean_dec_ref(v_type_1013_);
lean_dec(v_userName_1012_);
v___x_1016_ = lean_expr_lower_loose_bvars(v_a_974_, v_one_983_, v_one_983_);
lean_dec_ref(v_a_974_);
v_i_973_ = v_n_984_;
v_a_974_ = v___x_1016_;
goto _start;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = l_Lean_Expr_headBeta(v_type_1013_);
v___x_1019_ = lean_expr_abstract_range(v___x_1018_, v_n_984_, v_a_970_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = lean_expr_abstract_range(v_value_1014_, v_n_984_, v_a_970_);
lean_dec_ref(v_value_1014_);
v___x_1021_ = l_Lean_Expr_letE___override(v_userName_1012_, v___x_1019_, v___x_1020_, v_a_974_, v_nondep_1011_);
v_i_973_ = v_n_984_;
v_a_974_ = v___x_1021_;
goto _start;
}
}
else
{
lean_object* v_userName_1023_; lean_object* v_type_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_userName_1023_ = lean_ctor_get(v___x_986_, 2);
lean_inc(v_userName_1023_);
v_type_1024_ = lean_ctor_get(v___x_986_, 3);
lean_inc_ref(v_type_1024_);
lean_dec_ref_known(v___x_986_, 5);
v___x_1025_ = l_Lean_Expr_headBeta(v_type_1024_);
v___x_1026_ = lean_expr_abstract_range(v___x_1025_, v_n_984_, v_a_970_);
lean_dec_ref(v___x_1025_);
lean_inc_ref(v___x_1026_);
v___x_1027_ = l_Lean_Meta_getLevel(v___x_1026_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1030_ = lean_box(0);
lean_inc_n(v___x_972_, 2);
v___x_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_972_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_a_1028_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_mkConst(v___x_1029_, v___x_1032_);
v___x_1034_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_972_);
v___x_1035_ = 0;
lean_inc_ref(v___x_1026_);
v___x_1036_ = l_Lean_mkLambda(v_userName_1023_, v___x_1035_, v___x_1026_, v_a_974_);
v___x_1037_ = l_Lean_mkApp3(v___x_1033_, v___x_1026_, v___x_1034_, v___x_1036_);
v_i_973_ = v_n_984_;
v_a_974_ = v___x_1037_;
goto _start;
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v___x_1026_);
lean_dec(v_userName_1023_);
lean_dec(v_n_984_);
lean_dec_ref(v_a_974_);
lean_dec(v___x_972_);
lean_dec_ref(v___x_971_);
v_a_1039_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1027_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1027_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1047_, lean_object* v___x_1048_, lean_object* v___x_1049_, lean_object* v_i_1050_, lean_object* v_a_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1047_, v___x_1048_, v___x_1049_, v_i_1050_, v_a_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v_a_1047_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1062_, lean_object* v_dontRevert_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_box(0);
lean_inc_ref(v_e_1062_);
v___x_1070_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1062_, v_dontRevert_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v_lctx_1072_; lean_object* v___x_1073_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v_lctx_1072_ = lean_ctor_get(v_a_1064_, 2);
lean_inc(v_a_1067_);
lean_inc_ref(v_a_1066_);
lean_inc(v_a_1065_);
lean_inc_ref(v_a_1064_);
lean_inc_ref(v_e_1062_);
v___x_1073_ = lean_infer_type(v_e_1062_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1095_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1095_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1095_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = l_Lean_Expr_cleanupAnnotations(v_a_1074_);
lean_dec(v_a_1074_);
v___x_1079_ = l_Lean_Expr_isApp(v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1081_; 
lean_dec_ref(v___x_1078_);
lean_dec(v_a_1071_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_e_1062_);
v___x_1081_ = v___x_1076_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_e_1062_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1078_);
lean_dec_ref(v___x_1078_);
v___x_1084_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1085_ = l_Lean_Expr_isConstOf(v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1087_; 
lean_dec_ref(v___x_1083_);
lean_dec(v_a_1071_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_e_1062_);
v___x_1087_ = v___x_1076_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_e_1062_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_del_object(v___x_1076_);
v___x_1089_ = l_Lean_Expr_constLevels_x21(v___x_1083_);
lean_dec_ref(v___x_1083_);
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = l_List_get_x21Internal___redArg(v___x_1069_, v___x_1089_, v___x_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_array_get_size(v_a_1071_);
v___x_1093_ = lean_expr_abstract(v_e_1062_, v_a_1071_);
lean_dec_ref(v_e_1062_);
lean_inc_ref(v_lctx_1072_);
v___x_1094_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1071_, v_lctx_1072_, v___x_1091_, v___x_1092_, v___x_1093_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1071_);
return v___x_1094_;
}
}
}
}
else
{
lean_dec(v_a_1071_);
lean_dec_ref(v_e_1062_);
return v___x_1073_;
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_e_1062_);
v_a_1096_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1070_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1070_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1104_, lean_object* v_dontRevert_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1104_, v_dontRevert_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1112_, lean_object* v___x_1113_, lean_object* v___x_1114_, lean_object* v_n_1115_, lean_object* v_i_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1112_, v___x_1113_, v___x_1114_, v_i_1116_, v_a_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1125_, lean_object* v___x_1126_, lean_object* v___x_1127_, lean_object* v_n_1128_, lean_object* v_i_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1125_, v___x_1126_, v___x_1127_, v_n_1128_, v_i_1129_, v_a_1130_, v_a_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_n_1128_);
lean_dec_ref(v_a_1125_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1144_, lean_object* v_lhs_1145_, lean_object* v_rhs_1146_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1148_ = lean_box(0);
lean_inc(v_lvl_1144_);
v___x_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_lvl_1144_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_mkConst(v___x_1147_, v___x_1149_);
v___x_1151_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1144_);
v___x_1152_ = l_Lean_mkApp3(v___x_1150_, v___x_1151_, v_lhs_1145_, v_rhs_1146_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1159_, lean_object* v_lhs_1160_, lean_object* v_rhs_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1163_ = lean_box(0);
lean_inc(v_lvl_1159_);
v___x_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_lvl_1159_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = l_Lean_mkConst(v___x_1162_, v___x_1164_);
v___x_1166_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1159_);
v___x_1167_ = l_Lean_mkApp3(v___x_1165_, v___x_1166_, v_lhs_1160_, v_rhs_1161_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1168_){
_start:
{
lean_object* v_lvl_1169_; lean_object* v_cursorPred_1170_; lean_object* v_letMutsPred_1171_; lean_object* v___x_1172_; 
v_lvl_1169_ = lean_ctor_get(v_p_1168_, 0);
lean_inc(v_lvl_1169_);
v_cursorPred_1170_ = lean_ctor_get(v_p_1168_, 1);
lean_inc_ref(v_cursorPred_1170_);
v_letMutsPred_1171_ = lean_ctor_get(v_p_1168_, 2);
lean_inc_ref(v_letMutsPred_1171_);
lean_dec_ref(v_p_1168_);
v___x_1172_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1169_, v_cursorPred_1170_, v_letMutsPred_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(lean_object* v_x_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_obj_tag_nat(v_x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl___boxed(lean_object* v_x_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___impl(v_x_1175_);
lean_dec(v_x_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1177_, lean_object* v_k_1178_){
_start:
{
if (lean_obj_tag(v_t_1177_) == 3)
{
lean_object* v_e_1179_; lean_object* v___x_1180_; 
v_e_1179_ = lean_ctor_get(v_t_1177_, 0);
lean_inc_ref(v_e_1179_);
lean_dec_ref_known(v_t_1177_, 1);
v___x_1180_ = lean_apply_1(v_k_1178_, v_e_1179_);
return v___x_1180_;
}
else
{
lean_dec(v_t_1177_);
return v_k_1178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1181_, lean_object* v_ctorIdx_1182_, lean_object* v_t_1183_, lean_object* v_h_1184_, lean_object* v_k_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1183_, v_k_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1187_, lean_object* v_ctorIdx_1188_, lean_object* v_t_1189_, lean_object* v_h_1190_, lean_object* v_k_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1187_, v_ctorIdx_1188_, v_t_1189_, v_h_1190_, v_k_1191_);
lean_dec(v_ctorIdx_1188_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1193_, lean_object* v_punit_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1193_, v_punit_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1196_, lean_object* v_t_1197_, lean_object* v_h_1198_, lean_object* v_punit_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1197_, v_punit_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1201_, lean_object* v_false_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1201_, v_false_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1204_, lean_object* v_t_1205_, lean_object* v_h_1206_, lean_object* v_false_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1205_, v_false_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1209_, lean_object* v_true_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1209_, v_true_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1212_, lean_object* v_t_1213_, lean_object* v_h_1214_, lean_object* v_true_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1213_, v_true_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1217_, lean_object* v_other_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1217_, v_other_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1220_, lean_object* v_t_1221_, lean_object* v_h_1222_, lean_object* v_other_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1221_, v_other_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1225_){
_start:
{
lean_object* v_snd_1227_; lean_object* v_fst_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1267_; 
v_snd_1227_ = lean_ctor_get(v_a_1225_, 1);
v_fst_1228_ = lean_ctor_get(v_a_1225_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_a_1225_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1230_ = v_a_1225_;
v_isShared_1231_ = v_isSharedCheck_1267_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snd_1227_);
lean_inc(v_fst_1228_);
lean_dec(v_a_1225_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1267_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1266_; 
v_fst_1232_ = lean_ctor_get(v_snd_1227_, 0);
v_snd_1233_ = lean_ctor_get(v_snd_1227_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_snd_1227_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1235_ = v_snd_1227_;
v_isShared_1236_ = v_isSharedCheck_1266_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_snd_1233_);
lean_inc(v_fst_1232_);
lean_dec(v_snd_1227_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1266_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1237_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1238_ = lean_unsigned_to_nat(4u);
v___x_1239_ = l_Lean_Expr_isAppOfArity(v_fst_1232_, v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1241_; 
if (v_isShared_1236_ == 0)
{
v___x_1241_ = v___x_1235_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_fst_1232_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_snd_1233_);
v___x_1241_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1241_);
v___x_1243_ = v___x_1230_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_fst_1228_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1247_ = lean_unsigned_to_nat(3u);
v___x_1248_ = lean_unsigned_to_nat(2u);
v___x_1249_ = l_Lean_Expr_getAppNumArgs(v_fst_1232_);
v___x_1250_ = lean_nat_sub(v___x_1249_, v___x_1248_);
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_sub(v___x_1250_, v___x_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = l_Lean_Expr_getRevArg_x21(v_fst_1232_, v___x_1252_);
v___x_1254_ = lean_array_push(v_snd_1233_, v___x_1253_);
v___x_1255_ = lean_nat_add(v_fst_1228_, v___x_1251_);
lean_dec(v_fst_1228_);
v___x_1256_ = lean_nat_sub(v___x_1249_, v___x_1247_);
lean_dec(v___x_1249_);
v___x_1257_ = lean_nat_sub(v___x_1256_, v___x_1251_);
lean_dec(v___x_1256_);
v___x_1258_ = l_Lean_Expr_getRevArg_x21(v_fst_1232_, v___x_1257_);
lean_dec(v_fst_1232_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1254_);
lean_ctor_set(v___x_1235_, 0, v___x_1258_);
v___x_1260_ = v___x_1235_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1254_);
v___x_1260_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1260_);
lean_ctor_set(v___x_1230_, 0, v___x_1255_);
v___x_1262_ = v___x_1230_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v_a_1225_ = v___x_1262_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1268_);
return v_res_1270_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_letMutsTuple_1271_, lean_object* v___x_1272_, uint8_t v___x_1273_, lean_object* v_fvarId_1274_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1271_);
v___x_1276_ = l_Lean_instBEqFVarId_beq(v_fvarId_1274_, v___x_1275_);
lean_dec(v___x_1275_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Lean_LocalContext_contains(v___x_1272_, v_fvarId_1274_);
return v___x_1277_;
}
else
{
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1___boxed(lean_object* v_letMutsTuple_1278_, lean_object* v___x_1279_, lean_object* v___x_1280_, lean_object* v_fvarId_1281_){
_start:
{
uint8_t v___x_10026__boxed_1282_; uint8_t v_res_1283_; lean_object* v_r_1284_; 
v___x_10026__boxed_1282_ = lean_unbox(v___x_1280_);
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_letMutsTuple_1278_, v___x_1279_, v___x_10026__boxed_1282_, v_fvarId_1281_);
lean_dec(v_fvarId_1281_);
lean_dec_ref(v___x_1279_);
lean_dec_ref(v_letMutsTuple_1278_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_fst_1285_, lean_object* v_p_1286_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_inc(v_fst_1285_);
v___x_1287_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1285_);
v___x_1288_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1285_, v___x_1287_, v_p_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1318_, lean_object* v___x_1319_, lean_object* v_xs_1320_, lean_object* v_letMuts_1321_, lean_object* v_as_1322_, size_t v_sz_1323_, size_t v_i_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_a_1332_; uint8_t v___x_1336_; 
v___x_1336_ = lean_usize_dec_lt(v_i_1324_, v_sz_1323_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_b_1325_);
return v___x_1337_;
}
else
{
lean_object* v_snd_1338_; lean_object* v_fst_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1652_; 
v_snd_1338_ = lean_ctor_get(v_b_1325_, 1);
v_fst_1339_ = lean_ctor_get(v_b_1325_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_b_1325_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1341_ = v_b_1325_;
v_isShared_1342_ = v_isSharedCheck_1652_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_snd_1338_);
lean_inc(v_fst_1339_);
lean_dec(v_b_1325_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1652_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1651_; 
v_fst_1343_ = lean_ctor_get(v_snd_1338_, 0);
v_snd_1344_ = lean_ctor_get(v_snd_1338_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_snd_1338_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1346_ = v_snd_1338_;
v_isShared_1347_ = v_isSharedCheck_1651_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_inc(v_fst_1343_);
lean_dec(v_snd_1338_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1651_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_a_1360_; lean_object* v___x_1361_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1359_ = lean_box(0);
v_a_1360_ = lean_array_uget_borrowed(v_as_1322_, v_i_1324_);
lean_inc(v_a_1360_);
v___x_1361_ = l_Lean_MVarId_getType(v_a_1360_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1362_, v___y_1327_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v_prefixPoint_x3f_1367_; lean_object* v_suffixPoint_x3f_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = l_Lean_Expr_consumeMData(v_a_1364_);
lean_dec(v_a_1364_);
lean_inc_ref(v___x_1365_);
v___x_1476_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1476_, 0, v___x_1365_);
lean_inc(v_a_1360_);
v___x_1477_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1360_, v___x_1476_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
if (lean_obj_tag(v_a_1478_) == 1)
{
lean_object* v_val_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1626_; 
v_val_1479_ = lean_ctor_get(v_a_1478_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_a_1478_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1481_ = v_a_1478_;
v_isShared_1482_ = v_isSharedCheck_1626_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_val_1479_);
lean_dec(v_a_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1626_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_snd_1483_; lean_object* v_fst_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1625_; 
v_snd_1483_ = lean_ctor_get(v_val_1479_, 1);
v_fst_1484_ = lean_ctor_get(v_val_1479_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_val_1479_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1486_ = v_val_1479_;
v_isShared_1487_ = v_isSharedCheck_1625_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snd_1483_);
lean_inc(v_fst_1484_);
lean_dec(v_val_1479_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1625_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_fst_1488_; lean_object* v_snd_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1624_; 
v_fst_1488_ = lean_ctor_get(v_snd_1483_, 0);
v_snd_1489_ = lean_ctor_get(v_snd_1483_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_snd_1483_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1491_ = v_snd_1483_;
v_isShared_1492_ = v_isSharedCheck_1624_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snd_1489_);
lean_inc(v_fst_1488_);
lean_dec(v_snd_1483_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1624_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_prefixPoint_x3f_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___x_1573_; 
lean_inc(v_inv_1318_);
v___x_1573_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1489_, v_inv_1318_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_invariantUse_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1623_; 
v_invariantUse_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1623_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_invariantUse_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1623_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_conditionIdx_1578_; lean_object* v_cursorPrefix_1579_; lean_object* v_letMutsTuple_1580_; uint8_t v___x_1581_; 
v_conditionIdx_1578_ = lean_ctor_get(v_invariantUse_1574_, 0);
lean_inc(v_conditionIdx_1578_);
v_cursorPrefix_1579_ = lean_ctor_get(v_invariantUse_1574_, 1);
lean_inc_ref(v_cursorPrefix_1579_);
v_letMutsTuple_1580_ = lean_ctor_get(v_invariantUse_1574_, 4);
lean_inc_ref(v_letMutsTuple_1580_);
lean_dec_ref(v_invariantUse_1574_);
v___x_1581_ = lean_nat_dec_eq(v_conditionIdx_1578_, v___x_1357_);
lean_dec(v_conditionIdx_1578_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v_letMutsTuple_1580_);
lean_dec_ref(v_cursorPrefix_1579_);
lean_del_object(v___x_1576_);
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1488_);
lean_del_object(v___x_1486_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_del_object(v___x_1341_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_fst_1343_);
lean_ctor_set(v___x_1582_, 1, v_snd_1344_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_fst_1339_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v_a_1332_ = v___x_1583_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1585_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1579_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_dec_ref(v_letMutsTuple_1580_);
lean_dec_ref(v_cursorPrefix_1579_);
lean_del_object(v___x_1576_);
v_prefixPoint_x3f_1494_ = v_fst_1339_;
v___y_1495_ = v___y_1326_;
v___y_1496_ = v___y_1327_;
v___y_1497_ = v___y_1328_;
v___y_1498_ = v___y_1329_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v_fst_1339_);
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__12));
lean_inc_ref(v_xs_1320_);
v___x_1587_ = l_Lean_Meta_mkProjection(v_xs_1320_, v___x_1586_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l_Lean_Meta_mkEq(v_a_1588_, v_cursorPrefix_1579_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
lean_inc_ref(v_letMuts_1321_);
v___x_1591_ = l_Lean_Meta_mkEq(v_letMuts_1321_, v_letMutsTuple_1580_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
lean_inc_n(v_fst_1484_, 3);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_fst_1484_, v_a_1592_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_fst_1484_, v_a_1590_);
v___x_1595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1595_, 0, v_fst_1484_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
lean_ctor_set(v___x_1595_, 2, v___x_1593_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 1);
lean_ctor_set(v___x_1576_, 0, v___x_1595_);
v___x_1597_ = v___x_1576_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
v_prefixPoint_x3f_1494_ = v___x_1597_;
v___y_1495_ = v___y_1326_;
v___y_1496_ = v___y_1327_;
v___y_1497_ = v___y_1328_;
v___y_1498_ = v___y_1329_;
goto v___jp_1493_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_a_1590_);
lean_del_object(v___x_1576_);
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1488_);
lean_del_object(v___x_1486_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1599_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1591_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1591_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v_letMutsTuple_1580_);
lean_del_object(v___x_1576_);
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1488_);
lean_del_object(v___x_1486_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1607_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1589_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1589_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_letMutsTuple_1580_);
lean_dec_ref(v_cursorPrefix_1579_);
lean_del_object(v___x_1576_);
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1488_);
lean_del_object(v___x_1486_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1615_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1587_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1587_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1573_);
v_prefixPoint_x3f_1494_ = v_fst_1339_;
v___y_1495_ = v___y_1326_;
v___y_1496_ = v___y_1327_;
v___y_1497_ = v___y_1328_;
v___y_1498_ = v___y_1329_;
goto v___jp_1493_;
}
v___jp_1493_:
{
lean_object* v___x_1499_; 
lean_inc(v_inv_1318_);
v___x_1499_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_fst_1488_, v_inv_1318_);
lean_dec(v_fst_1488_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_invariantUse_1500_; lean_object* v_conditionIdx_1501_; lean_object* v_cursorSuffix_1502_; lean_object* v_letMutsTuple_1503_; uint8_t v___x_1504_; 
v_invariantUse_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc_ref(v_invariantUse_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v_conditionIdx_1501_ = lean_ctor_get(v_invariantUse_1500_, 0);
lean_inc(v_conditionIdx_1501_);
v_cursorSuffix_1502_ = lean_ctor_get(v_invariantUse_1500_, 2);
lean_inc_ref(v_cursorSuffix_1502_);
v_letMutsTuple_1503_ = lean_ctor_get(v_invariantUse_1500_, 4);
lean_inc_ref(v_letMutsTuple_1503_);
lean_dec_ref(v_invariantUse_1500_);
v___x_1504_ = lean_nat_dec_eq(v_conditionIdx_1501_, v___x_1357_);
lean_dec(v_conditionIdx_1501_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1506_; 
lean_dec_ref(v_letMutsTuple_1503_);
lean_dec_ref(v_cursorSuffix_1502_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_del_object(v___x_1341_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v_snd_1344_);
lean_ctor_set(v___x_1491_, 0, v_fst_1343_);
v___x_1506_ = v___x_1491_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_fst_1343_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_snd_1344_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1506_);
lean_ctor_set(v___x_1486_, 0, v_prefixPoint_x3f_1494_);
v___x_1508_ = v___x_1486_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_prefixPoint_x3f_1494_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
v_a_1332_ = v___x_1508_;
goto v___jp_1331_;
}
}
}
else
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
lean_del_object(v___x_1491_);
lean_del_object(v___x_1486_);
v___x_1511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1512_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1502_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_dec_ref(v_letMutsTuple_1503_);
lean_dec_ref(v_cursorSuffix_1502_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
v_prefixPoint_x3f_1367_ = v_prefixPoint_x3f_1494_;
v_suffixPoint_x3f_1368_ = v_fst_1343_;
v___y_1369_ = v___y_1495_;
v___y_1370_ = v___y_1496_;
v___y_1371_ = v___y_1497_;
v___y_1372_ = v___y_1498_;
goto v___jp_1366_;
}
else
{
uint8_t v___x_1513_; 
v___x_1513_ = l_Lean_Expr_isFVar(v_letMutsTuple_1503_);
if (v___x_1513_ == 0)
{
lean_dec_ref(v_letMutsTuple_1503_);
lean_dec_ref(v_cursorSuffix_1502_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
v_prefixPoint_x3f_1367_ = v_prefixPoint_x3f_1494_;
v_suffixPoint_x3f_1368_ = v_fst_1343_;
v___y_1369_ = v___y_1495_;
v___y_1370_ = v___y_1496_;
v___y_1371_ = v___y_1497_;
v___y_1372_ = v___y_1498_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1514_; lean_object* v___f_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = lean_box(v___x_1504_);
lean_inc_ref(v___x_1319_);
lean_inc_ref(v_letMutsTuple_1503_);
v___f_1515_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1515_, 0, v_letMutsTuple_1503_);
lean_closure_set(v___f_1515_, 1, v___x_1319_);
lean_closure_set(v___f_1515_, 2, v___x_1514_);
v___x_1516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1320_);
v___x_1517_ = l_Lean_Meta_mkProjection(v_xs_1320_, v___x_1516_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_Meta_mkEq(v_a_1518_, v_cursorSuffix_1502_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1521_, 0, v_snd_1489_);
lean_closure_set(v___x_1521_, 1, v___f_1515_);
lean_inc(v_a_1360_);
v___x_1522_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1360_, v___x_1521_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = l_Lean_Expr_replaceFVar(v_a_1523_, v_letMutsTuple_1503_, v_letMuts_1321_);
lean_dec(v_a_1523_);
if (lean_obj_tag(v_fst_1343_) == 1)
{
lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_a_1520_);
lean_del_object(v___x_1481_);
v_val_1525_ = lean_ctor_get(v_fst_1343_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_fst_1343_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1527_ = v_fst_1343_;
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_dec(v_fst_1343_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_lvl_1529_; lean_object* v_cursorPred_1530_; lean_object* v_letMutsPred_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1542_; 
v_lvl_1529_ = lean_ctor_get(v_val_1525_, 0);
v_cursorPred_1530_ = lean_ctor_get(v_val_1525_, 1);
v_letMutsPred_1531_ = lean_ctor_get(v_val_1525_, 2);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_val_1525_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1533_ = v_val_1525_;
v_isShared_1534_ = v_isSharedCheck_1542_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_letMutsPred_1531_);
lean_inc(v_cursorPred_1530_);
lean_inc(v_lvl_1529_);
lean_dec(v_val_1525_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1542_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_fst_1484_, v_letMutsPred_1531_, v___x_1524_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 2, v___x_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_lvl_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_cursorPred_1530_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1537_);
v___x_1539_ = v___x_1527_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v_prefixPoint_x3f_1367_ = v_prefixPoint_x3f_1494_;
v_suffixPoint_x3f_1368_ = v___x_1539_;
v___y_1369_ = v___y_1495_;
v___y_1370_ = v___y_1496_;
v___y_1371_ = v___y_1497_;
v___y_1372_ = v___y_1498_;
goto v___jp_1366_;
}
}
}
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
lean_dec(v_fst_1343_);
lean_inc(v_fst_1484_);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_fst_1484_, v_a_1520_);
v___x_1545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1545_, 0, v_fst_1484_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
lean_ctor_set(v___x_1545_, 2, v___x_1524_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1545_);
v___x_1547_ = v___x_1481_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
v_prefixPoint_x3f_1367_ = v_prefixPoint_x3f_1494_;
v_suffixPoint_x3f_1368_ = v___x_1547_;
v___y_1369_ = v___y_1495_;
v___y_1370_ = v___y_1496_;
v___y_1371_ = v___y_1497_;
v___y_1372_ = v___y_1498_;
goto v___jp_1366_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_a_1520_);
lean_dec_ref(v_letMutsTuple_1503_);
lean_dec(v_prefixPoint_x3f_1494_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1549_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1522_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1522_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v___f_1515_);
lean_dec_ref(v_letMutsTuple_1503_);
lean_dec(v_prefixPoint_x3f_1494_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1557_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1519_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1519_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v___f_1515_);
lean_dec_ref(v_letMutsTuple_1503_);
lean_dec_ref(v_cursorSuffix_1502_);
lean_dec(v_prefixPoint_x3f_1494_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1565_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1517_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1517_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1499_);
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_del_object(v___x_1486_);
lean_dec(v_fst_1484_);
lean_del_object(v___x_1481_);
v_prefixPoint_x3f_1367_ = v_prefixPoint_x3f_1494_;
v_suffixPoint_x3f_1368_ = v_fst_1343_;
v___y_1369_ = v___y_1495_;
v___y_1370_ = v___y_1496_;
v___y_1371_ = v___y_1497_;
v___y_1372_ = v___y_1498_;
goto v___jp_1366_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1478_);
v_prefixPoint_x3f_1367_ = v_fst_1339_;
v_suffixPoint_x3f_1368_ = v_fst_1343_;
v___y_1369_ = v___y_1326_;
v___y_1370_ = v___y_1327_;
v___y_1371_ = v___y_1328_;
v___y_1372_ = v___y_1329_;
goto v___jp_1366_;
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec(v_fst_1339_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1627_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1477_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1477_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
v___jp_1366_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1));
v___x_1374_ = lean_unsigned_to_nat(3u);
v___x_1375_ = l_Lean_Expr_isAppOfArity(v___x_1365_, v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v___x_1365_);
lean_del_object(v___x_1346_);
lean_del_object(v___x_1341_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_suffixPoint_x3f_1368_);
lean_ctor_set(v___x_1376_, 1, v_snd_1344_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_prefixPoint_x3f_1367_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v_a_1332_ = v___x_1377_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1378_ = l_Lean_Expr_appFn_x21(v___x_1365_);
v___x_1379_ = l_Lean_Expr_appArg_x21(v___x_1378_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1381_ = l_Lean_Expr_isAppOfArity(v___x_1379_, v___x_1380_, v___x_1374_);
if (v___x_1381_ == 0)
{
lean_dec_ref(v___x_1379_);
lean_dec_ref(v___x_1365_);
v___y_1349_ = v_prefixPoint_x3f_1367_;
v___y_1350_ = v_suffixPoint_x3f_1368_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1382_ = lean_unsigned_to_nat(2u);
v___x_1383_ = l_Lean_Expr_getAppNumArgs(v___x_1379_);
v___x_1384_ = lean_nat_sub(v___x_1383_, v___x_1382_);
lean_dec(v___x_1383_);
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = lean_nat_sub(v___x_1384_, v___x_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = l_Lean_Expr_getRevArg_x21(v___x_1379_, v___x_1386_);
lean_dec_ref(v___x_1379_);
lean_inc(v_inv_1318_);
v___x_1388_ = l_Lean_mkMVar(v_inv_1318_);
v___x_1389_ = lean_expr_eqv(v___x_1387_, v___x_1388_);
lean_dec_ref(v___x_1388_);
lean_dec_ref(v___x_1387_);
if (v___x_1389_ == 0)
{
lean_dec_ref(v___x_1365_);
v___y_1349_ = v_prefixPoint_x3f_1367_;
v___y_1350_ = v_suffixPoint_x3f_1368_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_del_object(v___x_1346_);
lean_del_object(v___x_1341_);
v___x_1390_ = l_Lean_Expr_appArg_x21(v___x_1365_);
lean_dec_ref(v___x_1365_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___x_1358_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1357_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1466_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v_snd_1395_ = lean_ctor_get(v_a_1394_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_a_1394_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_a_1394_, 0);
lean_dec(v_unused_1467_);
v___x_1397_ = v_a_1394_;
v_isShared_1398_ = v_isSharedCheck_1466_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_dec(v_a_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1466_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1465_; 
v_fst_1399_ = lean_ctor_get(v_snd_1395_, 0);
v_snd_1400_ = lean_ctor_get(v_snd_1395_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_snd_1395_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1402_ = v_snd_1395_;
v_isShared_1403_ = v_isSharedCheck_1465_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_snd_1400_);
lean_inc(v_fst_1399_);
lean_dec(v_snd_1395_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1465_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_points_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_points_1404_ = lean_ctor_get(v_snd_1344_, 0);
v___x_1405_ = lean_array_get_size(v_points_1404_);
v___x_1406_ = lean_array_get_size(v_snd_1400_);
v___x_1407_ = lean_nat_dec_lt(v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1409_; 
lean_dec(v_snd_1400_);
lean_dec(v_fst_1399_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v_snd_1344_);
lean_ctor_set(v___x_1402_, 0, v_suffixPoint_x3f_1368_);
v___x_1409_ = v___x_1402_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_suffixPoint_x3f_1368_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_snd_1344_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1409_);
lean_ctor_set(v___x_1397_, 0, v_prefixPoint_x3f_1367_);
v___x_1411_ = v___x_1397_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_prefixPoint_x3f_1367_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
v_a_1332_ = v___x_1411_;
goto v___jp_1331_;
}
}
}
else
{
lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v_snd_1344_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; lean_object* v_unused_1464_; 
v_unused_1463_ = lean_ctor_get(v_snd_1344_, 1);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_snd_1344_, 0);
lean_dec(v_unused_1464_);
v___x_1415_ = v_snd_1344_;
v_isShared_1416_ = v_isSharedCheck_1462_;
goto v_resetjp_1414_;
}
else
{
lean_dec(v_snd_1344_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1462_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_1418_ = l_Lean_Expr_isConstOf(v_fst_1399_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1420_ = l_Lean_Expr_isAppOfArity(v_fst_1399_, v___x_1419_, v___x_1385_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
v___x_1422_ = l_Lean_Expr_isAppOfArity(v_fst_1399_, v___x_1421_, v___x_1385_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_fst_1399_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1423_);
lean_ctor_set(v___x_1415_, 0, v_snd_1400_);
v___x_1425_ = v___x_1415_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_snd_1400_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1427_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1425_);
lean_ctor_set(v___x_1402_, 0, v_suffixPoint_x3f_1368_);
v___x_1427_ = v___x_1402_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_suffixPoint_x3f_1368_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1427_);
lean_ctor_set(v___x_1397_, 0, v_prefixPoint_x3f_1367_);
v___x_1429_ = v___x_1397_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_prefixPoint_x3f_1367_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v_a_1332_ = v___x_1429_;
goto v___jp_1331_;
}
}
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_dec(v_fst_1399_);
v___x_1433_ = lean_box(2);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1433_);
lean_ctor_set(v___x_1415_, 0, v_snd_1400_);
v___x_1435_ = v___x_1415_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_snd_1400_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1435_);
lean_ctor_set(v___x_1402_, 0, v_suffixPoint_x3f_1368_);
v___x_1437_ = v___x_1402_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_suffixPoint_x3f_1368_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1437_);
lean_ctor_set(v___x_1397_, 0, v_prefixPoint_x3f_1367_);
v___x_1439_ = v___x_1397_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_prefixPoint_x3f_1367_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v_a_1332_ = v___x_1439_;
goto v___jp_1331_;
}
}
}
}
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_dec(v_fst_1399_);
v___x_1443_ = lean_box(1);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1443_);
lean_ctor_set(v___x_1415_, 0, v_snd_1400_);
v___x_1445_ = v___x_1415_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_snd_1400_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1445_);
lean_ctor_set(v___x_1402_, 0, v_suffixPoint_x3f_1368_);
v___x_1447_ = v___x_1402_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_suffixPoint_x3f_1368_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1447_);
lean_ctor_set(v___x_1397_, 0, v_prefixPoint_x3f_1367_);
v___x_1449_ = v___x_1397_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_prefixPoint_x3f_1367_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
v_a_1332_ = v___x_1449_;
goto v___jp_1331_;
}
}
}
}
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_fst_1399_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1359_);
lean_ctor_set(v___x_1415_, 0, v_snd_1400_);
v___x_1454_ = v___x_1415_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_snd_1400_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1359_);
v___x_1454_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1456_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1454_);
lean_ctor_set(v___x_1402_, 0, v_suffixPoint_x3f_1368_);
v___x_1456_ = v___x_1402_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_suffixPoint_x3f_1368_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1456_);
lean_ctor_set(v___x_1397_, 0, v_prefixPoint_x3f_1367_);
v___x_1458_ = v___x_1397_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_prefixPoint_x3f_1367_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
v_a_1332_ = v___x_1458_;
goto v___jp_1331_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_suffixPoint_x3f_1368_);
lean_dec(v_prefixPoint_x3f_1367_);
lean_dec(v_snd_1344_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1468_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1393_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1393_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec(v_fst_1339_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1635_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1363_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1363_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_del_object(v___x_1341_);
lean_dec(v_fst_1339_);
lean_dec_ref(v_letMuts_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec(v_inv_1318_);
v_a_1643_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1361_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1361_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
v___jp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___y_1350_);
v___x_1352_ = v___x_1346_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___y_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_snd_1344_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1352_);
lean_ctor_set(v___x_1341_, 0, v___y_1349_);
v___x_1354_ = v___x_1341_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___y_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
v_a_1332_ = v___x_1354_;
goto v___jp_1331_;
}
}
}
}
}
}
v___jp_1331_:
{
size_t v___x_1333_; size_t v___x_1334_; 
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = lean_usize_add(v_i_1324_, v___x_1333_);
v_i_1324_ = v___x_1334_;
v_b_1325_ = v_a_1332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1653_, lean_object* v___x_1654_, lean_object* v_xs_1655_, lean_object* v_letMuts_1656_, lean_object* v_as_1657_, lean_object* v_sz_1658_, lean_object* v_i_1659_, lean_object* v_b_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
size_t v_sz_boxed_1666_; size_t v_i_boxed_1667_; lean_object* v_res_1668_; 
v_sz_boxed_1666_ = lean_unbox_usize(v_sz_1658_);
lean_dec(v_sz_1658_);
v_i_boxed_1667_ = lean_unbox_usize(v_i_1659_);
lean_dec(v_i_1659_);
v_res_1668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1653_, v___x_1654_, v_xs_1655_, v_letMuts_1656_, v_as_1657_, v_sz_boxed_1666_, v_i_boxed_1667_, v_b_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v_as_1657_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1678_, lean_object* v_inv_1679_, lean_object* v_xs_1680_, lean_object* v_letMuts_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_lctx_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; size_t v_sz_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
v_lctx_1687_ = lean_ctor_get(v_a_1682_, 2);
v___x_1688_ = lean_box(0);
v___x_1689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1690_ = lean_array_size(v_vcs_1678_);
v___x_1691_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1687_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1679_, v_lctx_1687_, v_xs_1680_, v_letMuts_1681_, v_vcs_1678_, v_sz_1690_, v___x_1691_, v___x_1689_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1736_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1736_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1736_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_snd_1701_; lean_object* v_fst_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1735_; 
v_snd_1701_ = lean_ctor_get(v_a_1693_, 1);
v_fst_1702_ = lean_ctor_get(v_a_1693_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_a_1693_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1704_ = v_a_1693_;
v_isShared_1705_ = v_isSharedCheck_1735_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_snd_1701_);
lean_inc(v_fst_1702_);
lean_dec(v_a_1693_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1735_;
goto v_resetjp_1703_;
}
v___jp_1697_:
{
lean_object* v___x_1699_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1688_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1688_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
v_resetjp_1703_:
{
if (lean_obj_tag(v_fst_1702_) == 0)
{
lean_del_object(v___x_1704_);
lean_dec(v_snd_1701_);
goto v___jp_1697_;
}
else
{
lean_object* v_fst_1706_; 
v_fst_1706_ = lean_ctor_get(v_snd_1701_, 0);
lean_inc(v_fst_1706_);
if (lean_obj_tag(v_fst_1706_) == 0)
{
lean_dec_ref_known(v_fst_1702_, 1);
lean_del_object(v___x_1704_);
lean_dec(v_snd_1701_);
goto v___jp_1697_;
}
else
{
lean_object* v_snd_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1733_; 
lean_del_object(v___x_1695_);
v_snd_1707_ = lean_ctor_get(v_snd_1701_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_snd_1701_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v_snd_1701_, 0);
lean_dec(v_unused_1734_);
v___x_1709_ = v_snd_1701_;
v_isShared_1710_ = v_isSharedCheck_1733_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_snd_1707_);
lean_dec(v_snd_1701_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1733_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_val_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1732_; 
v_val_1711_ = lean_ctor_get(v_fst_1702_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_fst_1702_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1713_ = v_fst_1702_;
v_isShared_1714_ = v_isSharedCheck_1732_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_val_1711_);
lean_dec(v_fst_1702_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1732_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_val_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1731_; 
v_val_1715_ = lean_ctor_get(v_fst_1706_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_fst_1706_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1717_ = v_fst_1706_;
v_isShared_1718_ = v_isSharedCheck_1731_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_val_1715_);
lean_dec(v_fst_1706_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1731_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v_val_1715_);
v___x_1720_ = v___x_1709_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_val_1715_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_snd_1707_);
v___x_1720_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v___x_1720_);
lean_ctor_set(v___x_1704_, 0, v_val_1711_);
v___x_1722_ = v___x_1704_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_val_1711_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1722_);
v___x_1724_ = v___x_1717_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1726_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1724_);
v___x_1726_ = v___x_1713_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_a_1737_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1692_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1692_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1745_, lean_object* v_inv_1746_, lean_object* v_xs_1747_, lean_object* v_letMuts_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1745_, v_inv_1746_, v_xs_1747_, v_letMuts_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec_ref(v_vcs_1745_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_1755_, lean_object* v_a_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1756_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_1763_, lean_object* v_a_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_1763_, v_a_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_MVarId_getDecl(v_m_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v_userName_1779_; lean_object* v_lctx_1780_; lean_object* v_type_1781_; lean_object* v_localInstances_1782_; uint8_t v_kind_1783_; lean_object* v_numScopeArgs_1784_; lean_object* v___x_1785_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v_userName_1779_ = lean_ctor_get(v_a_1778_, 0);
lean_inc(v_userName_1779_);
v_lctx_1780_ = lean_ctor_get(v_a_1778_, 1);
lean_inc_ref(v_lctx_1780_);
v_type_1781_ = lean_ctor_get(v_a_1778_, 2);
lean_inc_ref(v_type_1781_);
v_localInstances_1782_ = lean_ctor_get(v_a_1778_, 4);
lean_inc_ref(v_localInstances_1782_);
v_kind_1783_ = lean_ctor_get_uint8(v_a_1778_, sizeof(void*)*7);
v_numScopeArgs_1784_ = lean_ctor_get(v_a_1778_, 5);
lean_inc(v_numScopeArgs_1784_);
lean_dec(v_a_1778_);
v___x_1785_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1780_, v_localInstances_1782_, v_type_1781_, v_kind_1783_, v_userName_1779_, v_numScopeArgs_1784_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1794_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1794_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1794_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1790_ = l_Lean_Expr_mvarId_x21(v_a_1786_);
lean_dec(v_a_1786_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1790_);
v___x_1792_ = v___x_1788_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_a_1795_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1785_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1785_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_a_1803_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1777_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1777_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_1824_){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_1852_ = lean_unsigned_to_nat(2u);
v___x_1853_ = l_Lean_Expr_isAppOfArity(v_e_1824_, v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1855_ = lean_unsigned_to_nat(3u);
v___x_1856_ = l_Lean_Expr_isAppOfArity(v_e_1824_, v___x_1854_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1858_ = l_Lean_Expr_isAppOfArity(v_e_1824_, v___x_1857_, v___x_1855_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1860_ = l_Lean_Expr_isAppOfArity(v_e_1824_, v___x_1859_, v___x_1855_);
if (v___x_1860_ == 0)
{
goto v___jp_1825_;
}
else
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Expr_appArg_x21(v_e_1824_);
if (lean_obj_tag(v___x_1861_) == 6)
{
lean_object* v_binderName_1862_; lean_object* v_binderType_1863_; lean_object* v_body_1864_; uint8_t v_binderInfo_1865_; lean_object* v___x_1866_; 
lean_dec_ref(v_e_1824_);
v_binderName_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_binderName_1862_);
v_binderType_1863_ = lean_ctor_get(v___x_1861_, 1);
lean_inc_ref(v_binderType_1863_);
v_body_1864_ = lean_ctor_get(v___x_1861_, 2);
lean_inc_ref(v_body_1864_);
v_binderInfo_1865_ = lean_ctor_get_uint8(v___x_1861_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_1861_, 3);
v___x_1866_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_1864_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_dec_ref(v_binderType_1863_);
lean_dec(v_binderName_1862_);
return v___x_1866_;
}
else
{
lean_object* v_val_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1884_; 
v_val_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1884_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_val_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1884_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v_fst_1871_; lean_object* v_snd_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1883_; 
v_fst_1871_ = lean_ctor_get(v_val_1867_, 0);
v_snd_1872_ = lean_ctor_get(v_val_1867_, 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_val_1867_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1874_ = v_val_1867_;
v_isShared_1875_ = v_isSharedCheck_1883_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_snd_1872_);
lean_inc(v_fst_1871_);
lean_dec(v_val_1867_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1883_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = l_Lean_mkForall(v_binderName_1862_, v_binderInfo_1865_, v_binderType_1863_, v_snd_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 1, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_fst_1871_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1878_);
v___x_1880_ = v___x_1869_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1861_);
goto v___jp_1825_;
}
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = l_Lean_Expr_appFn_x21(v_e_1824_);
v___x_1886_ = l_Lean_Expr_appArg_x21(v___x_1885_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_1886_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_dec_ref(v_e_1824_);
return v___x_1887_;
}
else
{
lean_object* v_val_1888_; lean_object* v_snd_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_val_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v_snd_1889_ = lean_ctor_get(v_val_1888_, 1);
lean_inc(v_snd_1889_);
lean_dec(v_val_1888_);
v___x_1890_ = l_Lean_Expr_appArg_x21(v_e_1824_);
lean_dec_ref(v_e_1824_);
v___x_1891_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_1890_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_dec(v_snd_1889_);
return v___x_1891_;
}
else
{
lean_object* v_val_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1909_; 
v_val_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1909_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_val_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1909_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v_fst_1896_; lean_object* v_snd_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1908_; 
v_fst_1896_ = lean_ctor_get(v_val_1892_, 0);
v_snd_1897_ = lean_ctor_get(v_val_1892_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_val_1892_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1899_ = v_val_1892_;
v_isShared_1900_ = v_isSharedCheck_1908_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_snd_1897_);
lean_inc(v_fst_1896_);
lean_dec(v_val_1892_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1908_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = l_Lean_mkOr(v_snd_1889_, v_snd_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_fst_1896_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1903_);
v___x_1905_ = v___x_1894_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = l_Lean_Expr_appFn_x21(v_e_1824_);
v___x_1911_ = l_Lean_Expr_appArg_x21(v___x_1910_);
lean_dec_ref(v___x_1910_);
v___x_1912_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_1911_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_dec_ref(v_e_1824_);
return v___x_1912_;
}
else
{
lean_object* v_val_1913_; lean_object* v_snd_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_val_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v_snd_1914_ = lean_ctor_get(v_val_1913_, 1);
lean_inc(v_snd_1914_);
lean_dec(v_val_1913_);
v___x_1915_ = l_Lean_Expr_appArg_x21(v_e_1824_);
lean_dec_ref(v_e_1824_);
v___x_1916_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_dec(v_snd_1914_);
return v___x_1916_;
}
else
{
lean_object* v_val_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1934_; 
v_val_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1934_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_val_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1934_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v_fst_1921_; lean_object* v_snd_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1933_; 
v_fst_1921_ = lean_ctor_get(v_val_1917_, 0);
v_snd_1922_ = lean_ctor_get(v_val_1917_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_val_1917_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1924_ = v_val_1917_;
v_isShared_1925_ = v_isSharedCheck_1933_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snd_1922_);
lean_inc(v_fst_1921_);
lean_dec(v_val_1917_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1933_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = l_Lean_mkAnd(v_snd_1914_, v_snd_1922_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1926_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_fst_1921_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1930_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1928_);
v___x_1930_ = v___x_1919_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1935_ = lean_box(0);
v___x_1936_ = l_Lean_Expr_getAppFn(v_e_1824_);
v___x_1937_ = l_Lean_Expr_constLevels_x21(v___x_1936_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = l_List_get_x21Internal___redArg(v___x_1935_, v___x_1937_, v___x_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = l_Lean_Expr_getAppNumArgs(v_e_1824_);
v___x_1942_ = lean_nat_sub(v___x_1941_, v___x_1940_);
lean_dec(v___x_1941_);
v___x_1943_ = lean_nat_sub(v___x_1942_, v___x_1940_);
lean_dec(v___x_1942_);
v___x_1944_ = l_Lean_Expr_getRevArg_x21(v_e_1824_, v___x_1943_);
lean_dec_ref(v_e_1824_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1939_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
return v___x_1946_;
}
v___jp_1825_:
{
if (lean_obj_tag(v_e_1824_) == 8)
{
lean_object* v_declName_1826_; lean_object* v_type_1827_; lean_object* v_value_1828_; lean_object* v_body_1829_; uint8_t v_nondep_1830_; lean_object* v___x_1831_; 
v_declName_1826_ = lean_ctor_get(v_e_1824_, 0);
lean_inc(v_declName_1826_);
v_type_1827_ = lean_ctor_get(v_e_1824_, 1);
lean_inc_ref(v_type_1827_);
v_value_1828_ = lean_ctor_get(v_e_1824_, 2);
lean_inc_ref(v_value_1828_);
v_body_1829_ = lean_ctor_get(v_e_1824_, 3);
lean_inc_ref(v_body_1829_);
v_nondep_1830_ = lean_ctor_get_uint8(v_e_1824_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1824_, 4);
v___x_1831_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref(v_value_1828_);
lean_dec_ref(v_type_1827_);
lean_dec(v_declName_1826_);
return v___x_1831_;
}
else
{
lean_object* v_val_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1849_; 
v_val_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1849_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_val_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1849_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_fst_1836_; lean_object* v_snd_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1848_; 
v_fst_1836_ = lean_ctor_get(v_val_1832_, 0);
v_snd_1837_ = lean_ctor_get(v_val_1832_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_val_1832_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1839_ = v_val_1832_;
v_isShared_1840_ = v_isSharedCheck_1848_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_snd_1837_);
lean_inc(v_fst_1836_);
lean_dec(v_val_1832_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1848_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = l_Lean_Expr_letE___override(v_declName_1826_, v_type_1827_, v_value_1828_, v_snd_1837_, v_nondep_1830_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_fst_1836_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1843_);
v___x_1845_ = v___x_1834_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
else
{
lean_object* v___x_1850_; 
lean_dec_ref(v_e_1824_);
v___x_1850_ = lean_box(0);
return v___x_1850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_1947_){
_start:
{
lean_object* v___x_1948_; 
lean_inc_ref(v_e_1947_);
v___x_1948_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_1947_);
if (lean_obj_tag(v___x_1948_) == 0)
{
return v_e_1947_;
}
else
{
lean_object* v_val_1949_; lean_object* v_fst_1950_; lean_object* v_snd_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec_ref(v_e_1947_);
v_val_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_val_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v_fst_1950_ = lean_ctor_get(v_val_1949_, 0);
lean_inc_n(v_fst_1950_, 2);
v_snd_1951_ = lean_ctor_get(v_val_1949_, 1);
lean_inc(v_snd_1951_);
lean_dec(v_val_1949_);
v___x_1952_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1950_);
v___x_1953_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1950_, v___x_1952_, v_snd_1951_);
return v___x_1953_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Array_mkArray0___redArg();
return v___x_1964_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2003_ = l_String_toRawSubstring_x27(v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2015_ = l_String_toRawSubstring_x27(v___x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2025_, lean_object* v_default_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v___x_2032_; lean_object* v_handlers_2033_; 
v___x_2032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2033_ = l_Lean_Syntax_SepArray_ofElems(v___x_2032_, v_handlers_2025_);
switch(lean_obj_tag(v_default_2026_))
{
case 0:
{
lean_object* v_ref_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_ref_2034_ = lean_ctor_get(v_a_2029_, 2);
v___x_2035_ = 0;
v___x_2036_ = l_Lean_SourceInfo_fromRef(v_ref_2034_, v___x_2035_);
v___x_2037_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2038_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2036_, 3);
v___x_2039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2036_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2041_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2042_ = l_Array_append___redArg(v___x_2041_, v_handlers_2033_);
lean_dec_ref(v_handlers_2033_);
v___x_2043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2036_);
lean_ctor_set(v___x_2043_, 1, v___x_2040_);
lean_ctor_set(v___x_2043_, 2, v___x_2042_);
v___x_2044_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2036_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = l_Lean_Syntax_node3(v___x_2036_, v___x_2037_, v___x_2039_, v___x_2043_, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
case 1:
{
lean_object* v_toCold_2048_; lean_object* v_ref_2049_; lean_object* v_quotContext_2050_; lean_object* v_currMacroScope_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v_toCold_2048_ = lean_ctor_get(v_a_2029_, 0);
v_ref_2049_ = lean_ctor_get(v_a_2029_, 2);
v_quotContext_2050_ = lean_ctor_get(v_toCold_2048_, 8);
v_currMacroScope_2051_ = lean_ctor_get(v_toCold_2048_, 9);
v___x_2052_ = 0;
v___x_2053_ = l_Lean_SourceInfo_fromRef(v_ref_2049_, v___x_2052_);
v___x_2054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2053_, 12);
v___x_2056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2053_);
lean_ctor_set(v___x_2062_, 1, v___x_2060_);
v___x_2063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2053_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2067_ = l_Array_append___redArg(v___x_2066_, v_handlers_2033_);
lean_dec_ref(v_handlers_2033_);
v___x_2068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2053_);
lean_ctor_set(v___x_2068_, 1, v___x_2032_);
v___x_2069_ = lean_array_push(v___x_2067_, v___x_2068_);
v___x_2070_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2051_);
lean_inc(v_quotContext_2050_);
v___x_2072_ = l_Lean_addMacroScope(v_quotContext_2050_, v___x_2071_, v_currMacroScope_2051_);
v___x_2073_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27));
v___x_2074_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2053_);
lean_ctor_set(v___x_2074_, 1, v___x_2070_);
lean_ctor_set(v___x_2074_, 2, v___x_2072_);
lean_ctor_set(v___x_2074_, 3, v___x_2073_);
v___x_2075_ = lean_array_push(v___x_2069_, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2053_);
lean_ctor_set(v___x_2076_, 1, v___x_2059_);
lean_ctor_set(v___x_2076_, 2, v___x_2075_);
v___x_2077_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2053_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = l_Lean_Syntax_node3(v___x_2053_, v___x_2063_, v___x_2065_, v___x_2076_, v___x_2078_);
v___x_2080_ = l_Lean_Syntax_node2(v___x_2053_, v___x_2061_, v___x_2062_, v___x_2079_);
v___x_2081_ = l_Lean_Syntax_node1(v___x_2053_, v___x_2059_, v___x_2080_);
v___x_2082_ = l_Lean_Syntax_node1(v___x_2053_, v___x_2058_, v___x_2081_);
v___x_2083_ = l_Lean_Syntax_node1(v___x_2053_, v___x_2057_, v___x_2082_);
v___x_2084_ = l_Lean_Syntax_node2(v___x_2053_, v___x_2054_, v___x_2056_, v___x_2083_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
case 2:
{
lean_object* v_toCold_2086_; lean_object* v_ref_2087_; lean_object* v_quotContext_2088_; lean_object* v_currMacroScope_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_toCold_2086_ = lean_ctor_get(v_a_2029_, 0);
v_ref_2087_ = lean_ctor_get(v_a_2029_, 2);
v_quotContext_2088_ = lean_ctor_get(v_toCold_2086_, 8);
v_currMacroScope_2089_ = lean_ctor_get(v_toCold_2086_, 9);
v___x_2090_ = 0;
v___x_2091_ = l_Lean_SourceInfo_fromRef(v_ref_2087_, v___x_2090_);
v___x_2092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2093_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2091_, 12);
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2091_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2098_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2091_);
lean_ctor_set(v___x_2100_, 1, v___x_2098_);
v___x_2101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2091_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2105_ = l_Array_append___redArg(v___x_2104_, v_handlers_2033_);
lean_dec_ref(v_handlers_2033_);
v___x_2106_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2091_);
lean_ctor_set(v___x_2106_, 1, v___x_2032_);
v___x_2107_ = lean_array_push(v___x_2105_, v___x_2106_);
v___x_2108_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29);
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30));
lean_inc(v_currMacroScope_2089_);
lean_inc(v_quotContext_2088_);
v___x_2110_ = l_Lean_addMacroScope(v_quotContext_2088_, v___x_2109_, v_currMacroScope_2089_);
v___x_2111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32));
v___x_2112_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2091_);
lean_ctor_set(v___x_2112_, 1, v___x_2108_);
lean_ctor_set(v___x_2112_, 2, v___x_2110_);
lean_ctor_set(v___x_2112_, 3, v___x_2111_);
v___x_2113_ = lean_array_push(v___x_2107_, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2091_);
lean_ctor_set(v___x_2114_, 1, v___x_2097_);
lean_ctor_set(v___x_2114_, 2, v___x_2113_);
v___x_2115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2091_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = l_Lean_Syntax_node3(v___x_2091_, v___x_2101_, v___x_2103_, v___x_2114_, v___x_2116_);
v___x_2118_ = l_Lean_Syntax_node2(v___x_2091_, v___x_2099_, v___x_2100_, v___x_2117_);
v___x_2119_ = l_Lean_Syntax_node1(v___x_2091_, v___x_2097_, v___x_2118_);
v___x_2120_ = l_Lean_Syntax_node1(v___x_2091_, v___x_2096_, v___x_2119_);
v___x_2121_ = l_Lean_Syntax_node1(v___x_2091_, v___x_2095_, v___x_2120_);
v___x_2122_ = l_Lean_Syntax_node2(v___x_2091_, v___x_2092_, v___x_2094_, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
default: 
{
lean_object* v_e_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_e_2124_ = lean_ctor_get(v_default_2026_, 0);
lean_inc_ref(v_e_2124_);
lean_dec_ref_known(v_default_2026_, 1);
v___x_2125_ = lean_box(1);
v___x_2126_ = l_Lean_PrettyPrinter_delab(v_e_2124_, v___x_2125_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2163_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2163_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2163_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_ref_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v_ref_2131_ = lean_ctor_get(v_a_2029_, 2);
v___x_2132_ = 0;
v___x_2133_ = l_Lean_SourceInfo_fromRef(v_ref_2131_, v___x_2132_);
v___x_2134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2133_, 11);
v___x_2136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2133_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2133_);
lean_ctor_set(v___x_2142_, 1, v___x_2140_);
v___x_2143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2133_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2147_ = l_Array_append___redArg(v___x_2146_, v_handlers_2033_);
lean_dec_ref(v_handlers_2033_);
v___x_2148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2133_);
lean_ctor_set(v___x_2148_, 1, v___x_2032_);
v___x_2149_ = lean_array_push(v___x_2147_, v___x_2148_);
v___x_2150_ = lean_array_push(v___x_2149_, v_a_2127_);
v___x_2151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2133_);
lean_ctor_set(v___x_2151_, 1, v___x_2139_);
lean_ctor_set(v___x_2151_, 2, v___x_2150_);
v___x_2152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2133_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = l_Lean_Syntax_node3(v___x_2133_, v___x_2143_, v___x_2145_, v___x_2151_, v___x_2153_);
v___x_2155_ = l_Lean_Syntax_node2(v___x_2133_, v___x_2141_, v___x_2142_, v___x_2154_);
v___x_2156_ = l_Lean_Syntax_node1(v___x_2133_, v___x_2139_, v___x_2155_);
v___x_2157_ = l_Lean_Syntax_node1(v___x_2133_, v___x_2138_, v___x_2156_);
v___x_2158_ = l_Lean_Syntax_node1(v___x_2133_, v___x_2137_, v___x_2157_);
v___x_2159_ = l_Lean_Syntax_node2(v___x_2133_, v___x_2134_, v___x_2136_, v___x_2158_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2159_);
v___x_2161_ = v___x_2129_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
else
{
lean_dec_ref(v_handlers_2033_);
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2164_, lean_object* v_default_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2164_, v_default_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
lean_dec(v_a_2169_);
lean_dec_ref(v_a_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec_ref(v_handlers_2164_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v___x_2175_; 
v___x_2175_ = l_Lean_Expr_hasMVar(v_e_2172_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_e_2172_);
return v___x_2176_;
}
else
{
lean_object* v___x_2177_; lean_object* v_mctx_2178_; lean_object* v___x_2179_; lean_object* v_fst_2180_; lean_object* v_snd_2181_; lean_object* v___x_2182_; lean_object* v_cache_2183_; lean_object* v_zetaDeltaFVarIds_2184_; lean_object* v_postponed_2185_; lean_object* v_diag_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2195_; 
v___x_2177_ = lean_st_ref_get(v___y_2173_);
v_mctx_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc_ref(v_mctx_2178_);
lean_dec(v___x_2177_);
v___x_2179_ = l_Lean_instantiateMVarsCore(v_mctx_2178_, v_e_2172_);
v_fst_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_fst_2180_);
v_snd_2181_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_snd_2181_);
lean_dec_ref(v___x_2179_);
v___x_2182_ = lean_st_ref_take(v___y_2173_);
v_cache_2183_ = lean_ctor_get(v___x_2182_, 1);
v_zetaDeltaFVarIds_2184_ = lean_ctor_get(v___x_2182_, 2);
v_postponed_2185_ = lean_ctor_get(v___x_2182_, 3);
v_diag_2186_ = lean_ctor_get(v___x_2182_, 4);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; 
v_unused_2196_ = lean_ctor_get(v___x_2182_, 0);
lean_dec(v_unused_2196_);
v___x_2188_ = v___x_2182_;
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_diag_2186_);
lean_inc(v_postponed_2185_);
lean_inc(v_zetaDeltaFVarIds_2184_);
lean_inc(v_cache_2183_);
lean_dec(v___x_2182_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v_snd_2181_);
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_snd_2181_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_cache_2183_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_zetaDeltaFVarIds_2184_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v_postponed_2185_);
lean_ctor_set(v_reuseFailAlloc_2194_, 4, v_diag_2186_);
v___x_2191_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_st_ref_put(v___y_2173_, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_fst_2180_);
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2197_, v___y_2198_);
lean_dec(v___y_2198_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2201_, v___y_2207_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v___y_2225_);
lean_inc_ref(v___y_2224_);
v___x_2233_ = lean_apply_9(v_x_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, lean_box(0));
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2245_, lean_object* v_x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___f_2256_; lean_object* v___x_2257_; 
lean_inc(v___y_2250_);
lean_inc_ref(v___y_2249_);
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
v___f_2256_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2256_, 0, v_x_2246_);
lean_closure_set(v___f_2256_, 1, v___y_2247_);
lean_closure_set(v___f_2256_, 2, v___y_2248_);
lean_closure_set(v___f_2256_, 3, v___y_2249_);
lean_closure_set(v___f_2256_, 4, v___y_2250_);
v___x_2257_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2245_, v___f_2256_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2257_) == 0)
{
return v___x_2257_;
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2266_, lean_object* v_x_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2266_, v_x_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2278_, lean_object* v_mvarId_2279_, lean_object* v_x_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2279_, v_x_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2291_, lean_object* v_mvarId_2292_, lean_object* v_x_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2291_, v_mvarId_2292_, v_x_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2304_, lean_object* v_inv_2305_, lean_object* v_xs_2306_, uint8_t v___x_2307_, lean_object* v___x_2308_, lean_object* v_letMuts_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; 
lean_inc_ref(v_letMuts_2309_);
lean_inc_ref(v_xs_2306_);
v___x_2319_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2304_, v_inv_2305_, v_xs_2306_, v_letMuts_2309_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2396_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2396_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2396_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
if (lean_obj_tag(v_a_2320_) == 1)
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2391_; 
lean_del_object(v___x_2322_);
v_val_2324_ = lean_ctor_get(v_a_2320_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_a_2320_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2326_ = v_a_2320_;
v_isShared_2327_ = v_isSharedCheck_2391_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v_a_2320_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2391_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_snd_2328_; lean_object* v_fst_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2390_; 
v_snd_2328_ = lean_ctor_get(v_val_2324_, 1);
v_fst_2329_ = lean_ctor_get(v_val_2324_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_val_2324_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2331_ = v_val_2324_;
v_isShared_2332_ = v_isSharedCheck_2390_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_snd_2328_);
lean_inc(v_fst_2329_);
lean_dec(v_val_2324_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2390_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v_fst_2333_; lean_object* v_snd_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2389_; 
v_fst_2333_ = lean_ctor_get(v_snd_2328_, 0);
v_snd_2334_ = lean_ctor_get(v_snd_2328_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_snd_2328_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2336_ = v_snd_2328_;
v_isShared_2337_ = v_isSharedCheck_2389_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_snd_2334_);
lean_inc(v_fst_2333_);
lean_dec(v_snd_2328_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2389_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v_lvl_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; 
v_lvl_2338_ = lean_ctor_get(v_fst_2329_, 0);
lean_inc(v_lvl_2338_);
v___x_2339_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2329_);
lean_inc(v_fst_2333_);
v___x_2340_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2333_);
v___x_2341_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2338_, v___x_2339_, v___x_2340_);
v___x_2342_ = lean_unsigned_to_nat(2u);
v___x_2343_ = lean_mk_empty_array_with_capacity(v___x_2342_);
v___x_2344_ = lean_array_push(v___x_2343_, v_xs_2306_);
lean_inc_ref(v_letMuts_2309_);
v___x_2345_ = lean_array_push(v___x_2344_, v_letMuts_2309_);
v___x_2346_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2341_);
v___x_2347_ = 0;
v___x_2348_ = 1;
v___x_2349_ = l_Lean_Meta_mkLambdaFVars(v___x_2345_, v___x_2346_, v___x_2347_, v___x_2307_, v___x_2347_, v___x_2307_, v___x_2348_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec_ref(v___x_2345_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v_letMutsPred_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v_letMutsPred_2351_ = lean_ctor_get(v_fst_2333_, 2);
lean_inc_ref(v_letMutsPred_2351_);
lean_dec(v_fst_2333_);
v___x_2352_ = lean_mk_empty_array_with_capacity(v___x_2308_);
v___x_2353_ = lean_array_push(v___x_2352_, v_letMuts_2309_);
v___x_2354_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2351_);
v___x_2355_ = l_Lean_Meta_mkLambdaFVars(v___x_2353_, v___x_2354_, v___x_2347_, v___x_2307_, v___x_2347_, v___x_2307_, v___x_2348_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec_ref(v___x_2353_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2372_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2372_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2372_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v_a_2356_);
v___x_2361_ = v___x_2336_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2356_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_snd_2334_);
v___x_2361_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2361_);
lean_ctor_set(v___x_2331_, 0, v_a_2350_);
v___x_2363_ = v___x_2331_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2350_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2363_);
v___x_2365_ = v___x_2326_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2365_);
v___x_2367_ = v___x_2358_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_a_2350_);
lean_del_object(v___x_2336_);
lean_dec(v_snd_2334_);
lean_del_object(v___x_2331_);
lean_del_object(v___x_2326_);
v_a_2373_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2355_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2355_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_del_object(v___x_2336_);
lean_dec(v_snd_2334_);
lean_dec(v_fst_2333_);
lean_del_object(v___x_2331_);
lean_del_object(v___x_2326_);
lean_dec_ref(v_letMuts_2309_);
v_a_2381_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2349_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2349_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
lean_dec(v_a_2320_);
lean_dec_ref(v_letMuts_2309_);
lean_dec_ref(v_xs_2306_);
v___x_2392_ = lean_box(0);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2392_);
v___x_2394_ = v___x_2322_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_letMuts_2309_);
lean_dec_ref(v_xs_2306_);
v_a_2397_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2319_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2319_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2405_, lean_object* v_inv_2406_, lean_object* v_xs_2407_, lean_object* v___x_2408_, lean_object* v___x_2409_, lean_object* v_letMuts_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
uint8_t v___x_77955__boxed_2420_; lean_object* v_res_2421_; 
v___x_77955__boxed_2420_ = lean_unbox(v___x_2408_);
v_res_2421_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2405_, v_inv_2406_, v_xs_2407_, v___x_77955__boxed_2420_, v___x_2409_, v_letMuts_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___x_2409_);
lean_dec_ref(v_a_2405_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v_b_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2430_);
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2428_);
lean_inc(v___y_2426_);
lean_inc_ref(v___y_2425_);
lean_inc(v___y_2424_);
lean_inc_ref(v___y_2423_);
v___x_2433_ = lean_apply_10(v_k_2422_, v_b_2427_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, lean_box(0));
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v_b_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2446_, uint8_t v_bi_2447_, lean_object* v_type_2448_, lean_object* v_k_2449_, uint8_t v_kind_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___f_2460_; lean_object* v___x_2461_; 
lean_inc(v___y_2454_);
lean_inc_ref(v___y_2453_);
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2451_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2460_, 0, v_k_2449_);
lean_closure_set(v___f_2460_, 1, v___y_2451_);
lean_closure_set(v___f_2460_, 2, v___y_2452_);
lean_closure_set(v___f_2460_, 3, v___y_2453_);
lean_closure_set(v___f_2460_, 4, v___y_2454_);
v___x_2461_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2446_, v_bi_2447_, v_type_2448_, v___f_2460_, v_kind_2450_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2461_) == 0)
{
return v___x_2461_;
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2470_, lean_object* v_bi_2471_, lean_object* v_type_2472_, lean_object* v_k_2473_, lean_object* v_kind_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
uint8_t v_bi_boxed_2484_; uint8_t v_kind_boxed_2485_; lean_object* v_res_2486_; 
v_bi_boxed_2484_ = lean_unbox(v_bi_2471_);
v_kind_boxed_2485_ = lean_unbox(v_kind_2474_);
v_res_2486_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2470_, v_bi_boxed_2484_, v_type_2472_, v_k_2473_, v_kind_boxed_2485_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2487_, lean_object* v_type_2488_, lean_object* v_k_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
uint8_t v___x_2499_; uint8_t v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = 0;
v___x_2500_ = 0;
v___x_2501_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2487_, v___x_2499_, v_type_2488_, v_k_2489_, v___x_2500_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2502_, lean_object* v_type_2503_, lean_object* v_k_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2502_, v_type_2503_, v_k_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2518_, lean_object* v_inv_2519_, uint8_t v___x_2520_, lean_object* v___x_2521_, lean_object* v_arg_2522_, lean_object* v_xs_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_box(v___x_2520_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2534_, 0, v_a_2518_);
lean_closure_set(v___f_2534_, 1, v_inv_2519_);
lean_closure_set(v___f_2534_, 2, v_xs_2523_);
lean_closure_set(v___f_2534_, 3, v___x_2533_);
lean_closure_set(v___f_2534_, 4, v___x_2521_);
v___x_2535_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2536_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2535_, v_arg_2522_, v___f_2534_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2537_, lean_object* v_inv_2538_, lean_object* v___x_2539_, lean_object* v___x_2540_, lean_object* v_arg_2541_, lean_object* v_xs_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
uint8_t v___x_78275__boxed_2552_; lean_object* v_res_2553_; 
v___x_78275__boxed_2552_ = lean_unbox(v___x_2539_);
v_res_2553_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2537_, v_inv_2538_, v___x_78275__boxed_2552_, v___x_2540_, v_arg_2541_, v_xs_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
return v_res_2553_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2557_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = lean_unsigned_to_nat(32u);
v___x_2561_ = lean_mk_empty_array_with_capacity(v___x_2560_);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2563_, lean_object* v_xs_2564_, lean_object* v_fst_2565_, lean_object* v_r_2566_, lean_object* v___x_2567_, lean_object* v_fst_2568_, uint8_t v___x_2569_, lean_object* v___x_2570_, lean_object* v_letMuts_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
lean_inc_ref(v_fst_2563_);
v___x_2581_ = l_Lean_Meta_mkNone(v_fst_2563_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_2584_ = lean_unsigned_to_nat(2u);
v___x_2585_ = lean_mk_empty_array_with_capacity(v___x_2584_);
lean_inc_ref(v___x_2585_);
v___x_2586_ = lean_array_push(v___x_2585_, v_a_2582_);
lean_inc_ref(v_letMuts_2571_);
v___x_2587_ = lean_array_push(v___x_2586_, v_letMuts_2571_);
v___x_2588_ = l_Lean_Meta_mkAppM(v___x_2583_, v___x_2587_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
lean_inc_ref(v___x_2585_);
v___x_2590_ = lean_array_push(v___x_2585_, v_xs_2564_);
v___x_2591_ = lean_array_push(v___x_2590_, v_a_2589_);
v___x_2592_ = l_Lean_Expr_beta(v_fst_2565_, v___x_2591_);
v___x_2593_ = l_Lean_Meta_mkSome(v_fst_2563_, v_r_2566_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = lean_array_push(v___x_2585_, v_a_2594_);
v___x_2596_ = lean_array_push(v___x_2595_, v_letMuts_2571_);
v___x_2597_ = l_Lean_Meta_mkAppM(v___x_2583_, v___x_2596_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = lean_mk_empty_array_with_capacity(v___x_2567_);
lean_inc_ref(v___x_2599_);
v___x_2600_ = lean_array_push(v___x_2599_, v_a_2598_);
v___x_2601_ = l_Lean_Expr_beta(v_fst_2568_, v___x_2600_);
v___x_2602_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2579_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2604_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v___x_2604_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2579_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; uint8_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = lean_unsigned_to_nat(100000u);
v___x_2607_ = 0;
v___x_2608_ = 0;
v___x_2609_ = lean_box(0);
v___x_2610_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2610_, 0, v___x_2606_);
lean_ctor_set(v___x_2610_, 1, v___x_2584_);
lean_ctor_set(v___x_2610_, 2, v___x_2609_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 1, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 2, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 3, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 4, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 5, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 6, v___x_2608_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 7, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 8, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 9, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 10, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 11, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 12, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 13, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 14, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 15, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 16, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 17, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 18, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 19, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 20, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 21, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 22, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 23, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 24, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 25, v___x_2569_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 26, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 27, v___x_2607_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*3 + 28, v___x_2607_);
v___x_2611_ = lean_array_push(v___x_2599_, v_a_2603_);
v___x_2612_ = l_Lean_Options_empty;
v___x_2613_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2610_, v___x_2611_, v_a_2605_, v___x_2612_, v___y_2576_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v___x_2615_ = lean_mk_empty_array_with_capacity(v___x_2570_);
v___x_2616_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2617_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2615_, v___x_2616_, v___x_2607_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc_n(v_a_2618_, 2);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2619_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2570_, 2);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2570_);
v___x_2621_ = lean_unsigned_to_nat(32u);
v___x_2622_ = lean_mk_empty_array_with_capacity(v___x_2621_);
v___x_2623_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2624_ = ((size_t)5ULL);
v___x_2625_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2622_);
lean_ctor_set(v___x_2625_, 2, v___x_2570_);
lean_ctor_set(v___x_2625_, 3, v___x_2570_);
lean_ctor_set_usize(v___x_2625_, 4, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2619_);
lean_ctor_set(v___x_2626_, 1, v___x_2619_);
lean_ctor_set(v___x_2626_, 2, v___x_2619_);
lean_ctor_set(v___x_2626_, 3, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2620_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
lean_inc(v_a_2614_);
v___x_2628_ = l_Lean_Meta_simp(v___x_2592_, v_a_2614_, v_a_2618_, v___x_2609_, v___x_2627_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v_fst_2630_; lean_object* v___x_2631_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v_fst_2630_ = lean_ctor_get(v_a_2629_, 0);
lean_inc(v_fst_2630_);
lean_dec(v_a_2629_);
v___x_2631_ = l_Lean_Meta_simp(v___x_2601_, v_a_2614_, v_a_2618_, v___x_2609_, v___x_2627_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec_ref_known(v___x_2627_, 2);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v_fst_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2670_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v_fst_2633_ = lean_ctor_get(v_a_2632_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_a_2632_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v_a_2632_, 1);
lean_dec(v_unused_2671_);
v___x_2635_ = v_a_2632_;
v_isShared_2636_ = v_isSharedCheck_2670_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_fst_2633_);
lean_dec(v_a_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2670_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v_expr_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_expr_2637_ = lean_ctor_get(v_fst_2630_, 0);
lean_inc_ref(v_expr_2637_);
lean_dec(v_fst_2630_);
v___x_2638_ = lean_box(1);
v___x_2639_ = l_Lean_PrettyPrinter_delab(v_expr_2637_, v___x_2638_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v_expr_2641_; lean_object* v___x_2642_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v_expr_2641_ = lean_ctor_get(v_fst_2633_, 0);
lean_inc_ref(v_expr_2641_);
lean_dec(v_fst_2633_);
v___x_2642_ = l_Lean_PrettyPrinter_delab(v_expr_2641_, v___x_2638_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2653_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2653_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2653_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v_a_2643_);
lean_ctor_set(v___x_2635_, 0, v_a_2640_);
v___x_2648_ = v___x_2635_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2640_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2650_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2648_);
v___x_2650_ = v___x_2645_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_a_2640_);
lean_del_object(v___x_2635_);
v_a_2654_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2642_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2642_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_del_object(v___x_2635_);
lean_dec(v_fst_2633_);
v_a_2662_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2639_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2639_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v_fst_2630_);
v_a_2672_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2631_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2631_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref_known(v___x_2627_, 2);
lean_dec(v_a_2618_);
lean_dec(v_a_2614_);
lean_dec_ref(v___x_2601_);
v_a_2680_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2628_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2628_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_a_2614_);
lean_dec_ref(v___x_2601_);
lean_dec_ref(v___x_2592_);
lean_dec(v___x_2570_);
v_a_2688_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2617_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2617_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v___x_2601_);
lean_dec_ref(v___x_2592_);
lean_dec(v___x_2570_);
v_a_2696_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2613_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2613_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_a_2603_);
lean_dec_ref(v___x_2601_);
lean_dec_ref(v___x_2599_);
lean_dec_ref(v___x_2592_);
lean_dec(v___x_2570_);
v_a_2704_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2604_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2604_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v___x_2601_);
lean_dec_ref(v___x_2599_);
lean_dec_ref(v___x_2592_);
lean_dec(v___x_2570_);
v_a_2712_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2602_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2602_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v___x_2592_);
lean_dec(v___x_2570_);
lean_dec_ref(v_fst_2568_);
v_a_2720_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2597_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2597_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v___x_2592_);
lean_dec_ref(v___x_2585_);
lean_dec_ref(v_letMuts_2571_);
lean_dec(v___x_2570_);
lean_dec_ref(v_fst_2568_);
v_a_2728_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2593_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2593_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec_ref(v___x_2585_);
lean_dec_ref(v_letMuts_2571_);
lean_dec(v___x_2570_);
lean_dec_ref(v_fst_2568_);
lean_dec_ref(v_r_2566_);
lean_dec_ref(v_fst_2565_);
lean_dec_ref(v_xs_2564_);
lean_dec_ref(v_fst_2563_);
v_a_2736_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2588_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2588_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v_letMuts_2571_);
lean_dec(v___x_2570_);
lean_dec_ref(v_fst_2568_);
lean_dec_ref(v_r_2566_);
lean_dec_ref(v_fst_2565_);
lean_dec_ref(v_xs_2564_);
lean_dec_ref(v_fst_2563_);
v_a_2744_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2581_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2581_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_2752_ = _args[0];
lean_object* v_xs_2753_ = _args[1];
lean_object* v_fst_2754_ = _args[2];
lean_object* v_r_2755_ = _args[3];
lean_object* v___x_2756_ = _args[4];
lean_object* v_fst_2757_ = _args[5];
lean_object* v___x_2758_ = _args[6];
lean_object* v___x_2759_ = _args[7];
lean_object* v_letMuts_2760_ = _args[8];
lean_object* v___y_2761_ = _args[9];
lean_object* v___y_2762_ = _args[10];
lean_object* v___y_2763_ = _args[11];
lean_object* v___y_2764_ = _args[12];
lean_object* v___y_2765_ = _args[13];
lean_object* v___y_2766_ = _args[14];
lean_object* v___y_2767_ = _args[15];
lean_object* v___y_2768_ = _args[16];
lean_object* v___y_2769_ = _args[17];
_start:
{
uint8_t v___x_78351__boxed_2770_; lean_object* v_res_2771_; 
v___x_78351__boxed_2770_ = lean_unbox(v___x_2758_);
v_res_2771_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_2752_, v_xs_2753_, v_fst_2754_, v_r_2755_, v___x_2756_, v_fst_2757_, v___x_78351__boxed_2770_, v___x_2759_, v_letMuts_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___x_2756_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_2772_, lean_object* v_xs_2773_, lean_object* v_fst_2774_, lean_object* v___x_2775_, lean_object* v_fst_2776_, uint8_t v___x_2777_, lean_object* v___x_2778_, lean_object* v_snd_2779_, lean_object* v_r_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; lean_object* v___f_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2790_ = lean_box(v___x_2777_);
v___f_2791_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_2791_, 0, v_fst_2772_);
lean_closure_set(v___f_2791_, 1, v_xs_2773_);
lean_closure_set(v___f_2791_, 2, v_fst_2774_);
lean_closure_set(v___f_2791_, 3, v_r_2780_);
lean_closure_set(v___f_2791_, 4, v___x_2775_);
lean_closure_set(v___f_2791_, 5, v_fst_2776_);
lean_closure_set(v___f_2791_, 6, v___x_2790_);
lean_closure_set(v___f_2791_, 7, v___x_2778_);
v___x_2792_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2793_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2792_, v_snd_2779_, v___f_2791_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_2794_ = _args[0];
lean_object* v_xs_2795_ = _args[1];
lean_object* v_fst_2796_ = _args[2];
lean_object* v___x_2797_ = _args[3];
lean_object* v_fst_2798_ = _args[4];
lean_object* v___x_2799_ = _args[5];
lean_object* v___x_2800_ = _args[6];
lean_object* v_snd_2801_ = _args[7];
lean_object* v_r_2802_ = _args[8];
lean_object* v___y_2803_ = _args[9];
lean_object* v___y_2804_ = _args[10];
lean_object* v___y_2805_ = _args[11];
lean_object* v___y_2806_ = _args[12];
lean_object* v___y_2807_ = _args[13];
lean_object* v___y_2808_ = _args[14];
lean_object* v___y_2809_ = _args[15];
lean_object* v___y_2810_ = _args[16];
lean_object* v___y_2811_ = _args[17];
_start:
{
uint8_t v___x_78747__boxed_2812_; lean_object* v_res_2813_; 
v___x_78747__boxed_2812_ = lean_unbox(v___x_2799_);
v_res_2813_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_2794_, v_xs_2795_, v_fst_2796_, v___x_2797_, v_fst_2798_, v___x_78747__boxed_2812_, v___x_2800_, v_snd_2801_, v_r_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_2817_, lean_object* v_fst_2818_, lean_object* v___x_2819_, lean_object* v_fst_2820_, uint8_t v___x_2821_, lean_object* v___x_2822_, lean_object* v_snd_2823_, lean_object* v_xs_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2834_ = lean_box(v___x_2821_);
lean_inc_ref(v_fst_2817_);
v___f_2835_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_2835_, 0, v_fst_2817_);
lean_closure_set(v___f_2835_, 1, v_xs_2824_);
lean_closure_set(v___f_2835_, 2, v_fst_2818_);
lean_closure_set(v___f_2835_, 3, v___x_2819_);
lean_closure_set(v___f_2835_, 4, v_fst_2820_);
lean_closure_set(v___f_2835_, 5, v___x_2834_);
lean_closure_set(v___f_2835_, 6, v___x_2822_);
lean_closure_set(v___f_2835_, 7, v_snd_2823_);
v___x_2836_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_2837_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2836_, v_fst_2817_, v___f_2835_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_2838_ = _args[0];
lean_object* v_fst_2839_ = _args[1];
lean_object* v___x_2840_ = _args[2];
lean_object* v_fst_2841_ = _args[3];
lean_object* v___x_2842_ = _args[4];
lean_object* v___x_2843_ = _args[5];
lean_object* v_snd_2844_ = _args[6];
lean_object* v_xs_2845_ = _args[7];
lean_object* v___y_2846_ = _args[8];
lean_object* v___y_2847_ = _args[9];
lean_object* v___y_2848_ = _args[10];
lean_object* v___y_2849_ = _args[11];
lean_object* v___y_2850_ = _args[12];
lean_object* v___y_2851_ = _args[13];
lean_object* v___y_2852_ = _args[14];
lean_object* v___y_2853_ = _args[15];
lean_object* v___y_2854_ = _args[16];
_start:
{
uint8_t v___x_78810__boxed_2855_; lean_object* v_res_2856_; 
v___x_78810__boxed_2855_ = lean_unbox(v___x_2842_);
v_res_2856_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_2838_, v_fst_2839_, v___x_2840_, v_fst_2841_, v___x_78810__boxed_2855_, v___x_2843_, v_snd_2844_, v_xs_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_2857_, size_t v_sz_2858_, size_t v_i_2859_, lean_object* v_b_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = lean_usize_dec_lt(v_i_2859_, v_sz_2858_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_b_2860_);
return v___x_2867_;
}
else
{
lean_object* v___x_2868_; lean_object* v_a_2869_; lean_object* v___x_2870_; 
v___x_2868_ = lean_box(1);
v_a_2869_ = lean_array_uget_borrowed(v_as_2857_, v_i_2859_);
lean_inc(v_a_2869_);
v___x_2870_ = l_Lean_PrettyPrinter_delab(v_a_2869_, v___x_2868_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2872_; size_t v___x_2873_; size_t v___x_2874_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
v___x_2872_ = lean_array_push(v_b_2860_, v_a_2871_);
v___x_2873_ = ((size_t)1ULL);
v___x_2874_ = lean_usize_add(v_i_2859_, v___x_2873_);
v_i_2859_ = v___x_2874_;
v_b_2860_ = v___x_2872_;
goto _start;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v_b_2860_);
v_a_2876_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2870_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2870_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_2884_, lean_object* v_sz_2885_, lean_object* v_i_2886_, lean_object* v_b_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
size_t v_sz_boxed_2893_; size_t v_i_boxed_2894_; lean_object* v_res_2895_; 
v_sz_boxed_2893_ = lean_unbox_usize(v_sz_2885_);
lean_dec(v_sz_2885_);
v_i_boxed_2894_ = lean_unbox_usize(v_i_2886_);
lean_dec(v_i_2886_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_2884_, v_sz_boxed_2893_, v_i_boxed_2894_, v_b_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v_as_2884_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_2916_, lean_object* v_fst_2917_, lean_object* v_snd_2918_, lean_object* v___x_2919_, lean_object* v___x_2920_, lean_object* v___x_2921_, lean_object* v___x_2922_, lean_object* v___x_2923_, lean_object* v___x_2924_, lean_object* v___x_2925_, lean_object* v___x_2926_, lean_object* v_letMuts_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2937_ = lean_unsigned_to_nat(2u);
v___x_2938_ = lean_mk_empty_array_with_capacity(v___x_2937_);
v___x_2939_ = lean_array_push(v___x_2938_, v_xs_2916_);
v___x_2940_ = lean_array_push(v___x_2939_, v_letMuts_2927_);
v___x_2941_ = l_Lean_Expr_beta(v_fst_2917_, v___x_2940_);
v___x_2942_ = lean_box(1);
v___x_2943_ = l_Lean_PrettyPrinter_delab(v___x_2941_, v___x_2942_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3083_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_3083_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3083_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v_points_2948_; lean_object* v_default_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3082_; 
v_points_2948_ = lean_ctor_get(v_snd_2918_, 0);
v_default_2949_ = lean_ctor_get(v_snd_2918_, 1);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_snd_2918_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_2951_ = v_snd_2918_;
v_isShared_2952_ = v_isSharedCheck_3082_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_default_2949_);
lean_inc(v_points_2948_);
lean_dec(v_snd_2918_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3082_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
uint8_t v___y_2954_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = lean_array_get_size(v_points_2948_);
v___x_3006_ = lean_nat_dec_eq(v___x_3005_, v___x_2924_);
if (v___x_3006_ == 0)
{
lean_del_object(v___x_2946_);
lean_dec_ref(v___x_2926_);
lean_dec_ref(v___x_2925_);
v___y_2954_ = v___x_3006_;
goto v___jp_2953_;
}
else
{
if (lean_obj_tag(v_default_2949_) == 3)
{
uint8_t v___x_3007_; 
lean_del_object(v___x_2946_);
lean_dec_ref(v___x_2926_);
lean_dec_ref(v___x_2925_);
v___x_3007_ = 0;
v___y_2954_ = v___x_3007_;
goto v___jp_2953_;
}
else
{
lean_del_object(v___x_2951_);
lean_dec_ref(v_points_2948_);
if (lean_obj_tag(v_default_2949_) == 2)
{
lean_object* v_toCold_3008_; lean_object* v_ref_3009_; lean_object* v_quotContext_3010_; lean_object* v_currMacroScope_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v_toCold_3008_ = lean_ctor_get(v___y_2934_, 0);
v_ref_3009_ = lean_ctor_get(v___y_2934_, 2);
v_quotContext_3010_ = lean_ctor_get(v_toCold_3008_, 8);
v_currMacroScope_3011_ = lean_ctor_get(v_toCold_3008_, 9);
v___x_3012_ = 0;
v___x_3013_ = l_Lean_SourceInfo_fromRef(v_ref_3009_, v___x_3012_);
v___x_3014_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3015_ = l_Lean_Name_mkStr3(v___x_2925_, v___x_2926_, v___x_3014_);
v___x_3016_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7));
v___x_3017_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3013_, 11);
v___x_3018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3013_);
lean_ctor_set(v___x_3018_, 1, v___x_3016_);
lean_ctor_set(v___x_3018_, 2, v___x_3017_);
v___x_3019_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3013_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3013_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_String_toRawSubstring_x27(v___x_2919_);
lean_inc_n(v_currMacroScope_3011_, 2);
lean_inc_n(v_quotContext_3010_, 2);
v___x_3026_ = l_Lean_addMacroScope(v_quotContext_3010_, v___x_2920_, v_currMacroScope_3011_);
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3013_);
lean_ctor_set(v___x_3028_, 1, v___x_3025_);
lean_ctor_set(v___x_3028_, 2, v___x_3026_);
lean_ctor_set(v___x_3028_, 3, v___x_3027_);
v___x_3029_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3013_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = l_String_toRawSubstring_x27(v___x_2921_);
v___x_3032_ = l_Lean_addMacroScope(v_quotContext_3010_, v___x_2922_, v_currMacroScope_3011_);
v___x_3033_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3013_);
lean_ctor_set(v___x_3033_, 1, v___x_3031_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
lean_ctor_set(v___x_3033_, 3, v___x_3027_);
v___x_3034_ = l_Lean_Syntax_node3(v___x_3013_, v___x_3021_, v___x_3028_, v___x_3030_, v___x_3033_);
v___x_3035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3013_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = l_Lean_Syntax_node3(v___x_3013_, v___x_3022_, v___x_3024_, v___x_3034_, v___x_3036_);
v___x_3038_ = l_Lean_Syntax_node1(v___x_3013_, v___x_3021_, v___x_3037_);
v___x_3039_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3013_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = l_Lean_Syntax_node5(v___x_3013_, v___x_3015_, v___x_3018_, v___x_3020_, v___x_3038_, v___x_3040_, v_a_2944_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_3041_);
v___x_3043_ = v___x_2946_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
lean_object* v_toCold_3045_; lean_object* v_ref_3046_; lean_object* v_quotContext_3047_; lean_object* v_currMacroScope_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
lean_dec(v_default_2949_);
v_toCold_3045_ = lean_ctor_get(v___y_2934_, 0);
v_ref_3046_ = lean_ctor_get(v___y_2934_, 2);
v_quotContext_3047_ = lean_ctor_get(v_toCold_3045_, 8);
v_currMacroScope_3048_ = lean_ctor_get(v_toCold_3045_, 9);
v___x_3049_ = 0;
v___x_3050_ = l_Lean_SourceInfo_fromRef(v_ref_3046_, v___x_3049_);
v___x_3051_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3052_ = l_Lean_Name_mkStr3(v___x_2925_, v___x_2926_, v___x_3051_);
v___x_3053_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7));
v___x_3054_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3050_, 11);
v___x_3055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3050_);
lean_ctor_set(v___x_3055_, 1, v___x_3053_);
lean_ctor_set(v___x_3055_, 2, v___x_3054_);
v___x_3056_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3050_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3050_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = l_String_toRawSubstring_x27(v___x_2919_);
lean_inc_n(v_currMacroScope_3048_, 2);
lean_inc_n(v_quotContext_3047_, 2);
v___x_3063_ = l_Lean_addMacroScope(v_quotContext_3047_, v___x_2920_, v_currMacroScope_3048_);
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3050_);
lean_ctor_set(v___x_3065_, 1, v___x_3062_);
lean_ctor_set(v___x_3065_, 2, v___x_3063_);
lean_ctor_set(v___x_3065_, 3, v___x_3064_);
v___x_3066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3050_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_String_toRawSubstring_x27(v___x_2921_);
v___x_3069_ = l_Lean_addMacroScope(v_quotContext_3047_, v___x_2922_, v_currMacroScope_3048_);
v___x_3070_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3050_);
lean_ctor_set(v___x_3070_, 1, v___x_3068_);
lean_ctor_set(v___x_3070_, 2, v___x_3069_);
lean_ctor_set(v___x_3070_, 3, v___x_3064_);
v___x_3071_ = l_Lean_Syntax_node3(v___x_3050_, v___x_3058_, v___x_3065_, v___x_3067_, v___x_3070_);
v___x_3072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3050_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = l_Lean_Syntax_node3(v___x_3050_, v___x_3059_, v___x_3061_, v___x_3071_, v___x_3073_);
v___x_3075_ = l_Lean_Syntax_node1(v___x_3050_, v___x_3058_, v___x_3074_);
v___x_3076_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3050_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_Syntax_node5(v___x_3050_, v___x_3052_, v___x_3055_, v___x_3057_, v___x_3075_, v___x_3077_, v_a_2944_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_3078_);
v___x_3080_ = v___x_2946_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
v___jp_2953_:
{
lean_object* v_toCold_2955_; lean_object* v_ref_2956_; lean_object* v_quotContext_2957_; lean_object* v_currMacroScope_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v_toCold_2955_ = lean_ctor_get(v___y_2934_, 0);
v_ref_2956_ = lean_ctor_get(v___y_2934_, 2);
v_quotContext_2957_ = lean_ctor_get(v_toCold_2955_, 8);
v_currMacroScope_2958_ = lean_ctor_get(v_toCold_2955_, 9);
v___x_2959_ = l_Lean_SourceInfo_fromRef(v_ref_2956_, v___y_2954_);
v___x_2960_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_2961_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc(v___x_2959_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 2);
lean_ctor_set(v___x_2951_, 1, v___x_2960_);
lean_ctor_set(v___x_2951_, 0, v___x_2959_);
v___x_2963_ = v___x_2951_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v___x_2960_);
v___x_2963_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; size_t v_sz_2991_; size_t v___x_2992_; lean_object* v___x_2993_; 
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_2965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2967_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_2959_, 11);
v___x_2968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2959_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = l_String_toRawSubstring_x27(v___x_2919_);
lean_inc_n(v_currMacroScope_2958_, 2);
lean_inc_n(v_quotContext_2957_, 2);
v___x_2970_ = l_Lean_addMacroScope(v_quotContext_2957_, v___x_2920_, v_currMacroScope_2958_);
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2959_);
lean_ctor_set(v___x_2972_, 1, v___x_2969_);
lean_ctor_set(v___x_2972_, 2, v___x_2970_);
lean_ctor_set(v___x_2972_, 3, v___x_2971_);
v___x_2973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_2974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2959_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = l_String_toRawSubstring_x27(v___x_2921_);
v___x_2976_ = l_Lean_addMacroScope(v_quotContext_2957_, v___x_2922_, v_currMacroScope_2958_);
v___x_2977_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2959_);
lean_ctor_set(v___x_2977_, 1, v___x_2975_);
lean_ctor_set(v___x_2977_, 2, v___x_2976_);
lean_ctor_set(v___x_2977_, 3, v___x_2971_);
v___x_2978_ = l_Lean_Syntax_node3(v___x_2959_, v___x_2965_, v___x_2972_, v___x_2974_, v___x_2977_);
v___x_2979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2959_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = l_Lean_Syntax_node3(v___x_2959_, v___x_2966_, v___x_2968_, v___x_2978_, v___x_2980_);
v___x_2982_ = l_Lean_Syntax_node1(v___x_2959_, v___x_2965_, v___x_2981_);
v___x_2983_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2959_);
lean_ctor_set(v___x_2984_, 1, v___x_2965_);
lean_ctor_set(v___x_2984_, 2, v___x_2983_);
v___x_2985_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_2986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2959_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = l_Lean_Syntax_node4(v___x_2959_, v___x_2964_, v___x_2982_, v___x_2984_, v___x_2986_, v_a_2944_);
v___x_2988_ = l_Lean_Syntax_node2(v___x_2959_, v___x_2961_, v___x_2963_, v___x_2987_);
v___x_2989_ = lean_mk_empty_array_with_capacity(v___x_2923_);
v___x_2990_ = lean_array_push(v___x_2989_, v___x_2988_);
v_sz_2991_ = lean_array_size(v_points_2948_);
v___x_2992_ = ((size_t)0ULL);
v___x_2993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_2948_, v_sz_2991_, v___x_2992_, v___x_2990_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec_ref(v_points_2948_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_2994_, v_default_2949_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v_a_2994_);
return v___x_2995_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_default_2949_);
v_a_2996_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2993_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2993_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2926_);
lean_dec_ref(v___x_2925_);
lean_dec(v___x_2922_);
lean_dec_ref(v___x_2921_);
lean_dec(v___x_2920_);
lean_dec_ref(v___x_2919_);
lean_dec_ref(v_snd_2918_);
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3084_ = _args[0];
lean_object* v_fst_3085_ = _args[1];
lean_object* v_snd_3086_ = _args[2];
lean_object* v___x_3087_ = _args[3];
lean_object* v___x_3088_ = _args[4];
lean_object* v___x_3089_ = _args[5];
lean_object* v___x_3090_ = _args[6];
lean_object* v___x_3091_ = _args[7];
lean_object* v___x_3092_ = _args[8];
lean_object* v___x_3093_ = _args[9];
lean_object* v___x_3094_ = _args[10];
lean_object* v_letMuts_3095_ = _args[11];
lean_object* v___y_3096_ = _args[12];
lean_object* v___y_3097_ = _args[13];
lean_object* v___y_3098_ = _args[14];
lean_object* v___y_3099_ = _args[15];
lean_object* v___y_3100_ = _args[16];
lean_object* v___y_3101_ = _args[17];
lean_object* v___y_3102_ = _args[18];
lean_object* v___y_3103_ = _args[19];
lean_object* v___y_3104_ = _args[20];
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3084_, v_fst_3085_, v_snd_3086_, v___x_3087_, v___x_3088_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v___x_3094_, v_letMuts_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___x_3092_);
lean_dec(v___x_3091_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3106_, lean_object* v_snd_3107_, lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v___x_3111_, lean_object* v___x_3112_, lean_object* v___x_3113_, lean_object* v_arg_3114_, lean_object* v_xs_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___f_3127_; lean_object* v___x_3128_; 
v___x_3125_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3126_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___f_3127_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 21, 11);
lean_closure_set(v___f_3127_, 0, v_xs_3115_);
lean_closure_set(v___f_3127_, 1, v_fst_3106_);
lean_closure_set(v___f_3127_, 2, v_snd_3107_);
lean_closure_set(v___f_3127_, 3, v___x_3108_);
lean_closure_set(v___f_3127_, 4, v___x_3109_);
lean_closure_set(v___f_3127_, 5, v___x_3125_);
lean_closure_set(v___f_3127_, 6, v___x_3126_);
lean_closure_set(v___f_3127_, 7, v___x_3110_);
lean_closure_set(v___f_3127_, 8, v___x_3111_);
lean_closure_set(v___f_3127_, 9, v___x_3112_);
lean_closure_set(v___f_3127_, 10, v___x_3113_);
v___x_3128_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3126_, v_arg_3114_, v___f_3127_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3129_ = _args[0];
lean_object* v_snd_3130_ = _args[1];
lean_object* v___x_3131_ = _args[2];
lean_object* v___x_3132_ = _args[3];
lean_object* v___x_3133_ = _args[4];
lean_object* v___x_3134_ = _args[5];
lean_object* v___x_3135_ = _args[6];
lean_object* v___x_3136_ = _args[7];
lean_object* v_arg_3137_ = _args[8];
lean_object* v_xs_3138_ = _args[9];
lean_object* v___y_3139_ = _args[10];
lean_object* v___y_3140_ = _args[11];
lean_object* v___y_3141_ = _args[12];
lean_object* v___y_3142_ = _args[13];
lean_object* v___y_3143_ = _args[14];
lean_object* v___y_3144_ = _args[15];
lean_object* v___y_3145_ = _args[16];
lean_object* v___y_3146_ = _args[17];
lean_object* v___y_3147_ = _args[18];
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3129_, v_snd_3130_, v___x_3131_, v___x_3132_, v___x_3133_, v___x_3134_, v___x_3135_, v___x_3136_, v_arg_3137_, v_xs_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3149_, size_t v_sz_3150_, size_t v_i_3151_, lean_object* v_b_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_usize_dec_lt(v_i_3151_, v_sz_3150_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_b_3152_);
return v___x_3159_;
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_a_3160_ = lean_array_uget_borrowed(v_as_3149_, v_i_3151_);
v___x_3161_ = lean_box(1);
lean_inc(v_a_3160_);
v___x_3162_ = l_Lean_PrettyPrinter_delab(v_a_3160_, v___x_3161_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = lean_array_push(v_b_3152_, v_a_3163_);
v___x_3165_ = ((size_t)1ULL);
v___x_3166_ = lean_usize_add(v_i_3151_, v___x_3165_);
v_i_3151_ = v___x_3166_;
v_b_3152_ = v___x_3164_;
goto _start;
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v_b_3152_);
v_a_3168_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3162_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3162_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3176_, lean_object* v_sz_3177_, lean_object* v_i_3178_, lean_object* v_b_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
size_t v_sz_boxed_3185_; size_t v_i_boxed_3186_; lean_object* v_res_3187_; 
v_sz_boxed_3185_ = lean_unbox_usize(v_sz_3177_);
lean_dec(v_sz_3177_);
v_i_boxed_3186_ = lean_unbox_usize(v_i_3178_);
lean_dec(v_i_3178_);
v_res_3187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3176_, v_sz_boxed_3185_, v_i_boxed_3186_, v_b_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec_ref(v_as_3176_);
return v_res_3187_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3196_ = l_String_toRawSubstring_x27(v___x_3195_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3207_ = l_String_toRawSubstring_x27(v___x_3206_);
return v___x_3207_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3212_ = l_String_toRawSubstring_x27(v___x_3211_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3214_ = l_String_toRawSubstring_x27(v___x_3213_);
return v___x_3214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3218_ = l_String_toRawSubstring_x27(v___x_3217_);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3223_ = l_String_toRawSubstring_x27(v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3233_, lean_object* v___x_3234_, lean_object* v___f_3235_, lean_object* v_a_3236_, lean_object* v_inv_3237_, lean_object* v_arg_3238_, lean_object* v___x_3239_, uint8_t v___x_3240_, lean_object* v___x_3241_, lean_object* v___x_3242_, lean_object* v___x_3243_, lean_object* v___x_3244_, lean_object* v___x_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_a_3256_; lean_object* v___x_3259_; 
lean_inc_ref(v___x_3234_);
lean_inc(v___x_3233_);
v___x_3259_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3233_, v___x_3234_, v___f_3235_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v___x_3261_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3236_, v_inv_3237_, v_arg_3238_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3261_, 1);
if (lean_obj_tag(v_a_3262_) == 1)
{
lean_object* v_val_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v_arg_3238_);
v_val_3263_ = lean_ctor_get(v_a_3262_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_a_3262_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3265_ = v_a_3262_;
v_isShared_3266_ = v_isSharedCheck_3748_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_val_3263_);
lean_dec(v_a_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3748_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
if (lean_obj_tag(v_a_3260_) == 1)
{
lean_object* v_val_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3670_; 
lean_del_object(v___x_3265_);
v_val_3267_ = lean_ctor_get(v_a_3260_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_a_3260_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3269_ = v_a_3260_;
v_isShared_3270_ = v_isSharedCheck_3670_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_val_3267_);
lean_dec(v_a_3260_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3670_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v_snd_3271_; lean_object* v_fst_3272_; lean_object* v_snd_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3669_; 
v_snd_3271_ = lean_ctor_get(v_val_3267_, 1);
lean_inc(v_snd_3271_);
v_fst_3272_ = lean_ctor_get(v_val_3263_, 0);
v_snd_3273_ = lean_ctor_get(v_val_3263_, 1);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_val_3263_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3275_ = v_val_3263_;
v_isShared_3276_ = v_isSharedCheck_3669_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_snd_3273_);
lean_inc(v_fst_3272_);
lean_dec(v_val_3263_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3669_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v_fst_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3667_; 
v_fst_3277_ = lean_ctor_get(v_val_3267_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_val_3267_);
if (v_isSharedCheck_3667_ == 0)
{
lean_object* v_unused_3668_; 
v_unused_3668_ = lean_ctor_get(v_val_3267_, 1);
lean_dec(v_unused_3668_);
v___x_3279_ = v_val_3267_;
v_isShared_3280_ = v_isSharedCheck_3667_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_fst_3277_);
lean_dec(v_val_3267_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3667_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v_fst_3281_; lean_object* v_snd_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3666_; 
v_fst_3281_ = lean_ctor_get(v_snd_3271_, 0);
v_snd_3282_ = lean_ctor_get(v_snd_3271_, 1);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_snd_3271_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3284_ = v_snd_3271_;
v_isShared_3285_ = v_isSharedCheck_3666_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_snd_3282_);
lean_inc(v_fst_3281_);
lean_dec(v_snd_3271_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3666_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___f_3287_; lean_object* v___x_3288_; 
v___x_3286_ = lean_box(v___x_3240_);
lean_inc(v___x_3241_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3287_, 0, v_fst_3272_);
lean_closure_set(v___f_3287_, 1, v_fst_3277_);
lean_closure_set(v___f_3287_, 2, v___x_3239_);
lean_closure_set(v___f_3287_, 3, v_fst_3281_);
lean_closure_set(v___f_3287_, 4, v___x_3286_);
lean_closure_set(v___f_3287_, 5, v___x_3241_);
lean_closure_set(v___f_3287_, 6, v_snd_3273_);
lean_inc(v___x_3233_);
v___x_3288_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3233_, v___x_3234_, v___f_3287_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v_fst_3290_; lean_object* v_snd_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3657_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3288_, 1);
v_fst_3290_ = lean_ctor_get(v_a_3289_, 0);
v_snd_3291_ = lean_ctor_get(v_a_3289_, 1);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_a_3289_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3293_ = v_a_3289_;
v_isShared_3294_ = v_isSharedCheck_3657_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_snd_3291_);
lean_inc(v_fst_3290_);
lean_dec(v_a_3289_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3657_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v_points_3295_; lean_object* v_default_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3656_; 
v_points_3295_ = lean_ctor_get(v_snd_3282_, 0);
v_default_3296_ = lean_ctor_get(v_snd_3282_, 1);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_snd_3282_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3298_ = v_snd_3282_;
v_isShared_3299_ = v_isSharedCheck_3656_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_default_3296_);
lean_inc(v_points_3295_);
lean_dec(v_snd_3282_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3656_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; uint8_t v___x_3301_; 
v___x_3300_ = lean_array_get_size(v_points_3295_);
v___x_3301_ = lean_nat_dec_eq(v___x_3300_, v___x_3241_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; size_t v_sz_3303_; size_t v___x_3304_; lean_object* v___x_3305_; 
lean_del_object(v___x_3269_);
v___x_3302_ = lean_mk_empty_array_with_capacity(v___x_3241_);
lean_dec(v___x_3241_);
v_sz_3303_ = lean_array_size(v_points_3295_);
v___x_3304_ = ((size_t)0ULL);
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3295_, v_sz_3303_, v___x_3304_, v___x_3302_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec_ref(v_points_3295_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3306_, v_default_3296_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v_a_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_toCold_3308_; lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3391_; 
v_toCold_3308_ = lean_ctor_get(v___y_3252_, 0);
lean_inc_ref(v_toCold_3308_);
v_a_3309_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3311_ = v___x_3307_;
v_isShared_3312_ = v_isSharedCheck_3391_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3307_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3391_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v_ref_3313_; lean_object* v_quotContext_3314_; lean_object* v_currMacroScope_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3325_; 
v_ref_3313_ = lean_ctor_get(v___y_3252_, 2);
lean_inc(v_ref_3313_);
lean_dec_ref(v___y_3252_);
v_quotContext_3314_ = lean_ctor_get(v_toCold_3308_, 8);
lean_inc_n(v_quotContext_3314_, 2);
v_currMacroScope_3315_ = lean_ctor_get(v_toCold_3308_, 9);
lean_inc_n(v_currMacroScope_3315_, 2);
lean_dec_ref(v_toCold_3308_);
v___x_3316_ = l_Lean_SourceInfo_fromRef(v_ref_3313_, v___x_3301_);
lean_dec(v_ref_3313_);
v___x_3317_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3318_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3319_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3242_);
v___x_3320_ = l_Lean_Name_mkStr2(v___x_3242_, v___x_3319_);
v___x_3321_ = l_Lean_addMacroScope(v_quotContext_3314_, v___x_3320_, v_currMacroScope_3315_);
v___x_3322_ = l_Lean_Name_mkStr4(v___x_3243_, v___x_3244_, v___x_3242_, v___x_3319_);
v___x_3323_ = lean_box(0);
lean_inc(v___x_3322_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set_tag(v___x_3298_, 1);
lean_ctor_set(v___x_3298_, 1, v___x_3323_);
lean_ctor_set(v___x_3298_, 0, v___x_3322_);
v___x_3325_ = v___x_3298_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3327_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3322_);
v___x_3327_ = v___x_3311_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3322_);
v___x_3327_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3329_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 1);
lean_ctor_set(v___x_3293_, 1, v___x_3323_);
lean_ctor_set(v___x_3293_, 0, v___x_3327_);
v___x_3329_ = v___x_3293_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v___x_3323_);
v___x_3329_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
lean_object* v___x_3331_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 1);
lean_ctor_set(v___x_3284_, 1, v___x_3329_);
lean_ctor_set(v___x_3284_, 0, v___x_3325_);
v___x_3331_ = v___x_3284_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
lean_inc_n(v___x_3316_, 2);
v___x_3332_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3316_);
lean_ctor_set(v___x_3332_, 1, v___x_3318_);
lean_ctor_set(v___x_3332_, 2, v___x_3321_);
lean_ctor_set(v___x_3332_, 3, v___x_3331_);
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3334_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3335_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3280_ == 0)
{
lean_ctor_set_tag(v___x_3279_, 2);
lean_ctor_set(v___x_3279_, 1, v___x_3335_);
lean_ctor_set(v___x_3279_, 0, v___x_3316_);
v___x_3337_ = v___x_3279_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3338_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3339_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3315_);
lean_inc(v_quotContext_3314_);
v___x_3340_ = l_Lean_addMacroScope(v_quotContext_3314_, v___x_3339_, v_currMacroScope_3315_);
lean_inc_n(v___x_3316_, 2);
v___x_3341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3316_);
lean_ctor_set(v___x_3341_, 1, v___x_3338_);
lean_ctor_set(v___x_3341_, 2, v___x_3340_);
lean_ctor_set(v___x_3341_, 3, v___x_3323_);
v___x_3342_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 2);
lean_ctor_set(v___x_3275_, 1, v___x_3342_);
lean_ctor_set(v___x_3275_, 0, v___x_3316_);
v___x_3344_ = v___x_3275_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3345_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3346_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc_n(v___x_3316_, 19);
v___x_3347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3316_);
lean_ctor_set(v___x_3347_, 1, v___x_3345_);
v___x_3348_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3349_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3350_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3315_, 4);
lean_inc_n(v_quotContext_3314_, 4);
v___x_3351_ = l_Lean_addMacroScope(v_quotContext_3314_, v___x_3350_, v_currMacroScope_3315_);
v___x_3352_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3316_);
lean_ctor_set(v___x_3352_, 1, v___x_3349_);
lean_ctor_set(v___x_3352_, 2, v___x_3351_);
lean_ctor_set(v___x_3352_, 3, v___x_3323_);
v___x_3353_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3354_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3355_ = l_Lean_addMacroScope(v_quotContext_3314_, v___x_3354_, v_currMacroScope_3315_);
v___x_3356_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3316_);
lean_ctor_set(v___x_3356_, 1, v___x_3353_);
lean_ctor_set(v___x_3356_, 2, v___x_3355_);
lean_ctor_set(v___x_3356_, 3, v___x_3323_);
lean_inc_ref(v___x_3356_);
v___x_3357_ = l_Lean_Syntax_node2(v___x_3316_, v___x_3333_, v___x_3352_, v___x_3356_);
v___x_3358_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3316_);
lean_ctor_set(v___x_3359_, 1, v___x_3333_);
lean_ctor_set(v___x_3359_, 2, v___x_3358_);
v___x_3360_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3316_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
lean_inc_ref(v___x_3361_);
lean_inc_ref(v___x_3359_);
v___x_3362_ = l_Lean_Syntax_node4(v___x_3316_, v___x_3348_, v___x_3357_, v___x_3359_, v___x_3361_, v_snd_3291_);
lean_inc_ref(v___x_3347_);
v___x_3363_ = l_Lean_Syntax_node2(v___x_3316_, v___x_3346_, v___x_3347_, v___x_3362_);
v___x_3364_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3316_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
lean_inc_ref_n(v___x_3365_, 2);
lean_inc_ref_n(v___x_3344_, 2);
lean_inc_ref_n(v___x_3337_, 2);
v___x_3366_ = l_Lean_Syntax_node5(v___x_3316_, v___x_3334_, v___x_3337_, v___x_3341_, v___x_3344_, v___x_3363_, v___x_3365_);
v___x_3367_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3368_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3369_ = l_Lean_addMacroScope(v_quotContext_3314_, v___x_3368_, v_currMacroScope_3315_);
v___x_3370_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3316_);
lean_ctor_set(v___x_3370_, 1, v___x_3367_);
lean_ctor_set(v___x_3370_, 2, v___x_3369_);
lean_ctor_set(v___x_3370_, 3, v___x_3323_);
v___x_3371_ = l_String_toRawSubstring_x27(v___x_3245_);
v___x_3372_ = l_Lean_addMacroScope(v_quotContext_3314_, v___x_3233_, v_currMacroScope_3315_);
v___x_3373_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3316_);
lean_ctor_set(v___x_3373_, 1, v___x_3371_);
lean_ctor_set(v___x_3373_, 2, v___x_3372_);
lean_ctor_set(v___x_3373_, 3, v___x_3323_);
v___x_3374_ = l_Lean_Syntax_node2(v___x_3316_, v___x_3333_, v___x_3373_, v___x_3356_);
v___x_3375_ = l_Lean_Syntax_node4(v___x_3316_, v___x_3348_, v___x_3374_, v___x_3359_, v___x_3361_, v_fst_3290_);
v___x_3376_ = l_Lean_Syntax_node2(v___x_3316_, v___x_3346_, v___x_3347_, v___x_3375_);
v___x_3377_ = l_Lean_Syntax_node5(v___x_3316_, v___x_3334_, v___x_3337_, v___x_3370_, v___x_3344_, v___x_3376_, v___x_3365_);
v___x_3378_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3379_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3380_ = l_Lean_addMacroScope(v_quotContext_3314_, v___x_3379_, v_currMacroScope_3315_);
v___x_3381_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3316_);
lean_ctor_set(v___x_3381_, 1, v___x_3378_);
lean_ctor_set(v___x_3381_, 2, v___x_3380_);
lean_ctor_set(v___x_3381_, 3, v___x_3323_);
v___x_3382_ = l_Lean_Syntax_node5(v___x_3316_, v___x_3334_, v___x_3337_, v___x_3381_, v___x_3344_, v_a_3309_, v___x_3365_);
v___x_3383_ = l_Lean_Syntax_node3(v___x_3316_, v___x_3333_, v___x_3366_, v___x_3377_, v___x_3382_);
v___x_3384_ = l_Lean_Syntax_node2(v___x_3316_, v___x_3317_, v___x_3332_, v___x_3383_);
v_a_3256_ = v___x_3384_;
goto v___jp_3255_;
}
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3298_);
lean_del_object(v___x_3293_);
lean_dec(v_snd_3291_);
lean_dec(v_fst_3290_);
lean_del_object(v___x_3284_);
lean_del_object(v___x_3279_);
lean_del_object(v___x_3275_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3243_);
lean_dec_ref(v___x_3242_);
lean_dec(v___x_3233_);
return v___x_3307_;
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_del_object(v___x_3298_);
lean_dec(v_default_3296_);
lean_del_object(v___x_3293_);
lean_dec(v_snd_3291_);
lean_dec(v_fst_3290_);
lean_del_object(v___x_3284_);
lean_del_object(v___x_3279_);
lean_del_object(v___x_3275_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3243_);
lean_dec_ref(v___x_3242_);
lean_dec(v___x_3233_);
v_a_3392_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3305_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3305_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_dec_ref(v_points_3295_);
lean_dec(v___x_3241_);
switch(lean_obj_tag(v_default_3296_))
{
case 2:
{
lean_object* v_toCold_3400_; lean_object* v_ref_3401_; lean_object* v_quotContext_3402_; lean_object* v_currMacroScope_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v_toCold_3400_ = lean_ctor_get(v___y_3252_, 0);
lean_inc_ref(v_toCold_3400_);
v_ref_3401_ = lean_ctor_get(v___y_3252_, 2);
lean_inc(v_ref_3401_);
lean_dec_ref(v___y_3252_);
v_quotContext_3402_ = lean_ctor_get(v_toCold_3400_, 8);
lean_inc_n(v_quotContext_3402_, 2);
v_currMacroScope_3403_ = lean_ctor_get(v_toCold_3400_, 9);
lean_inc_n(v_currMacroScope_3403_, 2);
lean_dec_ref(v_toCold_3400_);
v___x_3404_ = 0;
v___x_3405_ = l_Lean_SourceInfo_fromRef(v_ref_3401_, v___x_3404_);
lean_dec(v_ref_3401_);
v___x_3406_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3407_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3408_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3242_);
v___x_3409_ = l_Lean_Name_mkStr2(v___x_3242_, v___x_3408_);
v___x_3410_ = l_Lean_addMacroScope(v_quotContext_3402_, v___x_3409_, v_currMacroScope_3403_);
lean_inc_ref(v___x_3244_);
lean_inc_ref(v___x_3243_);
v___x_3411_ = l_Lean_Name_mkStr4(v___x_3243_, v___x_3244_, v___x_3242_, v___x_3408_);
v___x_3412_ = lean_box(0);
lean_inc(v___x_3411_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set_tag(v___x_3298_, 1);
lean_ctor_set(v___x_3298_, 1, v___x_3412_);
lean_ctor_set(v___x_3298_, 0, v___x_3411_);
v___x_3414_ = v___x_3298_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3416_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set_tag(v___x_3269_, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3411_);
v___x_3416_ = v___x_3269_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3411_);
v___x_3416_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3418_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 1);
lean_ctor_set(v___x_3293_, 1, v___x_3412_);
lean_ctor_set(v___x_3293_, 0, v___x_3416_);
v___x_3418_ = v___x_3293_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___x_3412_);
v___x_3418_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 1);
lean_ctor_set(v___x_3284_, 1, v___x_3418_);
lean_ctor_set(v___x_3284_, 0, v___x_3414_);
v___x_3420_ = v___x_3284_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
lean_inc_n(v___x_3405_, 2);
v___x_3421_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3405_);
lean_ctor_set(v___x_3421_, 1, v___x_3407_);
lean_ctor_set(v___x_3421_, 2, v___x_3410_);
lean_ctor_set(v___x_3421_, 3, v___x_3420_);
v___x_3422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3423_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3424_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3280_ == 0)
{
lean_ctor_set_tag(v___x_3279_, 2);
lean_ctor_set(v___x_3279_, 1, v___x_3424_);
lean_ctor_set(v___x_3279_, 0, v___x_3405_);
v___x_3426_ = v___x_3279_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3427_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3428_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3403_);
lean_inc(v_quotContext_3402_);
v___x_3429_ = l_Lean_addMacroScope(v_quotContext_3402_, v___x_3428_, v_currMacroScope_3403_);
lean_inc_n(v___x_3405_, 2);
v___x_3430_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3405_);
lean_ctor_set(v___x_3430_, 1, v___x_3427_);
lean_ctor_set(v___x_3430_, 2, v___x_3429_);
lean_ctor_set(v___x_3430_, 3, v___x_3412_);
v___x_3431_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 2);
lean_ctor_set(v___x_3275_, 1, v___x_3431_);
lean_ctor_set(v___x_3275_, 0, v___x_3405_);
v___x_3433_ = v___x_3275_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3434_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3435_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc_n(v___x_3405_, 22);
v___x_3436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3405_);
lean_ctor_set(v___x_3436_, 1, v___x_3434_);
v___x_3437_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3438_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3439_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3403_, 5);
lean_inc_n(v_quotContext_3402_, 5);
v___x_3440_ = l_Lean_addMacroScope(v_quotContext_3402_, v___x_3439_, v_currMacroScope_3403_);
v___x_3441_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3405_);
lean_ctor_set(v___x_3441_, 1, v___x_3438_);
lean_ctor_set(v___x_3441_, 2, v___x_3440_);
lean_ctor_set(v___x_3441_, 3, v___x_3412_);
v___x_3442_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3443_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3444_ = l_Lean_addMacroScope(v_quotContext_3402_, v___x_3443_, v_currMacroScope_3403_);
v___x_3445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3405_);
lean_ctor_set(v___x_3445_, 1, v___x_3442_);
lean_ctor_set(v___x_3445_, 2, v___x_3444_);
lean_ctor_set(v___x_3445_, 3, v___x_3412_);
lean_inc_ref(v___x_3445_);
v___x_3446_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3422_, v___x_3441_, v___x_3445_);
v___x_3447_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3405_);
lean_ctor_set(v___x_3448_, 1, v___x_3422_);
lean_ctor_set(v___x_3448_, 2, v___x_3447_);
v___x_3449_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3405_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
lean_inc_ref(v___x_3450_);
lean_inc_ref(v___x_3448_);
v___x_3451_ = l_Lean_Syntax_node4(v___x_3405_, v___x_3437_, v___x_3446_, v___x_3448_, v___x_3450_, v_snd_3291_);
lean_inc_ref(v___x_3436_);
v___x_3452_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3435_, v___x_3436_, v___x_3451_);
v___x_3453_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3405_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
lean_inc_ref_n(v___x_3454_, 2);
lean_inc_ref_n(v___x_3433_, 2);
lean_inc_ref_n(v___x_3426_, 2);
v___x_3455_ = l_Lean_Syntax_node5(v___x_3405_, v___x_3423_, v___x_3426_, v___x_3430_, v___x_3433_, v___x_3452_, v___x_3454_);
v___x_3456_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3457_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3458_ = l_Lean_addMacroScope(v_quotContext_3402_, v___x_3457_, v_currMacroScope_3403_);
v___x_3459_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3405_);
lean_ctor_set(v___x_3459_, 1, v___x_3456_);
lean_ctor_set(v___x_3459_, 2, v___x_3458_);
lean_ctor_set(v___x_3459_, 3, v___x_3412_);
v___x_3460_ = l_String_toRawSubstring_x27(v___x_3245_);
v___x_3461_ = l_Lean_addMacroScope(v_quotContext_3402_, v___x_3233_, v_currMacroScope_3403_);
v___x_3462_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3405_);
lean_ctor_set(v___x_3462_, 1, v___x_3460_);
lean_ctor_set(v___x_3462_, 2, v___x_3461_);
lean_ctor_set(v___x_3462_, 3, v___x_3412_);
v___x_3463_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3422_, v___x_3462_, v___x_3445_);
v___x_3464_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3465_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3466_ = l_Lean_addMacroScope(v_quotContext_3402_, v___x_3465_, v_currMacroScope_3403_);
v___x_3467_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3405_);
lean_ctor_set(v___x_3467_, 1, v___x_3464_);
lean_ctor_set(v___x_3467_, 2, v___x_3466_);
lean_ctor_set(v___x_3467_, 3, v___x_3412_);
v___x_3468_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29);
v___x_3469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0));
v___x_3470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7));
v___x_3471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30));
v___x_3472_ = l_Lean_addMacroScope(v_quotContext_3402_, v___x_3471_, v_currMacroScope_3403_);
v___x_3473_ = l_Lean_Name_mkStr4(v___x_3243_, v___x_3244_, v___x_3469_, v___x_3470_);
v___x_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3412_);
v___x_3475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___x_3412_);
v___x_3476_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3405_);
lean_ctor_set(v___x_3476_, 1, v___x_3468_);
lean_ctor_set(v___x_3476_, 2, v___x_3472_);
lean_ctor_set(v___x_3476_, 3, v___x_3475_);
v___x_3477_ = l_Lean_Syntax_node5(v___x_3405_, v___x_3423_, v___x_3426_, v___x_3467_, v___x_3433_, v___x_3476_, v___x_3454_);
v___x_3478_ = l_Lean_Syntax_node1(v___x_3405_, v___x_3422_, v___x_3477_);
v___x_3479_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3406_, v_fst_3290_, v___x_3478_);
v___x_3480_ = l_Lean_Syntax_node4(v___x_3405_, v___x_3437_, v___x_3463_, v___x_3448_, v___x_3450_, v___x_3479_);
v___x_3481_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3435_, v___x_3436_, v___x_3480_);
v___x_3482_ = l_Lean_Syntax_node5(v___x_3405_, v___x_3423_, v___x_3426_, v___x_3459_, v___x_3433_, v___x_3481_, v___x_3454_);
v___x_3483_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3422_, v___x_3455_, v___x_3482_);
v___x_3484_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3406_, v___x_3421_, v___x_3483_);
v_a_3256_ = v___x_3484_;
goto v___jp_3255_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_del_object(v___x_3269_);
v_e_3491_ = lean_ctor_get(v_default_3296_, 0);
lean_inc_ref(v_e_3491_);
lean_dec_ref_known(v_default_3296_, 1);
v___x_3492_ = lean_box(1);
v___x_3493_ = l_Lean_PrettyPrinter_delab(v_e_3491_, v___x_3492_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_toCold_3494_; lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3580_; 
v_toCold_3494_ = lean_ctor_get(v___y_3252_, 0);
lean_inc_ref(v_toCold_3494_);
v_a_3495_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3497_ = v___x_3493_;
v_isShared_3498_ = v_isSharedCheck_3580_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3493_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3580_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v_ref_3499_; lean_object* v_quotContext_3500_; lean_object* v_currMacroScope_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3512_; 
v_ref_3499_ = lean_ctor_get(v___y_3252_, 2);
lean_inc(v_ref_3499_);
lean_dec_ref(v___y_3252_);
v_quotContext_3500_ = lean_ctor_get(v_toCold_3494_, 8);
lean_inc_n(v_quotContext_3500_, 2);
v_currMacroScope_3501_ = lean_ctor_get(v_toCold_3494_, 9);
lean_inc_n(v_currMacroScope_3501_, 2);
lean_dec_ref(v_toCold_3494_);
v___x_3502_ = 0;
v___x_3503_ = l_Lean_SourceInfo_fromRef(v_ref_3499_, v___x_3502_);
lean_dec(v_ref_3499_);
v___x_3504_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3505_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3506_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3242_);
v___x_3507_ = l_Lean_Name_mkStr2(v___x_3242_, v___x_3506_);
v___x_3508_ = l_Lean_addMacroScope(v_quotContext_3500_, v___x_3507_, v_currMacroScope_3501_);
v___x_3509_ = l_Lean_Name_mkStr4(v___x_3243_, v___x_3244_, v___x_3242_, v___x_3506_);
v___x_3510_ = lean_box(0);
lean_inc(v___x_3509_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set_tag(v___x_3298_, 1);
lean_ctor_set(v___x_3298_, 1, v___x_3510_);
lean_ctor_set(v___x_3298_, 0, v___x_3509_);
v___x_3512_ = v___x_3298_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3514_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3509_);
v___x_3514_ = v___x_3497_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3509_);
v___x_3514_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3516_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 1);
lean_ctor_set(v___x_3293_, 1, v___x_3510_);
lean_ctor_set(v___x_3293_, 0, v___x_3514_);
v___x_3516_ = v___x_3293_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3510_);
v___x_3516_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
lean_object* v___x_3518_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 1);
lean_ctor_set(v___x_3284_, 1, v___x_3516_);
lean_ctor_set(v___x_3284_, 0, v___x_3512_);
v___x_3518_ = v___x_3284_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
lean_inc_n(v___x_3503_, 2);
v___x_3519_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3503_);
lean_ctor_set(v___x_3519_, 1, v___x_3505_);
lean_ctor_set(v___x_3519_, 2, v___x_3508_);
lean_ctor_set(v___x_3519_, 3, v___x_3518_);
v___x_3520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3521_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3522_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3280_ == 0)
{
lean_ctor_set_tag(v___x_3279_, 2);
lean_ctor_set(v___x_3279_, 1, v___x_3522_);
lean_ctor_set(v___x_3279_, 0, v___x_3503_);
v___x_3524_ = v___x_3279_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3525_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3526_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3501_);
lean_inc(v_quotContext_3500_);
v___x_3527_ = l_Lean_addMacroScope(v_quotContext_3500_, v___x_3526_, v_currMacroScope_3501_);
lean_inc_n(v___x_3503_, 2);
v___x_3528_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3503_);
lean_ctor_set(v___x_3528_, 1, v___x_3525_);
lean_ctor_set(v___x_3528_, 2, v___x_3527_);
lean_ctor_set(v___x_3528_, 3, v___x_3510_);
v___x_3529_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 2);
lean_ctor_set(v___x_3275_, 1, v___x_3529_);
lean_ctor_set(v___x_3275_, 0, v___x_3503_);
v___x_3531_ = v___x_3275_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3532_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3533_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc_n(v___x_3503_, 21);
v___x_3534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3503_);
lean_ctor_set(v___x_3534_, 1, v___x_3532_);
v___x_3535_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3536_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3537_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3501_, 4);
lean_inc_n(v_quotContext_3500_, 4);
v___x_3538_ = l_Lean_addMacroScope(v_quotContext_3500_, v___x_3537_, v_currMacroScope_3501_);
v___x_3539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3503_);
lean_ctor_set(v___x_3539_, 1, v___x_3536_);
lean_ctor_set(v___x_3539_, 2, v___x_3538_);
lean_ctor_set(v___x_3539_, 3, v___x_3510_);
v___x_3540_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3542_ = l_Lean_addMacroScope(v_quotContext_3500_, v___x_3541_, v_currMacroScope_3501_);
v___x_3543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3503_);
lean_ctor_set(v___x_3543_, 1, v___x_3540_);
lean_ctor_set(v___x_3543_, 2, v___x_3542_);
lean_ctor_set(v___x_3543_, 3, v___x_3510_);
lean_inc_ref(v___x_3543_);
v___x_3544_ = l_Lean_Syntax_node2(v___x_3503_, v___x_3520_, v___x_3539_, v___x_3543_);
v___x_3545_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3503_);
lean_ctor_set(v___x_3546_, 1, v___x_3520_);
lean_ctor_set(v___x_3546_, 2, v___x_3545_);
v___x_3547_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3503_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
lean_inc_ref(v___x_3548_);
lean_inc_ref(v___x_3546_);
v___x_3549_ = l_Lean_Syntax_node4(v___x_3503_, v___x_3535_, v___x_3544_, v___x_3546_, v___x_3548_, v_snd_3291_);
lean_inc_ref(v___x_3534_);
v___x_3550_ = l_Lean_Syntax_node2(v___x_3503_, v___x_3533_, v___x_3534_, v___x_3549_);
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3503_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
lean_inc_ref_n(v___x_3552_, 2);
lean_inc_ref_n(v___x_3531_, 2);
lean_inc_ref_n(v___x_3524_, 2);
v___x_3553_ = l_Lean_Syntax_node5(v___x_3503_, v___x_3521_, v___x_3524_, v___x_3528_, v___x_3531_, v___x_3550_, v___x_3552_);
v___x_3554_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3555_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3556_ = l_Lean_addMacroScope(v_quotContext_3500_, v___x_3555_, v_currMacroScope_3501_);
v___x_3557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3503_);
lean_ctor_set(v___x_3557_, 1, v___x_3554_);
lean_ctor_set(v___x_3557_, 2, v___x_3556_);
lean_ctor_set(v___x_3557_, 3, v___x_3510_);
v___x_3558_ = l_String_toRawSubstring_x27(v___x_3245_);
v___x_3559_ = l_Lean_addMacroScope(v_quotContext_3500_, v___x_3233_, v_currMacroScope_3501_);
v___x_3560_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3503_);
lean_ctor_set(v___x_3560_, 1, v___x_3558_);
lean_ctor_set(v___x_3560_, 2, v___x_3559_);
lean_ctor_set(v___x_3560_, 3, v___x_3510_);
v___x_3561_ = l_Lean_Syntax_node2(v___x_3503_, v___x_3520_, v___x_3560_, v___x_3543_);
v___x_3562_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3563_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3564_ = l_Lean_addMacroScope(v_quotContext_3500_, v___x_3563_, v_currMacroScope_3501_);
v___x_3565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3503_);
lean_ctor_set(v___x_3565_, 1, v___x_3562_);
lean_ctor_set(v___x_3565_, 2, v___x_3564_);
lean_ctor_set(v___x_3565_, 3, v___x_3510_);
v___x_3566_ = l_Lean_Syntax_node5(v___x_3503_, v___x_3521_, v___x_3524_, v___x_3565_, v___x_3531_, v_a_3495_, v___x_3552_);
v___x_3567_ = l_Lean_Syntax_node1(v___x_3503_, v___x_3520_, v___x_3566_);
v___x_3568_ = l_Lean_Syntax_node2(v___x_3503_, v___x_3504_, v_fst_3290_, v___x_3567_);
v___x_3569_ = l_Lean_Syntax_node4(v___x_3503_, v___x_3535_, v___x_3561_, v___x_3546_, v___x_3548_, v___x_3568_);
v___x_3570_ = l_Lean_Syntax_node2(v___x_3503_, v___x_3533_, v___x_3534_, v___x_3569_);
v___x_3571_ = l_Lean_Syntax_node5(v___x_3503_, v___x_3521_, v___x_3524_, v___x_3557_, v___x_3531_, v___x_3570_, v___x_3552_);
v___x_3572_ = l_Lean_Syntax_node2(v___x_3503_, v___x_3520_, v___x_3553_, v___x_3571_);
v___x_3573_ = l_Lean_Syntax_node2(v___x_3503_, v___x_3504_, v___x_3519_, v___x_3572_);
v_a_3256_ = v___x_3573_;
goto v___jp_3255_;
}
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3298_);
lean_del_object(v___x_3293_);
lean_dec(v_snd_3291_);
lean_dec(v_fst_3290_);
lean_del_object(v___x_3284_);
lean_del_object(v___x_3279_);
lean_del_object(v___x_3275_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3243_);
lean_dec_ref(v___x_3242_);
lean_dec(v___x_3233_);
return v___x_3493_;
}
}
default: 
{
lean_object* v_toCold_3581_; lean_object* v_ref_3582_; lean_object* v_quotContext_3583_; lean_object* v_currMacroScope_3584_; uint8_t v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
lean_dec(v_default_3296_);
v_toCold_3581_ = lean_ctor_get(v___y_3252_, 0);
lean_inc_ref(v_toCold_3581_);
v_ref_3582_ = lean_ctor_get(v___y_3252_, 2);
lean_inc(v_ref_3582_);
lean_dec_ref(v___y_3252_);
v_quotContext_3583_ = lean_ctor_get(v_toCold_3581_, 8);
lean_inc_n(v_quotContext_3583_, 2);
v_currMacroScope_3584_ = lean_ctor_get(v_toCold_3581_, 9);
lean_inc_n(v_currMacroScope_3584_, 2);
lean_dec_ref(v_toCold_3581_);
v___x_3585_ = 0;
v___x_3586_ = l_Lean_SourceInfo_fromRef(v_ref_3582_, v___x_3585_);
lean_dec(v_ref_3582_);
v___x_3587_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3588_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3589_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3242_);
v___x_3590_ = l_Lean_Name_mkStr2(v___x_3242_, v___x_3589_);
v___x_3591_ = l_Lean_addMacroScope(v_quotContext_3583_, v___x_3590_, v_currMacroScope_3584_);
v___x_3592_ = l_Lean_Name_mkStr4(v___x_3243_, v___x_3244_, v___x_3242_, v___x_3589_);
v___x_3593_ = lean_box(0);
lean_inc(v___x_3592_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set_tag(v___x_3298_, 1);
lean_ctor_set(v___x_3298_, 1, v___x_3593_);
lean_ctor_set(v___x_3298_, 0, v___x_3592_);
v___x_3595_ = v___x_3298_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v___x_3593_);
v___x_3595_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set_tag(v___x_3269_, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3592_);
v___x_3597_ = v___x_3269_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3592_);
v___x_3597_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3599_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 1);
lean_ctor_set(v___x_3293_, 1, v___x_3593_);
lean_ctor_set(v___x_3293_, 0, v___x_3597_);
v___x_3599_ = v___x_3293_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_3593_);
v___x_3599_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3601_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 1);
lean_ctor_set(v___x_3284_, 1, v___x_3599_);
lean_ctor_set(v___x_3284_, 0, v___x_3595_);
v___x_3601_ = v___x_3284_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
lean_inc_n(v___x_3586_, 2);
v___x_3602_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3586_);
lean_ctor_set(v___x_3602_, 1, v___x_3588_);
lean_ctor_set(v___x_3602_, 2, v___x_3591_);
lean_ctor_set(v___x_3602_, 3, v___x_3601_);
v___x_3603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3604_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3605_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3280_ == 0)
{
lean_ctor_set_tag(v___x_3279_, 2);
lean_ctor_set(v___x_3279_, 1, v___x_3605_);
lean_ctor_set(v___x_3279_, 0, v___x_3586_);
v___x_3607_ = v___x_3279_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3608_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3609_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3584_);
lean_inc(v_quotContext_3583_);
v___x_3610_ = l_Lean_addMacroScope(v_quotContext_3583_, v___x_3609_, v_currMacroScope_3584_);
lean_inc_n(v___x_3586_, 2);
v___x_3611_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3586_);
lean_ctor_set(v___x_3611_, 1, v___x_3608_);
lean_ctor_set(v___x_3611_, 2, v___x_3610_);
lean_ctor_set(v___x_3611_, 3, v___x_3593_);
v___x_3612_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 2);
lean_ctor_set(v___x_3275_, 1, v___x_3612_);
lean_ctor_set(v___x_3275_, 0, v___x_3586_);
v___x_3614_ = v___x_3275_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3615_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3616_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
lean_inc_n(v___x_3586_, 17);
v___x_3617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3586_);
lean_ctor_set(v___x_3617_, 1, v___x_3615_);
v___x_3618_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3619_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3620_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3584_, 3);
lean_inc_n(v_quotContext_3583_, 3);
v___x_3621_ = l_Lean_addMacroScope(v_quotContext_3583_, v___x_3620_, v_currMacroScope_3584_);
v___x_3622_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3586_);
lean_ctor_set(v___x_3622_, 1, v___x_3619_);
lean_ctor_set(v___x_3622_, 2, v___x_3621_);
lean_ctor_set(v___x_3622_, 3, v___x_3593_);
v___x_3623_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3624_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3625_ = l_Lean_addMacroScope(v_quotContext_3583_, v___x_3624_, v_currMacroScope_3584_);
v___x_3626_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3586_);
lean_ctor_set(v___x_3626_, 1, v___x_3623_);
lean_ctor_set(v___x_3626_, 2, v___x_3625_);
lean_ctor_set(v___x_3626_, 3, v___x_3593_);
lean_inc_ref(v___x_3626_);
v___x_3627_ = l_Lean_Syntax_node2(v___x_3586_, v___x_3603_, v___x_3622_, v___x_3626_);
v___x_3628_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3586_);
lean_ctor_set(v___x_3629_, 1, v___x_3603_);
lean_ctor_set(v___x_3629_, 2, v___x_3628_);
v___x_3630_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3586_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
lean_inc_ref(v___x_3631_);
lean_inc_ref(v___x_3629_);
v___x_3632_ = l_Lean_Syntax_node4(v___x_3586_, v___x_3618_, v___x_3627_, v___x_3629_, v___x_3631_, v_snd_3291_);
lean_inc_ref(v___x_3617_);
v___x_3633_ = l_Lean_Syntax_node2(v___x_3586_, v___x_3616_, v___x_3617_, v___x_3632_);
v___x_3634_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3586_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
lean_inc_ref(v___x_3635_);
lean_inc_ref(v___x_3614_);
lean_inc_ref(v___x_3607_);
v___x_3636_ = l_Lean_Syntax_node5(v___x_3586_, v___x_3604_, v___x_3607_, v___x_3611_, v___x_3614_, v___x_3633_, v___x_3635_);
v___x_3637_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3638_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3639_ = l_Lean_addMacroScope(v_quotContext_3583_, v___x_3638_, v_currMacroScope_3584_);
v___x_3640_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3586_);
lean_ctor_set(v___x_3640_, 1, v___x_3637_);
lean_ctor_set(v___x_3640_, 2, v___x_3639_);
lean_ctor_set(v___x_3640_, 3, v___x_3593_);
v___x_3641_ = l_String_toRawSubstring_x27(v___x_3245_);
v___x_3642_ = l_Lean_addMacroScope(v_quotContext_3583_, v___x_3233_, v_currMacroScope_3584_);
v___x_3643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3586_);
lean_ctor_set(v___x_3643_, 1, v___x_3641_);
lean_ctor_set(v___x_3643_, 2, v___x_3642_);
lean_ctor_set(v___x_3643_, 3, v___x_3593_);
v___x_3644_ = l_Lean_Syntax_node2(v___x_3586_, v___x_3603_, v___x_3643_, v___x_3626_);
v___x_3645_ = l_Lean_Syntax_node4(v___x_3586_, v___x_3618_, v___x_3644_, v___x_3629_, v___x_3631_, v_fst_3290_);
v___x_3646_ = l_Lean_Syntax_node2(v___x_3586_, v___x_3616_, v___x_3617_, v___x_3645_);
v___x_3647_ = l_Lean_Syntax_node5(v___x_3586_, v___x_3604_, v___x_3607_, v___x_3640_, v___x_3614_, v___x_3646_, v___x_3635_);
v___x_3648_ = l_Lean_Syntax_node2(v___x_3586_, v___x_3603_, v___x_3636_, v___x_3647_);
v___x_3649_ = l_Lean_Syntax_node2(v___x_3586_, v___x_3587_, v___x_3602_, v___x_3648_);
v_a_3256_ = v___x_3649_;
goto v___jp_3255_;
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_del_object(v___x_3284_);
lean_dec(v_snd_3282_);
lean_del_object(v___x_3279_);
lean_del_object(v___x_3275_);
lean_del_object(v___x_3269_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3243_);
lean_dec_ref(v___x_3242_);
lean_dec(v___x_3241_);
lean_dec(v___x_3233_);
v_a_3658_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3288_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3288_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3260_);
lean_dec(v___x_3241_);
lean_dec(v___x_3239_);
lean_dec_ref(v___x_3234_);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_val_3263_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; lean_object* v_unused_3747_; 
v_unused_3746_ = lean_ctor_get(v_val_3263_, 1);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_val_3263_, 0);
lean_dec(v_unused_3747_);
v___x_3672_ = v_val_3263_;
v_isShared_3673_ = v_isSharedCheck_3745_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v_val_3263_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3745_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v_toCold_3674_; lean_object* v_ref_3675_; lean_object* v_quotContext_3676_; lean_object* v_currMacroScope_3677_; uint8_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
v_toCold_3674_ = lean_ctor_get(v___y_3252_, 0);
lean_inc_ref(v_toCold_3674_);
v_ref_3675_ = lean_ctor_get(v___y_3252_, 2);
lean_inc(v_ref_3675_);
lean_dec_ref(v___y_3252_);
v_quotContext_3676_ = lean_ctor_get(v_toCold_3674_, 8);
lean_inc_n(v_quotContext_3676_, 2);
v_currMacroScope_3677_ = lean_ctor_get(v_toCold_3674_, 9);
lean_inc_n(v_currMacroScope_3677_, 2);
lean_dec_ref(v_toCold_3674_);
v___x_3678_ = 0;
v___x_3679_ = l_Lean_SourceInfo_fromRef(v_ref_3675_, v___x_3678_);
lean_dec(v_ref_3675_);
v___x_3680_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3681_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3682_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3242_);
v___x_3683_ = l_Lean_Name_mkStr2(v___x_3242_, v___x_3682_);
v___x_3684_ = l_Lean_addMacroScope(v_quotContext_3676_, v___x_3683_, v_currMacroScope_3677_);
v___x_3685_ = l_Lean_Name_mkStr4(v___x_3243_, v___x_3244_, v___x_3242_, v___x_3682_);
v___x_3686_ = lean_box(0);
lean_inc(v___x_3685_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set_tag(v___x_3672_, 1);
lean_ctor_set(v___x_3672_, 1, v___x_3686_);
lean_ctor_set(v___x_3672_, 0, v___x_3685_);
v___x_3688_ = v___x_3672_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set_tag(v___x_3265_, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3685_);
v___x_3690_ = v___x_3265_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3685_);
v___x_3690_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v___x_3686_);
v___x_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3688_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
lean_inc_n(v___x_3679_, 23);
v___x_3693_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3679_);
lean_ctor_set(v___x_3693_, 1, v___x_3681_);
lean_ctor_set(v___x_3693_, 2, v___x_3684_);
lean_ctor_set(v___x_3693_, 3, v___x_3692_);
v___x_3694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3695_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_3697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3679_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_3677_, 4);
lean_inc_n(v_quotContext_3676_, 4);
v___x_3700_ = l_Lean_addMacroScope(v_quotContext_3676_, v___x_3699_, v_currMacroScope_3677_);
v___x_3701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3679_);
lean_ctor_set(v___x_3701_, 1, v___x_3698_);
lean_ctor_set(v___x_3701_, 2, v___x_3700_);
lean_ctor_set(v___x_3701_, 3, v___x_3686_);
v___x_3702_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_3703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3679_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3705_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1));
v___x_3706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3679_);
lean_ctor_set(v___x_3706_, 1, v___x_3704_);
v___x_3707_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3708_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3709_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3710_ = l_Lean_addMacroScope(v_quotContext_3676_, v___x_3709_, v_currMacroScope_3677_);
v___x_3711_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3679_);
lean_ctor_set(v___x_3711_, 1, v___x_3708_);
lean_ctor_set(v___x_3711_, 2, v___x_3710_);
lean_ctor_set(v___x_3711_, 3, v___x_3686_);
v___x_3712_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3713_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3714_ = l_Lean_addMacroScope(v_quotContext_3676_, v___x_3713_, v_currMacroScope_3677_);
v___x_3715_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3679_);
lean_ctor_set(v___x_3715_, 1, v___x_3712_);
lean_ctor_set(v___x_3715_, 2, v___x_3714_);
lean_ctor_set(v___x_3715_, 3, v___x_3686_);
lean_inc_ref(v___x_3715_);
v___x_3716_ = l_Lean_Syntax_node2(v___x_3679_, v___x_3694_, v___x_3711_, v___x_3715_);
v___x_3717_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3679_);
lean_ctor_set(v___x_3718_, 1, v___x_3694_);
lean_ctor_set(v___x_3718_, 2, v___x_3717_);
v___x_3719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3679_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_3722_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_3723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3679_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = l_Lean_Syntax_node1(v___x_3679_, v___x_3721_, v___x_3723_);
lean_inc(v___x_3724_);
lean_inc_ref(v___x_3720_);
lean_inc_ref(v___x_3718_);
v___x_3725_ = l_Lean_Syntax_node4(v___x_3679_, v___x_3707_, v___x_3716_, v___x_3718_, v___x_3720_, v___x_3724_);
lean_inc_ref(v___x_3706_);
v___x_3726_ = l_Lean_Syntax_node2(v___x_3679_, v___x_3705_, v___x_3706_, v___x_3725_);
v___x_3727_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3679_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
lean_inc_ref(v___x_3728_);
lean_inc_ref(v___x_3703_);
lean_inc_ref(v___x_3697_);
v___x_3729_ = l_Lean_Syntax_node5(v___x_3679_, v___x_3695_, v___x_3697_, v___x_3701_, v___x_3703_, v___x_3726_, v___x_3728_);
v___x_3730_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3731_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3732_ = l_Lean_addMacroScope(v_quotContext_3676_, v___x_3731_, v_currMacroScope_3677_);
v___x_3733_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3679_);
lean_ctor_set(v___x_3733_, 1, v___x_3730_);
lean_ctor_set(v___x_3733_, 2, v___x_3732_);
lean_ctor_set(v___x_3733_, 3, v___x_3686_);
v___x_3734_ = l_String_toRawSubstring_x27(v___x_3245_);
v___x_3735_ = l_Lean_addMacroScope(v_quotContext_3676_, v___x_3233_, v_currMacroScope_3677_);
v___x_3736_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3679_);
lean_ctor_set(v___x_3736_, 1, v___x_3734_);
lean_ctor_set(v___x_3736_, 2, v___x_3735_);
lean_ctor_set(v___x_3736_, 3, v___x_3686_);
v___x_3737_ = l_Lean_Syntax_node2(v___x_3679_, v___x_3694_, v___x_3736_, v___x_3715_);
v___x_3738_ = l_Lean_Syntax_node4(v___x_3679_, v___x_3707_, v___x_3737_, v___x_3718_, v___x_3720_, v___x_3724_);
v___x_3739_ = l_Lean_Syntax_node2(v___x_3679_, v___x_3705_, v___x_3706_, v___x_3738_);
v___x_3740_ = l_Lean_Syntax_node5(v___x_3679_, v___x_3695_, v___x_3697_, v___x_3733_, v___x_3703_, v___x_3739_, v___x_3728_);
v___x_3741_ = l_Lean_Syntax_node2(v___x_3679_, v___x_3694_, v___x_3729_, v___x_3740_);
v___x_3742_ = l_Lean_Syntax_node2(v___x_3679_, v___x_3680_, v___x_3693_, v___x_3741_);
v_a_3256_ = v___x_3742_;
goto v___jp_3255_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3262_);
lean_dec_ref(v___x_3242_);
if (lean_obj_tag(v_a_3260_) == 1)
{
lean_object* v_val_3749_; lean_object* v_snd_3750_; lean_object* v_fst_3751_; lean_object* v_snd_3752_; lean_object* v___f_3753_; lean_object* v___x_3754_; 
v_val_3749_ = lean_ctor_get(v_a_3260_, 0);
lean_inc(v_val_3749_);
lean_dec_ref_known(v_a_3260_, 1);
v_snd_3750_ = lean_ctor_get(v_val_3749_, 1);
lean_inc(v_snd_3750_);
v_fst_3751_ = lean_ctor_get(v_val_3749_, 0);
lean_inc(v_fst_3751_);
lean_dec(v_val_3749_);
v_snd_3752_ = lean_ctor_get(v_snd_3750_, 1);
lean_inc(v_snd_3752_);
lean_dec(v_snd_3750_);
lean_inc(v___x_3233_);
v___f_3753_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 19, 9);
lean_closure_set(v___f_3753_, 0, v_fst_3751_);
lean_closure_set(v___f_3753_, 1, v_snd_3752_);
lean_closure_set(v___f_3753_, 2, v___x_3245_);
lean_closure_set(v___f_3753_, 3, v___x_3233_);
lean_closure_set(v___f_3753_, 4, v___x_3239_);
lean_closure_set(v___f_3753_, 5, v___x_3241_);
lean_closure_set(v___f_3753_, 6, v___x_3243_);
lean_closure_set(v___f_3753_, 7, v___x_3244_);
lean_closure_set(v___f_3753_, 8, v_arg_3238_);
v___x_3754_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3233_, v___x_3234_, v___f_3753_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec_ref(v___y_3252_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v_a_3256_ = v_a_3755_;
goto v___jp_3255_;
}
else
{
return v___x_3754_;
}
}
else
{
lean_object* v_toCold_3756_; lean_object* v_ref_3757_; lean_object* v_quotContext_3758_; lean_object* v_currMacroScope_3759_; uint8_t v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
lean_dec(v_a_3260_);
lean_dec(v___x_3241_);
lean_dec(v___x_3239_);
lean_dec_ref(v_arg_3238_);
lean_dec_ref(v___x_3234_);
v_toCold_3756_ = lean_ctor_get(v___y_3252_, 0);
lean_inc_ref(v_toCold_3756_);
v_ref_3757_ = lean_ctor_get(v___y_3252_, 2);
lean_inc(v_ref_3757_);
lean_dec_ref(v___y_3252_);
v_quotContext_3758_ = lean_ctor_get(v_toCold_3756_, 8);
lean_inc_n(v_quotContext_3758_, 2);
v_currMacroScope_3759_ = lean_ctor_get(v_toCold_3756_, 9);
lean_inc_n(v_currMacroScope_3759_, 2);
lean_dec_ref(v_toCold_3756_);
v___x_3760_ = 0;
v___x_3761_ = l_Lean_SourceInfo_fromRef(v_ref_3757_, v___x_3760_);
lean_dec(v_ref_3757_);
v___x_3762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3763_ = l_Lean_Name_mkStr3(v___x_3243_, v___x_3244_, v___x_3762_);
v___x_3764_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7));
v___x_3765_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3761_, 13);
v___x_3766_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3761_);
lean_ctor_set(v___x_3766_, 1, v___x_3764_);
lean_ctor_set(v___x_3766_, 2, v___x_3765_);
v___x_3767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3761_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3761_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = l_String_toRawSubstring_x27(v___x_3245_);
v___x_3774_ = l_Lean_addMacroScope(v_quotContext_3758_, v___x_3233_, v_currMacroScope_3759_);
v___x_3775_ = lean_box(0);
v___x_3776_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3761_);
lean_ctor_set(v___x_3776_, 1, v___x_3773_);
lean_ctor_set(v___x_3776_, 2, v___x_3774_);
lean_ctor_set(v___x_3776_, 3, v___x_3775_);
v___x_3777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3761_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3780_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3781_ = l_Lean_addMacroScope(v_quotContext_3758_, v___x_3780_, v_currMacroScope_3759_);
v___x_3782_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3761_);
lean_ctor_set(v___x_3782_, 1, v___x_3779_);
lean_ctor_set(v___x_3782_, 2, v___x_3781_);
lean_ctor_set(v___x_3782_, 3, v___x_3775_);
v___x_3783_ = l_Lean_Syntax_node3(v___x_3761_, v___x_3769_, v___x_3776_, v___x_3778_, v___x_3782_);
v___x_3784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3761_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = l_Lean_Syntax_node3(v___x_3761_, v___x_3770_, v___x_3772_, v___x_3783_, v___x_3785_);
v___x_3787_ = l_Lean_Syntax_node1(v___x_3761_, v___x_3769_, v___x_3786_);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3761_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_3791_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_3792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3761_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = l_Lean_Syntax_node1(v___x_3761_, v___x_3790_, v___x_3792_);
v___x_3794_ = l_Lean_Syntax_node5(v___x_3761_, v___x_3763_, v___x_3766_, v___x_3768_, v___x_3787_, v___x_3789_, v___x_3793_);
v_a_3256_ = v___x_3794_;
goto v___jp_3255_;
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec(v_a_3260_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3243_);
lean_dec_ref(v___x_3242_);
lean_dec(v___x_3241_);
lean_dec(v___x_3239_);
lean_dec_ref(v_arg_3238_);
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3233_);
v_a_3795_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3261_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3261_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3243_);
lean_dec_ref(v___x_3242_);
lean_dec(v___x_3241_);
lean_dec(v___x_3239_);
lean_dec_ref(v_arg_3238_);
lean_dec(v_inv_3237_);
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3233_);
v_a_3803_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3259_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3259_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
v___jp_3255_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = l_Lean_Syntax_eraseQuoteMacroScopes(v_a_3256_);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
return v___x_3258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_3811_ = _args[0];
lean_object* v___x_3812_ = _args[1];
lean_object* v___f_3813_ = _args[2];
lean_object* v_a_3814_ = _args[3];
lean_object* v_inv_3815_ = _args[4];
lean_object* v_arg_3816_ = _args[5];
lean_object* v___x_3817_ = _args[6];
lean_object* v___x_3818_ = _args[7];
lean_object* v___x_3819_ = _args[8];
lean_object* v___x_3820_ = _args[9];
lean_object* v___x_3821_ = _args[10];
lean_object* v___x_3822_ = _args[11];
lean_object* v___x_3823_ = _args[12];
lean_object* v___y_3824_ = _args[13];
lean_object* v___y_3825_ = _args[14];
lean_object* v___y_3826_ = _args[15];
lean_object* v___y_3827_ = _args[16];
lean_object* v___y_3828_ = _args[17];
lean_object* v___y_3829_ = _args[18];
lean_object* v___y_3830_ = _args[19];
lean_object* v___y_3831_ = _args[20];
lean_object* v___y_3832_ = _args[21];
_start:
{
uint8_t v___x_79874__boxed_3833_; lean_object* v_res_3834_; 
v___x_79874__boxed_3833_ = lean_unbox(v___x_3818_);
v_res_3834_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_3811_, v___x_3812_, v___f_3813_, v_a_3814_, v_inv_3815_, v_arg_3816_, v___x_3817_, v___x_79874__boxed_3833_, v___x_3819_, v___x_3820_, v___x_3821_, v___x_3822_, v___x_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec_ref(v_a_3814_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___x_3841_; lean_object* v_env_3842_; uint8_t v___x_3843_; lean_object* v_env_3844_; lean_object* v___x_3845_; lean_object* v_toCold_3846_; lean_object* v_mctx_3847_; lean_object* v_lctx_3848_; lean_object* v_options_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3841_ = lean_st_ref_get(v___y_3839_);
v_env_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc_ref(v_env_3842_);
lean_dec(v___x_3841_);
v___x_3843_ = 0;
v_env_3844_ = l_Lean_Environment_setRecordingDeps(v_env_3842_, v___x_3843_);
v___x_3845_ = lean_st_ref_get(v___y_3837_);
v_toCold_3846_ = lean_ctor_get(v___y_3838_, 0);
v_mctx_3847_ = lean_ctor_get(v___x_3845_, 0);
lean_inc_ref(v_mctx_3847_);
lean_dec(v___x_3845_);
v_lctx_3848_ = lean_ctor_get(v___y_3836_, 2);
v_options_3849_ = lean_ctor_get(v_toCold_3846_, 2);
lean_inc_ref(v_options_3849_);
lean_inc_ref(v_lctx_3848_);
v___x_3850_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3850_, 0, v_env_3844_);
lean_ctor_set(v___x_3850_, 1, v_mctx_3847_);
lean_ctor_set(v___x_3850_, 2, v_lctx_3848_);
lean_ctor_set(v___x_3850_, 3, v_options_3849_);
v___x_3851_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
lean_ctor_set(v___x_3851_, 1, v_msgData_3835_);
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_ref_3866_; lean_object* v___x_3867_; lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3876_; 
v_ref_3866_ = lean_ctor_get(v___y_3863_, 2);
v___x_3867_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
lean_inc(v_ref_3866_);
v___x_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3872_, 0, v_ref_3866_);
lean_ctor_set(v___x_3872_, 1, v_a_3868_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set_tag(v___x_3870_, 1);
lean_ctor_set(v___x_3870_, 0, v___x_3872_);
v___x_3874_ = v___x_3870_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_3890_, size_t v_i_3891_, size_t v_stop_3892_, lean_object* v_b_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_a_3904_; lean_object* v___y_3909_; lean_object* v_a_3912_; uint8_t v___x_3914_; 
v___x_3914_ = lean_usize_dec_eq(v_i_3891_, v_stop_3892_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_array_uget_borrowed(v_as_3890_, v_i_3891_);
v___x_3916_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3895_, v___y_3897_, v___y_3899_, v___y_3901_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___y_3919_; lean_object* v_a_3920_; lean_object* v_ref_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v_ref_3935_ = lean_ctor_get(v___y_3900_, 2);
v___x_3936_ = l_Lean_SourceInfo_fromRef(v_ref_3935_, v___x_3914_);
v___x_3937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_3938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
lean_inc(v___x_3936_);
v___x_3939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3936_);
lean_ctor_set(v___x_3939_, 1, v___x_3937_);
v___x_3940_ = l_Lean_Syntax_node1(v___x_3936_, v___x_3938_, v___x_3939_);
lean_inc(v___x_3915_);
v___x_3941_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_3915_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3943_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref_known(v___x_3941_, 1);
v___x_3943_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_3940_, v_a_3942_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; 
lean_dec(v_a_3917_);
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = lean_array_mk(v_a_3944_);
v_a_3912_ = v___x_3945_;
goto v___jp_3911_;
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
v_a_3946_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3943_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3943_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
lean_inc(v_a_3946_);
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
v___y_3919_ = v___x_3951_;
v_a_3920_ = v_a_3946_;
goto v___jp_3918_;
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v___x_3940_);
v_a_3954_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3941_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3941_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
lean_inc(v_a_3954_);
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
v___y_3919_ = v___x_3959_;
v_a_3920_ = v_a_3954_;
goto v___jp_3918_;
}
}
}
v___jp_3918_:
{
uint8_t v___x_3921_; 
v___x_3921_ = l_Lean_Exception_isInterrupt(v_a_3920_);
if (v___x_3921_ == 0)
{
uint8_t v___x_3922_; 
v___x_3922_ = l_Lean_Exception_isRuntime(v_a_3920_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; 
lean_dec_ref(v___y_3919_);
v___x_3923_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3917_, v___x_3922_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_dec_ref_known(v___x_3923_, 1);
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = lean_mk_empty_array_with_capacity(v___x_3924_);
lean_inc(v___x_3915_);
v___x_3926_ = lean_array_push(v___x_3925_, v___x_3915_);
v_a_3912_ = v___x_3926_;
goto v___jp_3911_;
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v_b_3893_);
v_a_3927_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3923_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3923_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
else
{
lean_dec(v_a_3917_);
lean_dec_ref(v_b_3893_);
v___y_3909_ = v___y_3919_;
goto v___jp_3908_;
}
}
else
{
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3917_);
lean_dec_ref(v_b_3893_);
v___y_3909_ = v___y_3919_;
goto v___jp_3908_;
}
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v_b_3893_);
v_a_3962_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3916_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3916_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
else
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v_b_3893_);
return v___x_3970_;
}
v___jp_3903_:
{
size_t v___x_3905_; size_t v___x_3906_; 
v___x_3905_ = ((size_t)1ULL);
v___x_3906_ = lean_usize_add(v_i_3891_, v___x_3905_);
v_i_3891_ = v___x_3906_;
v_b_3893_ = v_a_3904_;
goto _start;
}
v___jp_3908_:
{
if (lean_obj_tag(v___y_3909_) == 0)
{
lean_object* v_a_3910_; 
v_a_3910_ = lean_ctor_get(v___y_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___y_3909_, 1);
v_a_3904_ = v_a_3910_;
goto v___jp_3903_;
}
else
{
return v___y_3909_;
}
}
v___jp_3911_:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Array_append___redArg(v_b_3893_, v_a_3912_);
lean_dec_ref(v_a_3912_);
v_a_3904_ = v___x_3913_;
goto v___jp_3903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_3971_, lean_object* v_i_3972_, lean_object* v_stop_3973_, lean_object* v_b_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
size_t v_i_boxed_3984_; size_t v_stop_boxed_3985_; lean_object* v_res_3986_; 
v_i_boxed_3984_ = lean_unbox_usize(v_i_3972_);
lean_dec(v_i_3972_);
v_stop_boxed_3985_ = lean_unbox_usize(v_stop_3973_);
lean_dec(v_stop_3973_);
v_res_3986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_3971_, v_i_boxed_3984_, v_stop_boxed_3985_, v_b_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec_ref(v_as_3971_);
return v_res_3986_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_3989_ = l_Lean_stringToMessageData(v___x_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4005_, lean_object* v_inv_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v___x_4016_; 
lean_inc(v_inv_4006_);
v___x_4016_ = l_Lean_MVarId_getType(v_inv_4006_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4018_; lean_object* v_a_4019_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___x_4033_; uint8_t v___x_4034_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
v___x_4018_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4017_, v_a_4012_);
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref(v___x_4018_);
v___x_4033_ = l_Lean_Expr_cleanupAnnotations(v_a_4019_);
v___x_4034_ = l_Lean_Expr_isApp(v___x_4033_);
if (v___x_4034_ == 0)
{
lean_dec_ref(v___x_4033_);
lean_dec(v_inv_4006_);
v___y_4021_ = v_a_4007_;
v___y_4022_ = v_a_4008_;
v___y_4023_ = v_a_4009_;
v___y_4024_ = v_a_4010_;
v___y_4025_ = v_a_4011_;
v___y_4026_ = v_a_4012_;
v___y_4027_ = v_a_4013_;
v___y_4028_ = v_a_4014_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4035_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4033_);
lean_dec_ref(v___x_4033_);
v___x_4036_ = l_Lean_Expr_isApp(v___x_4035_);
if (v___x_4036_ == 0)
{
lean_dec_ref(v___x_4035_);
lean_dec(v_inv_4006_);
v___y_4021_ = v_a_4007_;
v___y_4022_ = v_a_4008_;
v___y_4023_ = v_a_4009_;
v___y_4024_ = v_a_4010_;
v___y_4025_ = v_a_4011_;
v___y_4026_ = v_a_4012_;
v___y_4027_ = v_a_4013_;
v___y_4028_ = v_a_4014_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4037_; uint8_t v___x_4038_; 
v___x_4037_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4035_);
v___x_4038_ = l_Lean_Expr_isApp(v___x_4037_);
if (v___x_4038_ == 0)
{
lean_dec_ref(v___x_4037_);
lean_dec_ref(v___x_4035_);
lean_dec(v_inv_4006_);
v___y_4021_ = v_a_4007_;
v___y_4022_ = v_a_4008_;
v___y_4023_ = v_a_4009_;
v___y_4024_ = v_a_4010_;
v___y_4025_ = v_a_4011_;
v___y_4026_ = v_a_4012_;
v___y_4027_ = v_a_4013_;
v___y_4028_ = v_a_4014_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4039_; uint8_t v___x_4040_; 
v___x_4039_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4037_);
v___x_4040_ = l_Lean_Expr_isApp(v___x_4039_);
if (v___x_4040_ == 0)
{
lean_dec_ref(v___x_4039_);
lean_dec_ref(v___x_4037_);
lean_dec_ref(v___x_4035_);
lean_dec(v_inv_4006_);
v___y_4021_ = v_a_4007_;
v___y_4022_ = v_a_4008_;
v___y_4023_ = v_a_4009_;
v___y_4024_ = v_a_4010_;
v___y_4025_ = v_a_4011_;
v___y_4026_ = v_a_4012_;
v___y_4027_ = v_a_4013_;
v___y_4028_ = v_a_4014_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v___x_4041_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4039_);
v___x_4042_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4043_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4045_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4046_ = l_Lean_Expr_isConstOf(v___x_4041_, v___x_4045_);
if (v___x_4046_ == 0)
{
lean_dec_ref(v___x_4041_);
lean_dec_ref(v___x_4039_);
lean_dec_ref(v___x_4037_);
lean_dec_ref(v___x_4035_);
lean_dec(v_inv_4006_);
v___y_4021_ = v_a_4007_;
v___y_4022_ = v_a_4008_;
v___y_4023_ = v_a_4009_;
v___y_4024_ = v_a_4010_;
v___y_4025_ = v_a_4011_;
v___y_4026_ = v_a_4012_;
v___y_4027_ = v_a_4013_;
v___y_4028_ = v_a_4014_;
goto v___jp_4020_;
}
else
{
lean_object* v_arg_4047_; lean_object* v_arg_4048_; lean_object* v_arg_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v_a_4056_; lean_object* v___x_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; 
lean_dec(v_a_4019_);
v_arg_4047_ = lean_ctor_get(v___x_4035_, 1);
lean_inc_ref(v_arg_4047_);
lean_dec_ref(v___x_4035_);
v_arg_4048_ = lean_ctor_get(v___x_4037_, 1);
lean_inc_ref(v_arg_4048_);
lean_dec_ref(v___x_4037_);
v_arg_4049_ = lean_ctor_get(v___x_4039_, 1);
lean_inc_ref(v_arg_4049_);
lean_dec_ref(v___x_4039_);
v___x_4050_ = lean_unsigned_to_nat(1u);
v___x_4051_ = l_Lean_Expr_constLevels_x21(v___x_4041_);
lean_dec_ref(v___x_4041_);
v___x_4052_ = lean_unsigned_to_nat(0u);
v___x_4053_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4051_);
v___x_4054_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4051_, v___x_4051_, v___x_4050_, v___x_4053_);
lean_dec(v___x_4051_);
v___x_4067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4068_ = lean_array_get_size(v_vcs_4005_);
v___x_4069_ = lean_nat_dec_lt(v___x_4052_, v___x_4068_);
if (v___x_4069_ == 0)
{
v_a_4056_ = v___x_4067_;
goto v___jp_4055_;
}
else
{
size_t v___x_4070_; size_t v___x_4071_; lean_object* v___x_4072_; 
v___x_4070_ = ((size_t)0ULL);
v___x_4071_ = lean_usize_of_nat(v___x_4068_);
v___x_4072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4005_, v___x_4070_, v___x_4071_, v___x_4067_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v___x_4072_, 1);
v_a_4056_ = v_a_4073_;
goto v___jp_4055_;
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v___x_4054_);
lean_dec_ref(v_arg_4049_);
lean_dec_ref(v_arg_4048_);
lean_dec_ref(v_arg_4047_);
lean_dec(v_inv_4006_);
v_a_4074_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4072_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4072_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
v___jp_4055_:
{
lean_object* v___x_4057_; lean_object* v___f_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___f_4065_; lean_object* v___x_4066_; 
v___x_4057_ = lean_box(v___x_4046_);
lean_inc_ref(v_arg_4047_);
lean_inc_n(v_inv_4006_, 2);
lean_inc_ref(v_a_4056_);
v___f_4058_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4058_, 0, v_a_4056_);
lean_closure_set(v___f_4058_, 1, v_inv_4006_);
lean_closure_set(v___f_4058_, 2, v___x_4057_);
lean_closure_set(v___f_4058_, 3, v___x_4050_);
lean_closure_set(v___f_4058_, 4, v_arg_4047_);
v___x_4059_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4061_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4062_ = l_Lean_mkConst(v___x_4061_, v___x_4054_);
v___x_4063_ = l_Lean_mkAppB(v___x_4062_, v_arg_4049_, v_arg_4048_);
v___x_4064_ = lean_box(v___x_4046_);
v___f_4065_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4065_, 0, v___x_4060_);
lean_closure_set(v___f_4065_, 1, v___x_4063_);
lean_closure_set(v___f_4065_, 2, v___f_4058_);
lean_closure_set(v___f_4065_, 3, v_a_4056_);
lean_closure_set(v___f_4065_, 4, v_inv_4006_);
lean_closure_set(v___f_4065_, 5, v_arg_4047_);
lean_closure_set(v___f_4065_, 6, v___x_4050_);
lean_closure_set(v___f_4065_, 7, v___x_4064_);
lean_closure_set(v___f_4065_, 8, v___x_4052_);
lean_closure_set(v___f_4065_, 9, v___x_4044_);
lean_closure_set(v___f_4065_, 10, v___x_4042_);
lean_closure_set(v___f_4065_, 11, v___x_4043_);
lean_closure_set(v___f_4065_, 12, v___x_4059_);
v___x_4066_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4006_, v___f_4065_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
return v___x_4066_;
}
}
}
}
}
}
v___jp_4020_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4029_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4030_ = l_Lean_MessageData_ofExpr(v_a_4019_);
v___x_4031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4031_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
return v___x_4032_;
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec(v_inv_4006_);
v_a_4082_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4016_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4016_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4090_, lean_object* v_inv_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4090_, v_inv_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec_ref(v_vcs_4090_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4102_, lean_object* v_msg_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4103_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4114_, lean_object* v_msg_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4114_, v_msg_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4126_, lean_object* v_name_4127_, uint8_t v_bi_4128_, lean_object* v_type_4129_, lean_object* v_k_4130_, uint8_t v_kind_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4127_, v_bi_4128_, v_type_4129_, v_k_4130_, v_kind_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4142_, lean_object* v_name_4143_, lean_object* v_bi_4144_, lean_object* v_type_4145_, lean_object* v_k_4146_, lean_object* v_kind_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
uint8_t v_bi_boxed_4157_; uint8_t v_kind_boxed_4158_; lean_object* v_res_4159_; 
v_bi_boxed_4157_ = lean_unbox(v_bi_4144_);
v_kind_boxed_4158_ = lean_unbox(v_kind_4147_);
v_res_4159_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4142_, v_name_4143_, v_bi_boxed_4157_, v_type_4145_, v_k_4146_, v_kind_boxed_4158_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4160_, lean_object* v_name_4161_, lean_object* v_type_4162_, lean_object* v_k_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4161_, v_type_4162_, v_k_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4174_, lean_object* v_name_4175_, lean_object* v_type_4176_, lean_object* v_k_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4174_, v_name_4175_, v_type_4176_, v_k_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4188_, size_t v_sz_4189_, size_t v_i_4190_, lean_object* v_b_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4188_, v_sz_4189_, v_i_4190_, v_b_4191_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4202_, lean_object* v_sz_4203_, lean_object* v_i_4204_, lean_object* v_b_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
size_t v_sz_boxed_4215_; size_t v_i_boxed_4216_; lean_object* v_res_4217_; 
v_sz_boxed_4215_ = lean_unbox_usize(v_sz_4203_);
lean_dec(v_sz_4203_);
v_i_boxed_4216_ = lean_unbox_usize(v_i_4204_);
lean_dec(v_i_4204_);
v_res_4217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4202_, v_sz_boxed_4215_, v_i_boxed_4216_, v_b_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec_ref(v_as_4202_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4218_, size_t v_sz_4219_, size_t v_i_4220_, lean_object* v_b_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4218_, v_sz_4219_, v_i_4220_, v_b_4221_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4232_, lean_object* v_sz_4233_, lean_object* v_i_4234_, lean_object* v_b_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
size_t v_sz_boxed_4245_; size_t v_i_boxed_4246_; lean_object* v_res_4247_; 
v_sz_boxed_4245_ = lean_unbox_usize(v_sz_4233_);
lean_dec(v_sz_4233_);
v_i_boxed_4246_ = lean_unbox_usize(v_i_4234_);
lean_dec(v_i_4234_);
v_res_4247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4232_, v_sz_boxed_4245_, v_i_boxed_4246_, v_b_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec_ref(v_as_4232_);
return v_res_4247_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(builtin);
}
#ifdef __cplusplus
}
#endif
