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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 91, 82, 196, 249, 72, 203, 194)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ExceptConds"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(72, 205, 41, 157, 129, 142, 231, 99)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(226, 139, 39, 26, 105, 135, 247, 193)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "prefix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(230, 205, 224, 142, 140, 162, 83, 182)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10_value;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(139, 147, 12, 12, 50, 62, 178, 236)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(80, 174, 198, 53, 67, 44, 24, 11)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 33, 255, 249, 3, 79, 124, 43)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ExceptConds.true"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(139, 147, 12, 12, 50, 62, 178, 236)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(251, 220, 146, 174, 153, 82, 100, 162)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(240, 66, 120, 132, 230, 141, 174, 69)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__33 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 10, .m_data = "term_⇓_=>_"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⇓"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__7_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "term_⇓\?_=>_"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⇓\?"};
static const lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___y_62_; lean_object* v___y_63_; lean_object* v___x_76_; lean_object* v_dummy_77_; lean_object* v_nargs_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v_a_82_; uint8_t v___y_84_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_76_ = lean_box(0);
v_dummy_77_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0);
v_nargs_78_ = l_Lean_Expr_getAppNumArgs(v_type_49_);
lean_inc(v_nargs_78_);
v___x_79_ = lean_mk_array(v_nargs_78_, v_dummy_77_);
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_sub(v_nargs_78_, v___x_80_);
lean_inc(v___x_81_);
lean_inc_ref(v_type_49_);
v_a_82_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_49_, v___x_79_, v___x_81_);
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__5));
v___x_107_ = l_Lean_Expr_isAppOf(v_type_49_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__8));
v___x_109_ = l_Lean_Expr_isAppOf(v_type_49_, v___x_108_);
v___y_84_ = v___x_109_;
goto v___jp_83_;
}
else
{
v___y_84_ = v___x_107_;
goto v___jp_83_;
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
if (lean_obj_tag(v___y_63_) == 0)
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
v___y_53_ = v___y_62_;
v___y_54_ = v___x_64_;
goto v___jp_52_;
}
else
{
lean_object* v_val_65_; 
v_val_65_ = lean_ctor_get(v___y_63_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v___y_63_, 1);
v___y_53_ = v___y_62_;
v___y_54_ = v_val_65_;
goto v___jp_52_;
}
}
v___jp_66_:
{
lean_object* v_lctx_67_; lean_object* v___x_68_; 
v_lctx_67_ = lean_ctor_get(v_a_50_, 2);
v___x_68_ = l_Lean_LocalContext_lastDecl(v_lctx_67_);
if (lean_obj_tag(v___x_68_) == 1)
{
lean_object* v_val_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_val_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_val_69_);
lean_dec_ref_known(v___x_68_, 1);
v___x_70_ = l_Lean_LocalDecl_type(v_val_69_);
lean_dec(v_val_69_);
v___x_71_ = l_Lean_Expr_consumeMData(v___x_70_);
lean_dec_ref(v___x_70_);
v___x_72_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel(v_type_49_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v___x_73_; 
v___x_73_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_getULiftDownLevel(v___x_71_);
v___y_62_ = v___x_71_;
v___y_63_ = v___x_73_;
goto v___jp_61_;
}
else
{
v___y_62_ = v___x_71_;
v___y_63_ = v___x_72_;
goto v___jp_61_;
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v___x_68_);
lean_dec_ref(v_type_49_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
v___jp_83_:
{
if (v___y_84_ == 0)
{
lean_dec_ref(v_a_82_);
lean_dec(v___x_81_);
lean_dec(v_nargs_78_);
goto v___jp_66_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_85_ = lean_unsigned_to_nat(2u);
v___x_86_ = lean_array_get_size(v_a_82_);
v___x_87_ = lean_nat_dec_lt(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_dec_ref(v_a_82_);
lean_dec(v___x_81_);
lean_dec(v_nargs_78_);
goto v___jp_66_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_88_ = l_Lean_Expr_getAppFn(v_type_49_);
v___x_89_ = l_Lean_Expr_constLevels_x21(v___x_88_);
lean_dec_ref(v___x_88_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = l_List_get_x21Internal___redArg(v___x_76_, v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_nat_sub(v___x_81_, v___x_80_);
lean_dec(v___x_81_);
v___x_93_ = l_Lean_Expr_getRevArg_x21(v_type_49_, v___x_92_);
v___x_94_ = lean_unsigned_to_nat(3u);
v___x_95_ = l_Array_toSubarray___redArg(v_a_82_, v___x_94_, v___x_86_);
v___x_96_ = l_Subarray_copy___redArg(v___x_95_);
lean_inc_ref(v___x_96_);
v___x_97_ = l_Lean_Expr_beta(v___x_93_, v___x_96_);
v___x_98_ = lean_nat_sub(v_nargs_78_, v___x_85_);
lean_dec(v_nargs_78_);
v___x_99_ = lean_nat_sub(v___x_98_, v___x_80_);
lean_dec(v___x_98_);
v___x_100_ = l_Lean_Expr_getRevArg_x21(v_type_49_, v___x_99_);
lean_dec_ref(v_type_49_);
v___x_101_ = l_Lean_Expr_beta(v___x_100_, v___x_96_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_97_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_91_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___boxed(lean_object* v_type_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(v_type_110_, v_a_111_);
lean_dec_ref(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget(lean_object* v_type_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg(v_type_114_, v_a_115_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed(lean_object* v_type_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget(v_type_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx(lean_object* v_x_128_){
_start:
{
switch(lean_obj_tag(v_x_128_))
{
case 0:
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(0u);
return v___x_129_;
}
case 1:
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(1u);
return v___x_130_;
}
default: 
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(2u);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx___boxed(lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorIdx(v_x_132_);
lean_dec(v_x_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(lean_object* v_t_134_, lean_object* v_k_135_){
_start:
{
if (lean_obj_tag(v_t_134_) == 0)
{
lean_object* v_invariantUse_136_; lean_object* v___x_137_; 
v_invariantUse_136_ = lean_ctor_get(v_t_134_, 0);
lean_inc_ref(v_invariantUse_136_);
lean_dec_ref_known(v_t_134_, 1);
v___x_137_ = lean_apply_1(v_k_135_, v_invariantUse_136_);
return v___x_137_;
}
else
{
lean_dec(v_t_134_);
return v_k_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim(lean_object* v_motive_138_, lean_object* v_ctorIdx_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_k_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_140_, v_k_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___boxed(lean_object* v_motive_144_, lean_object* v_ctorIdx_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim(v_motive_144_, v_ctorIdx_145_, v_t_146_, v_h_147_, v_k_148_);
lean_dec(v_ctorIdx_145_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_success_elim___redArg(lean_object* v_t_150_, lean_object* v_success_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_150_, v_success_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_success_elim(lean_object* v_motive_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_success_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_154_, v_success_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_notAnInvariantUse_elim___redArg(lean_object* v_t_158_, lean_object* v_notAnInvariantUse_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_158_, v_notAnInvariantUse_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_notAnInvariantUse_elim(lean_object* v_motive_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_notAnInvariantUse_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_162_, v_notAnInvariantUse_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_unknownInvariantUse_elim___redArg(lean_object* v_t_166_, lean_object* v_unknownInvariantUse_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_166_, v_unknownInvariantUse_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_unknownInvariantUse_elim(lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_unknownInvariantUse_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ClassifyInvariantUseResult_ctorElim___redArg(v_t_170_, v_unknownInvariantUse_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(lean_object* v_a_179_){
_start:
{
lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_206_; 
v_fst_180_ = lean_ctor_get(v_a_179_, 0);
v_snd_181_ = lean_ctor_get(v_a_179_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_a_179_);
if (v_isSharedCheck_206_ == 0)
{
v___x_183_ = v_a_179_;
v_isShared_184_ = v_isSharedCheck_206_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_inc(v_fst_180_);
lean_dec(v_a_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_206_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = lean_unsigned_to_nat(4u);
v___x_186_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_187_ = l_Lean_Expr_isAppOfArity(v_fst_180_, v___x_186_, v___x_185_);
if (v___x_187_ == 0)
{
lean_object* v___x_189_; 
if (v_isShared_184_ == 0)
{
v___x_189_ = v___x_183_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_fst_180_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_snd_181_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_191_ = lean_unsigned_to_nat(2u);
v___x_192_ = lean_unsigned_to_nat(3u);
v___x_193_ = l_Lean_Expr_getAppNumArgs(v_fst_180_);
v___x_194_ = lean_nat_sub(v___x_193_, v___x_191_);
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_sub(v___x_194_, v___x_195_);
lean_dec(v___x_194_);
v___x_197_ = l_Lean_Expr_getRevArg_x21(v_fst_180_, v___x_196_);
v___x_198_ = lean_array_push(v_snd_181_, v___x_197_);
v___x_199_ = lean_nat_sub(v___x_193_, v___x_192_);
lean_dec(v___x_193_);
v___x_200_ = lean_nat_sub(v___x_199_, v___x_195_);
lean_dec(v___x_199_);
v___x_201_ = l_Lean_Expr_getRevArg_x21(v_fst_180_, v___x_200_);
lean_dec(v_fst_180_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_198_);
lean_ctor_set(v___x_183_, 0, v___x_201_);
v___x_203_ = v___x_183_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_198_);
v___x_203_ = v_reuseFailAlloc_205_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v_a_179_ = v___x_203_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(lean_object* v_inv_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_254_; 
v_snd_215_ = lean_ctor_get(v_a_214_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v_a_214_, 0);
lean_dec(v_unused_255_);
v___x_217_ = v_a_214_;
v_isShared_218_ = v_isSharedCheck_254_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_dec(v_a_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_254_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_fst_219_; lean_object* v_snd_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_253_; 
v_fst_219_ = lean_ctor_get(v_snd_215_, 0);
v_snd_220_ = lean_ctor_get(v_snd_215_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_snd_215_);
if (v_isSharedCheck_253_ == 0)
{
v___x_222_ = v_snd_215_;
v_isShared_223_ = v_isSharedCheck_253_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_snd_220_);
lean_inc(v_fst_219_);
lean_dec(v_snd_215_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_253_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = lean_box(0);
lean_inc(v_inv_213_);
v___x_225_ = l_Lean_mkMVar(v_inv_213_);
v___x_226_ = lean_expr_eqv(v_fst_219_, v___x_225_);
lean_dec_ref(v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_227_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_228_ = lean_unsigned_to_nat(4u);
v___x_229_ = l_Lean_Expr_isAppOfArity(v_fst_219_, v___x_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_232_; 
lean_dec(v_inv_213_);
v___x_230_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__2));
if (v_isShared_223_ == 0)
{
v___x_232_ = v___x_222_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_fst_219_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_snd_220_);
v___x_232_ = v_reuseFailAlloc_236_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_232_);
lean_ctor_set(v___x_217_, 0, v___x_230_);
v___x_234_ = v___x_217_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_snd_220_, v___x_237_);
lean_dec(v_snd_220_);
v___x_239_ = l_Lean_Expr_getRevArg_x21(v_fst_219_, v___x_237_);
lean_dec(v_fst_219_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_238_);
lean_ctor_set(v___x_222_, 0, v___x_239_);
v___x_241_ = v___x_222_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_238_);
v___x_241_ = v_reuseFailAlloc_246_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_241_);
lean_ctor_set(v___x_217_, 0, v___x_224_);
v___x_243_ = v___x_217_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_241_);
v___x_243_ = v_reuseFailAlloc_245_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
v_a_214_ = v___x_243_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_248_; 
lean_dec(v_inv_213_);
if (v_isShared_223_ == 0)
{
v___x_248_ = v___x_222_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_fst_219_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_snd_220_);
v___x_248_ = v_reuseFailAlloc_252_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_248_);
lean_ctor_set(v___x_217_, 0, v___x_224_);
v___x_250_ = v___x_217_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(lean_object* v_assertion_268_, lean_object* v_inv_269_){
_start:
{
lean_object* v_assertion_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_assertion_270_ = l_Lean_Expr_consumeMData(v_assertion_268_);
v___x_271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1));
v___x_272_ = l_Lean_Expr_isAppOf(v_assertion_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec_ref(v_assertion_270_);
lean_dec(v_inv_269_);
v___x_273_ = lean_box(1);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_head_279_; lean_object* v_conditionIdx_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_fst_285_; 
v___x_274_ = lean_unsigned_to_nat(2u);
v___x_275_ = l_Lean_Expr_getAppNumArgs(v_assertion_270_);
v___x_276_ = lean_nat_sub(v___x_275_, v___x_274_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_sub(v___x_276_, v___x_277_);
lean_dec(v___x_276_);
v_head_279_ = l_Lean_Expr_getRevArg_x21(v_assertion_270_, v___x_278_);
v_conditionIdx_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_box(0);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_head_279_);
lean_ctor_set(v___x_282_, 1, v_conditionIdx_280_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(v_inv_269_, v___x_283_);
v_fst_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_fst_285_);
if (lean_obj_tag(v_fst_285_) == 0)
{
lean_object* v_snd_286_; lean_object* v_dummy_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_snd_286_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_snd_286_);
lean_dec_ref(v___x_284_);
v_dummy_287_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0);
lean_inc(v___x_275_);
v___x_288_ = lean_mk_array(v___x_275_, v_dummy_287_);
v___x_289_ = lean_nat_sub(v___x_275_, v___x_277_);
lean_dec(v___x_275_);
v___x_290_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_assertion_270_, v___x_288_, v___x_289_);
v___x_291_ = lean_array_get_size(v___x_290_);
v___x_292_ = lean_unsigned_to_nat(4u);
v___x_293_ = lean_nat_dec_lt(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_294_ = l_Lean_instInhabitedExpr;
v___x_295_ = lean_unsigned_to_nat(3u);
v___x_296_ = lean_array_get(v___x_294_, v___x_290_, v___x_295_);
v___x_297_ = l_Lean_Expr_cleanupAnnotations(v___x_296_);
v___x_298_ = l_Lean_Expr_isApp(v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec_ref(v___x_297_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_299_ = lean_box(2);
return v___x_299_;
}
else
{
lean_object* v_arg_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_arg_300_ = lean_ctor_get(v___x_297_, 1);
lean_inc_ref(v_arg_300_);
v___x_301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_297_);
v___x_302_ = l_Lean_Expr_isApp(v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_301_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_303_ = lean_box(2);
return v___x_303_;
}
else
{
lean_object* v_arg_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_arg_304_ = lean_ctor_get(v___x_301_, 1);
lean_inc_ref(v_arg_304_);
v___x_305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_301_);
v___x_306_ = l_Lean_Expr_isApp(v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_dec_ref(v___x_305_);
lean_dec_ref(v_arg_304_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_307_ = lean_box(2);
return v___x_307_;
}
else
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = l_Lean_Expr_appFnCleanup___redArg(v___x_305_);
v___x_309_ = l_Lean_Expr_isApp(v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
lean_dec_ref(v___x_308_);
lean_dec_ref(v_arg_304_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_310_ = lean_box(2);
return v___x_310_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_311_ = l_Lean_Expr_appFnCleanup___redArg(v___x_308_);
v___x_312_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_313_ = l_Lean_Expr_isConstOf(v___x_311_, v___x_312_);
lean_dec_ref(v___x_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec_ref(v_arg_304_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_314_ = lean_box(2);
return v___x_314_;
}
else
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = l_Lean_Expr_cleanupAnnotations(v_arg_304_);
v___x_316_ = l_Lean_Expr_isApp(v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec_ref(v___x_315_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
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
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_320_ = lean_box(2);
return v___x_320_;
}
else
{
lean_object* v_arg_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_arg_321_ = lean_ctor_get(v___x_318_, 1);
lean_inc_ref(v_arg_321_);
v___x_322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_318_);
v___x_323_ = l_Lean_Expr_isApp(v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec_ref(v___x_322_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_324_ = lean_box(2);
return v___x_324_;
}
else
{
lean_object* v_arg_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_arg_325_ = lean_ctor_get(v___x_322_, 1);
lean_inc_ref(v_arg_325_);
v___x_326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_322_);
v___x_327_ = l_Lean_Expr_isApp(v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_328_ = lean_box(2);
return v___x_328_;
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = l_Lean_Expr_appFnCleanup___redArg(v___x_326_);
v___x_330_ = l_Lean_Expr_isApp(v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v___x_329_);
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_331_ = lean_box(2);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_329_);
v___x_333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_332_, v___x_333_);
lean_dec_ref(v___x_332_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_335_ = lean_box(2);
return v___x_335_;
}
else
{
lean_object* v_snd_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_352_; 
v_snd_336_ = lean_ctor_get(v_snd_286_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_snd_286_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v_snd_286_, 0);
lean_dec(v_unused_353_);
v___x_338_ = v_snd_286_;
v_isShared_339_ = v_isSharedCheck_352_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snd_336_);
lean_dec(v_snd_286_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_352_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
lean_inc_ref(v_arg_300_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v___x_340_);
lean_ctor_set(v___x_338_, 0, v_arg_300_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_arg_300_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_351_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_343_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(v___x_342_);
v_fst_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_fst_344_);
v_snd_345_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_snd_345_);
lean_dec_ref(v___x_343_);
v___x_346_ = l_Array_toSubarray___redArg(v___x_290_, v___x_292_, v___x_291_);
v___x_347_ = lean_array_push(v_snd_345_, v_fst_344_);
v___x_348_ = l_Subarray_copy___redArg(v___x_346_);
v___x_349_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_349_, 0, v_snd_336_);
lean_ctor_set(v___x_349_, 1, v_arg_325_);
lean_ctor_set(v___x_349_, 2, v_arg_321_);
lean_ctor_set(v___x_349_, 3, v___x_347_);
lean_ctor_set(v___x_349_, 4, v_arg_300_);
lean_ctor_set(v___x_349_, 5, v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
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
lean_object* v___x_354_; 
lean_dec_ref(v___x_290_);
lean_dec(v_snd_286_);
v___x_354_ = lean_box(1);
return v___x_354_;
}
}
else
{
lean_object* v_val_355_; 
lean_dec_ref(v___x_284_);
lean_dec(v___x_275_);
lean_dec_ref(v_assertion_270_);
v_val_355_ = lean_ctor_get(v_fst_285_, 0);
lean_inc(v_val_355_);
lean_dec_ref_known(v_fst_285_, 1);
return v_val_355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___boxed(lean_object* v_assertion_356_, lean_object* v_inv_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_assertion_356_, v_inv_357_);
lean_dec_ref(v_assertion_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0(lean_object* v_inv_359_, lean_object* v_inst_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(v_inv_359_, v_a_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1(lean_object* v_inst_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(v_a_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(lean_object* v_mvarId_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_366_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_373_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_373_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg___boxed(lean_object* v_mvarId_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_390_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_object* v_00_u03b1_398_, lean_object* v_mvarId_399_, lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_399_, v_x_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___boxed(lean_object* v_00_u03b1_407_, lean_object* v_mvarId_408_, lean_object* v_x_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(v_00_u03b1_407_, v_mvarId_408_, v_x_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(lean_object* v_e_416_, lean_object* v___y_417_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = l_Lean_Expr_hasMVar(v_e_416_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_e_416_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v_mctx_422_; lean_object* v___x_423_; lean_object* v_fst_424_; lean_object* v_snd_425_; lean_object* v___x_426_; lean_object* v_cache_427_; lean_object* v_zetaDeltaFVarIds_428_; lean_object* v_postponed_429_; lean_object* v_diag_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_439_; 
v___x_421_ = lean_st_ref_get(v___y_417_);
v_mctx_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_mctx_422_);
lean_dec(v___x_421_);
v___x_423_ = l_Lean_instantiateMVarsCore(v_mctx_422_, v_e_416_);
v_fst_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_fst_424_);
v_snd_425_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_snd_425_);
lean_dec_ref(v___x_423_);
v___x_426_ = lean_st_ref_take(v___y_417_);
v_cache_427_ = lean_ctor_get(v___x_426_, 1);
v_zetaDeltaFVarIds_428_ = lean_ctor_get(v___x_426_, 2);
v_postponed_429_ = lean_ctor_get(v___x_426_, 3);
v_diag_430_ = lean_ctor_get(v___x_426_, 4);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_426_, 0);
lean_dec(v_unused_440_);
v___x_432_ = v___x_426_;
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_diag_430_);
lean_inc(v_postponed_429_);
lean_inc(v_zetaDeltaFVarIds_428_);
lean_inc(v_cache_427_);
lean_dec(v___x_426_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v_snd_425_);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_snd_425_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_cache_427_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_zetaDeltaFVarIds_428_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_postponed_429_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_diag_430_);
v___x_435_ = v_reuseFailAlloc_438_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_st_ref_put(v___y_417_, v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v_fst_424_);
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg___boxed(lean_object* v_e_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_441_, v___y_442_);
lean_dec(v___y_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(lean_object* v_e_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_445_, v___y_447_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___boxed(lean_object* v_e_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(v_e_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object* v_inv_476_, uint8_t v___x_477_, lean_object* v___x_478_, lean_object* v_as_479_, size_t v_sz_480_, size_t v_i_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_a_489_; uint8_t v___x_493_; 
v___x_493_ = lean_usize_dec_lt(v_i_481_, v_sz_480_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v_inv_476_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_b_482_);
return v___x_494_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_496_; 
lean_dec_ref(v_b_482_);
v_a_495_ = lean_array_uget_borrowed(v_as_479_, v_i_481_);
lean_inc(v_a_495_);
v___x_496_ = l_Lean_MVarId_getType(v_a_495_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_558_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_558_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_558_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_558_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___y_503_; uint8_t v___y_504_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v_a_518_; lean_object* v___x_546_; 
v___x_501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v___x_515_ = lean_unsigned_to_nat(2u);
v___x_516_ = lean_nat_dec_lt(v___x_478_, v___x_515_);
v___x_546_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_497_, v___y_484_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = l_Lean_Expr_consumeMData(v_a_547_);
lean_dec(v_a_547_);
v_a_518_ = v___x_548_;
goto v___jp_517_;
}
else
{
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_546_, 1);
v_a_518_ = v_a_549_;
goto v___jp_517_;
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_del_object(v___x_499_);
lean_dec(v_inv_476_);
v_a_550_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_546_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_546_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
v___jp_502_:
{
if (v___y_504_ == 0)
{
lean_dec_ref(v___y_503_);
lean_del_object(v___x_499_);
v_a_489_ = v___x_501_;
goto v___jp_488_;
}
else
{
lean_object* v_letMuts_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_letMuts_505_ = lean_ctor_get(v___y_503_, 3);
lean_inc_ref(v_letMuts_505_);
lean_dec_ref(v___y_503_);
v___x_506_ = l_Lean_instInhabitedExpr;
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_array_get(v___x_506_, v_letMuts_505_, v___x_507_);
lean_dec_ref(v_letMuts_505_);
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3));
v___x_510_ = l_Lean_Expr_isAppOf(v___x_508_, v___x_509_);
lean_dec(v___x_508_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_dec(v_inv_476_);
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5));
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_511_);
v___x_513_ = v___x_499_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_del_object(v___x_499_);
v_a_489_ = v___x_501_;
goto v___jp_488_;
}
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_519_, 0, v_a_518_);
lean_inc(v_a_495_);
v___x_520_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_495_, v___x_519_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_537_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_537_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_537_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_537_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
if (lean_obj_tag(v_a_521_) == 1)
{
lean_object* v_val_525_; lean_object* v_snd_526_; lean_object* v_snd_527_; lean_object* v___x_528_; 
v_val_525_ = lean_ctor_get(v_a_521_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_a_521_, 1);
v_snd_526_ = lean_ctor_get(v_val_525_, 1);
lean_inc(v_snd_526_);
lean_dec(v_val_525_);
v_snd_527_ = lean_ctor_get(v_snd_526_, 1);
lean_inc(v_snd_527_);
lean_dec(v_snd_526_);
lean_inc(v_inv_476_);
v___x_528_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_527_, v_inv_476_);
lean_dec(v_snd_527_);
switch(lean_obj_tag(v___x_528_))
{
case 0:
{
lean_object* v_invariantUse_529_; lean_object* v_cursorSuffix_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
lean_del_object(v___x_523_);
v_invariantUse_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_ref(v_invariantUse_529_);
lean_dec_ref_known(v___x_528_, 1);
v_cursorSuffix_530_ = lean_ctor_get(v_invariantUse_529_, 2);
v___x_531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_532_ = l_Lean_Expr_isAppOf(v_cursorSuffix_530_, v___x_531_);
if (v___x_532_ == 0)
{
v___y_503_ = v_invariantUse_529_;
v___y_504_ = v___x_477_;
goto v___jp_502_;
}
else
{
v___y_503_ = v_invariantUse_529_;
v___y_504_ = v___x_516_;
goto v___jp_502_;
}
}
case 1:
{
lean_del_object(v___x_523_);
lean_del_object(v___x_499_);
v_a_489_ = v___x_501_;
goto v___jp_488_;
}
default: 
{
lean_object* v___x_533_; lean_object* v___x_535_; 
lean_del_object(v___x_499_);
lean_dec(v_inv_476_);
v___x_533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5));
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_533_);
v___x_535_ = v___x_523_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_del_object(v___x_523_);
lean_dec(v_a_521_);
lean_del_object(v___x_499_);
v_a_489_ = v___x_501_;
goto v___jp_488_;
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_del_object(v___x_499_);
lean_dec(v_inv_476_);
v_a_538_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_520_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_520_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec(v_inv_476_);
v_a_559_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_496_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_496_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
v___jp_488_:
{
size_t v___x_490_; size_t v___x_491_; 
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_481_, v___x_490_);
lean_inc_ref(v_a_489_);
v_i_481_ = v___x_491_;
v_b_482_ = v_a_489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object* v_inv_567_, lean_object* v___x_568_, lean_object* v___x_569_, lean_object* v_as_570_, lean_object* v_sz_571_, lean_object* v_i_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v___x_5242__boxed_579_; size_t v_sz_boxed_580_; size_t v_i_boxed_581_; lean_object* v_res_582_; 
v___x_5242__boxed_579_ = lean_unbox(v___x_568_);
v_sz_boxed_580_ = lean_unbox_usize(v_sz_571_);
lean_dec(v_sz_571_);
v_i_boxed_581_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_567_, v___x_5242__boxed_579_, v___x_569_, v_as_570_, v_sz_boxed_580_, v_i_boxed_581_, v_b_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_as_570_);
lean_dec(v___x_569_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object* v_vcs_587_, lean_object* v_inv_588_, lean_object* v_letMutsTy_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0));
v___x_602_ = l_Lean_Expr_isAppOf(v_letMutsTy_589_, v___x_601_);
if (v___x_602_ == 0)
{
lean_dec(v_inv_588_);
goto v___jp_595_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_603_ = l_Lean_Expr_getAppNumArgs(v_letMutsTy_589_);
v___x_604_ = lean_unsigned_to_nat(2u);
v___x_605_ = lean_nat_dec_lt(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_sub(v___x_603_, v___x_606_);
lean_inc(v___x_607_);
v___x_608_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_589_, v___x_607_);
v___x_609_ = l_Lean_Expr_cleanupAnnotations(v___x_608_);
v___x_610_ = l_Lean_Expr_isApp(v___x_609_);
if (v___x_610_ == 0)
{
lean_dec_ref(v___x_609_);
lean_dec(v___x_607_);
lean_dec(v___x_603_);
lean_dec(v_inv_588_);
goto v___jp_598_;
}
else
{
lean_object* v_arg_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_arg_611_ = lean_ctor_get(v___x_609_, 1);
lean_inc_ref(v_arg_611_);
v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_609_);
v___x_613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1));
v___x_614_ = l_Lean_Expr_isConstOf(v___x_612_, v___x_613_);
lean_dec_ref(v___x_612_);
if (v___x_614_ == 0)
{
lean_dec_ref(v_arg_611_);
lean_dec(v___x_607_);
lean_dec(v___x_603_);
lean_dec(v_inv_588_);
goto v___jp_598_;
}
else
{
lean_object* v___x_615_; size_t v_sz_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v_sz_616_ = lean_array_size(v_vcs_587_);
v___x_617_ = ((size_t)0ULL);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_588_, v___x_614_, v___x_603_, v_vcs_587_, v_sz_616_, v___x_617_, v___x_615_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v___x_603_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_642_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_642_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_642_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_642_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_fst_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_640_; 
v_fst_623_ = lean_ctor_get(v_a_619_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_a_619_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v_a_619_, 1);
lean_dec(v_unused_641_);
v___x_625_ = v_a_619_;
v_isShared_626_ = v_isSharedCheck_640_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_fst_623_);
lean_dec(v_a_619_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_640_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
if (lean_obj_tag(v_fst_623_) == 0)
{
lean_object* v___x_627_; lean_object* v_00_u03c3_628_; lean_object* v___x_630_; 
v___x_627_ = lean_nat_sub(v___x_607_, v___x_606_);
lean_dec(v___x_607_);
v_00_u03c3_628_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_589_, v___x_627_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_00_u03c3_628_);
lean_ctor_set(v___x_625_, 0, v_arg_611_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_arg_611_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_00_u03c3_628_);
v___x_630_ = v_reuseFailAlloc_635_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_631_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v_val_636_; lean_object* v___x_638_; 
lean_del_object(v___x_625_);
lean_dec_ref(v_arg_611_);
lean_dec(v___x_607_);
v_val_636_ = lean_ctor_get(v_fst_623_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v_fst_623_, 1);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_val_636_);
v___x_638_ = v___x_621_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_val_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v_arg_611_);
lean_dec(v___x_607_);
v_a_643_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_618_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_618_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
else
{
lean_dec(v___x_603_);
lean_dec(v_inv_588_);
goto v___jp_595_;
}
}
v___jp_595_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_box(0);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object* v_vcs_651_, lean_object* v_inv_652_, lean_object* v_letMutsTy_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_vcs_651_, v_inv_652_, v_letMutsTy_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec_ref(v_letMutsTy_653_);
lean_dec_ref(v_vcs_651_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object* v_dontRevert_660_, lean_object* v_as_661_, size_t v_i_662_, size_t v_stop_663_, lean_object* v_b_664_){
_start:
{
lean_object* v___y_666_; uint8_t v___x_670_; 
v___x_670_ = lean_usize_dec_eq(v_i_662_, v_stop_663_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_array_uget_borrowed(v_as_661_, v_i_662_);
lean_inc_ref(v_dontRevert_660_);
lean_inc(v___x_671_);
v___x_672_ = lean_apply_1(v_dontRevert_660_, v___x_671_);
v___x_673_ = lean_unbox(v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_inc(v___x_671_);
v___x_674_ = lean_array_push(v_b_664_, v___x_671_);
v___y_666_ = v___x_674_;
goto v___jp_665_;
}
else
{
v___y_666_ = v_b_664_;
goto v___jp_665_;
}
}
else
{
lean_dec_ref(v_dontRevert_660_);
return v_b_664_;
}
v___jp_665_:
{
size_t v___x_667_; size_t v___x_668_; 
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_add(v_i_662_, v___x_667_);
v_i_662_ = v___x_668_;
v_b_664_ = v___y_666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object* v_dontRevert_675_, lean_object* v_as_676_, lean_object* v_i_677_, lean_object* v_stop_678_, lean_object* v_b_679_){
_start:
{
size_t v_i_boxed_680_; size_t v_stop_boxed_681_; lean_object* v_res_682_; 
v_i_boxed_680_ = lean_unbox_usize(v_i_677_);
lean_dec(v_i_677_);
v_stop_boxed_681_ = lean_unbox_usize(v_stop_678_);
lean_dec(v_stop_678_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_675_, v_as_676_, v_i_boxed_680_, v_stop_boxed_681_, v_b_679_);
lean_dec_ref(v_as_676_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t v_sz_683_, size_t v_i_684_, lean_object* v_bs_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_lt(v_i_684_, v_sz_683_);
if (v___x_686_ == 0)
{
return v_bs_685_;
}
else
{
lean_object* v_v_687_; lean_object* v___x_688_; lean_object* v_bs_x27_689_; lean_object* v___x_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v_v_687_ = lean_array_uget(v_bs_685_, v_i_684_);
v___x_688_ = lean_unsigned_to_nat(0u);
v_bs_x27_689_ = lean_array_uset(v_bs_685_, v_i_684_, v___x_688_);
v___x_690_ = l_Lean_mkFVar(v_v_687_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_684_, v___x_691_);
v___x_693_ = lean_array_uset(v_bs_x27_689_, v_i_684_, v___x_690_);
v_i_684_ = v___x_692_;
v_bs_685_ = v___x_693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object* v_sz_695_, lean_object* v_i_696_, lean_object* v_bs_697_){
_start:
{
size_t v_sz_boxed_698_; size_t v_i_boxed_699_; lean_object* v_res_700_; 
v_sz_boxed_698_ = lean_unbox_usize(v_sz_695_);
lean_dec(v_sz_695_);
v_i_boxed_699_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_boxed_698_, v_i_boxed_699_, v_bs_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t v_sz_701_, size_t v_i_702_, lean_object* v_bs_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = lean_usize_dec_lt(v_i_702_, v_sz_701_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_bs_703_);
return v___x_710_;
}
else
{
lean_object* v_v_711_; lean_object* v___x_712_; 
v_v_711_ = lean_array_uget_borrowed(v_bs_703_, v_i_702_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v_v_711_);
v___x_712_ = lean_infer_type(v_v_711_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; lean_object* v_bs_x27_715_; size_t v___x_716_; size_t v___x_717_; lean_object* v___x_718_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = lean_unsigned_to_nat(0u);
v_bs_x27_715_ = lean_array_uset(v_bs_703_, v_i_702_, v___x_714_);
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_add(v_i_702_, v___x_716_);
v___x_718_ = lean_array_uset(v_bs_x27_715_, v_i_702_, v_a_713_);
v_i_702_ = v___x_717_;
v_bs_703_ = v___x_718_;
goto _start;
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v_bs_703_);
v_a_720_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_712_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_712_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object* v_sz_728_, lean_object* v_i_729_, lean_object* v_bs_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
size_t v_sz_boxed_736_; size_t v_i_boxed_737_; lean_object* v_res_738_; 
v_sz_boxed_736_ = lean_unbox_usize(v_sz_728_);
lean_dec(v_sz_728_);
v_i_boxed_737_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_boxed_736_, v_i_boxed_737_, v_bs_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object* v_m_739_, lean_object* v_query_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
lean_object* v_zero_744_; uint8_t v_isZero_745_; 
v_zero_744_ = lean_unsigned_to_nat(0u);
v_isZero_745_ = lean_nat_dec_eq(v_x_742_, v_zero_744_);
if (v_isZero_745_ == 1)
{
lean_dec(v_x_743_);
lean_dec(v_x_742_);
if (lean_obj_tag(v_x_741_) == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_box(2);
return v___x_746_;
}
else
{
lean_object* v_val_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_val_747_ = lean_ctor_get(v_x_741_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v_x_741_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_val_747_);
lean_dec(v_x_741_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_val_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_keyArray_755_; lean_object* v_valueArray_756_; lean_object* v___x_757_; uint8_t v_isSome_758_; 
v_keyArray_755_ = lean_ctor_get(v_m_739_, 1);
v_valueArray_756_ = lean_ctor_get(v_m_739_, 2);
v___x_757_ = lean_array_fget_borrowed(v_keyArray_755_, v_x_743_);
v_isSome_758_ = lean_noption_is_some(v___x_757_);
if (v_isSome_758_ == 0)
{
lean_dec(v_x_742_);
if (lean_obj_tag(v_x_741_) == 0)
{
lean_object* v___x_759_; 
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v_x_743_);
return v___x_759_;
}
else
{
lean_object* v_val_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_x_743_);
v_val_760_ = lean_ctor_get(v_x_741_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v_x_741_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_val_760_);
lean_dec(v_x_741_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_val_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_one_768_; lean_object* v_n_769_; lean_object* v___y_771_; 
v_one_768_ = lean_unsigned_to_nat(1u);
v_n_769_ = lean_nat_sub(v_x_742_, v_one_768_);
lean_dec(v_x_742_);
if (v_isSome_758_ == 0)
{
goto v___jp_777_;
}
else
{
lean_object* v___x_779_; uint8_t v_isSome_780_; 
v___x_779_ = lean_array_fget_borrowed(v_valueArray_756_, v_x_743_);
v_isSome_780_ = lean_noption_is_some(v___x_779_);
if (v_isSome_780_ == 0)
{
goto v___jp_777_;
}
else
{
lean_object* v_val_781_; uint8_t v___x_782_; 
lean_inc(v___x_757_);
v_val_781_ = lean_noption_get(v___x_757_);
v___x_782_ = lean_expr_eqv(v_val_781_, v_query_740_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
lean_dec(v_val_781_);
v___x_783_ = lean_array_get_size(v_keyArray_755_);
v___x_784_ = lean_nat_add(v_x_743_, v_one_768_);
lean_dec(v_x_743_);
v___x_785_ = lean_nat_dec_lt(v___x_784_, v___x_783_);
if (v___x_785_ == 0)
{
lean_dec(v___x_784_);
v_x_742_ = v_n_769_;
v_x_743_ = v_zero_744_;
goto _start;
}
else
{
v_x_742_ = v_n_769_;
v_x_743_ = v___x_784_;
goto _start;
}
}
else
{
lean_object* v_val_788_; lean_object* v___x_789_; 
lean_dec(v_n_769_);
lean_dec(v_x_741_);
lean_inc(v___x_779_);
v_val_788_ = lean_noption_get(v___x_779_);
v___x_789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_789_, 0, v_x_743_);
lean_ctor_set(v___x_789_, 1, v_val_781_);
lean_ctor_set(v___x_789_, 2, v_val_788_);
return v___x_789_;
}
}
}
v___jp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = lean_array_get_size(v_keyArray_755_);
v___x_773_ = lean_nat_add(v_x_743_, v_one_768_);
lean_dec(v_x_743_);
v___x_774_ = lean_nat_dec_lt(v___x_773_, v___x_772_);
if (v___x_774_ == 0)
{
lean_dec(v___x_773_);
v_x_741_ = v___y_771_;
v_x_742_ = v_n_769_;
v_x_743_ = v_zero_744_;
goto _start;
}
else
{
v_x_741_ = v___y_771_;
v_x_742_ = v_n_769_;
v_x_743_ = v___x_773_;
goto _start;
}
}
v___jp_777_:
{
if (lean_obj_tag(v_x_741_) == 0)
{
lean_object* v___x_778_; 
lean_inc(v_x_743_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_x_743_);
v___y_771_ = v___x_778_;
goto v___jp_770_;
}
else
{
v___y_771_ = v_x_741_;
goto v___jp_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_m_790_, lean_object* v_query_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_m_790_, v_query_791_, v_x_792_, v_x_793_, v_x_794_);
lean_dec_ref(v_query_791_);
lean_dec_ref(v_m_790_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_796_, lean_object* v_query_797_){
_start:
{
lean_object* v_keyArray_798_; lean_object* v___x_799_; uint64_t v___x_800_; uint64_t v___x_801_; uint64_t v___x_802_; uint64_t v_fold_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_keyArray_798_ = lean_ctor_get(v_m_796_, 1);
v___x_799_ = lean_array_get_size(v_keyArray_798_);
v___x_800_ = l_Lean_Expr_hash(v_query_797_);
v___x_801_ = 32ULL;
v___x_802_ = lean_uint64_shift_right(v___x_800_, v___x_801_);
v_fold_803_ = lean_uint64_xor(v___x_800_, v___x_802_);
v___x_804_ = 16ULL;
v___x_805_ = lean_uint64_shift_right(v_fold_803_, v___x_804_);
v___x_806_ = lean_uint64_xor(v_fold_803_, v___x_805_);
v___x_807_ = lean_uint64_to_usize(v___x_806_);
v___x_808_ = lean_usize_of_nat(v___x_799_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_sub(v___x_808_, v___x_809_);
v___x_811_ = lean_usize_land(v___x_807_, v___x_810_);
v___x_812_ = lean_usize_to_nat(v___x_811_);
v___x_813_ = lean_box(0);
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_m_796_, v_query_797_, v___x_813_, v___x_799_, v___x_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg___boxed(lean_object* v_m_815_, lean_object* v_query_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_815_, v_query_816_);
lean_dec_ref(v_query_816_);
lean_dec_ref(v_m_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___redArg(lean_object* v_b_818_, lean_object* v_acc_819_, lean_object* v_i_820_){
_start:
{
lean_object* v___y_822_; lean_object* v_keyArray_830_; lean_object* v_valueArray_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_keyArray_830_ = lean_ctor_get(v_b_818_, 1);
v_valueArray_831_ = lean_ctor_get(v_b_818_, 2);
v___x_832_ = lean_array_get_size(v_keyArray_830_);
v___x_833_ = lean_nat_dec_lt(v_i_820_, v___x_832_);
if (v___x_833_ == 0)
{
lean_dec(v_i_820_);
return v_acc_819_;
}
else
{
lean_object* v___x_834_; uint8_t v_isSome_835_; 
v___x_834_ = lean_array_fget_borrowed(v_keyArray_830_, v_i_820_);
v_isSome_835_ = lean_noption_is_some(v___x_834_);
if (v_isSome_835_ == 0)
{
goto v___jp_826_;
}
else
{
lean_object* v___x_836_; uint8_t v_isSome_837_; 
v___x_836_ = lean_array_fget_borrowed(v_valueArray_831_, v_i_820_);
v_isSome_837_ = lean_noption_is_some(v___x_836_);
if (v_isSome_837_ == 0)
{
goto v___jp_826_;
}
else
{
lean_object* v_val_838_; lean_object* v_val_839_; lean_object* v_i_841_; lean_object* v___x_846_; 
lean_inc(v___x_834_);
v_val_838_ = lean_noption_get(v___x_834_);
lean_inc(v___x_836_);
v_val_839_ = lean_noption_get(v___x_836_);
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_acc_819_, v_val_838_);
switch(lean_obj_tag(v___x_846_))
{
case 0:
{
lean_object* v_index_847_; lean_object* v_size_848_; lean_object* v___x_849_; 
v_index_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_index_847_);
lean_dec_ref_known(v___x_846_, 3);
v_size_848_ = lean_ctor_get(v_acc_819_, 0);
lean_inc(v_size_848_);
v___x_849_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_819_, v_size_848_, v_index_847_, v_val_838_, v_val_839_);
lean_dec(v_index_847_);
v___y_822_ = v___x_849_;
goto v___jp_821_;
}
case 1:
{
lean_object* v_index_850_; 
v_index_850_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_index_850_);
lean_dec_ref_known(v___x_846_, 1);
v_i_841_ = v_index_850_;
goto v___jp_840_;
}
default: 
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_819_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_index_853_; 
v_index_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_index_853_);
lean_dec_ref_known(v___x_852_, 1);
v_i_841_ = v_index_853_;
goto v___jp_840_;
}
else
{
lean_dec(v_val_839_);
lean_dec(v_val_838_);
v___y_822_ = v_acc_819_;
goto v___jp_821_;
}
}
}
v___jp_840_:
{
lean_object* v_size_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_size_842_ = lean_ctor_get(v_acc_819_, 0);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_add(v_size_842_, v___x_843_);
v___x_845_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_819_, v___x_844_, v_i_841_, v_val_838_, v_val_839_);
lean_dec(v_i_841_);
v___y_822_ = v___x_845_;
goto v___jp_821_;
}
}
}
}
v___jp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_i_820_, v___x_823_);
lean_dec(v_i_820_);
v_acc_819_ = v___y_822_;
v_i_820_ = v___x_824_;
goto _start;
}
v___jp_826_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_add(v_i_820_, v___x_827_);
lean_dec(v_i_820_);
v_i_820_ = v___x_828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_b_854_, lean_object* v_acc_855_, lean_object* v_i_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___redArg(v_b_854_, v_acc_855_, v_i_856_);
lean_dec_ref(v_b_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___redArg(lean_object* v_init_858_, lean_object* v_b_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___redArg(v_b_859_, v_init_858_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_init_862_, lean_object* v_b_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___redArg(v_init_862_, v_b_863_);
lean_dec_ref(v_b_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg(lean_object* v_m_865_){
_start:
{
lean_object* v_keyArray_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v_cellCount_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_target_873_; lean_object* v___x_874_; 
v_keyArray_866_ = lean_ctor_get(v_m_865_, 1);
v___x_867_ = lean_array_get_size(v_keyArray_866_);
v___x_868_ = lean_unsigned_to_nat(2u);
v_cellCount_869_ = lean_nat_mul(v___x_867_, v___x_868_);
v___x_870_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_869_);
v___x_871_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_869_);
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_869_);
v_target_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_873_, 0, v___x_870_);
lean_ctor_set(v_target_873_, 1, v___x_871_);
lean_ctor_set(v_target_873_, 2, v___x_872_);
v___x_874_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___redArg(v_target_873_, v_m_865_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg___boxed(lean_object* v_m_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg(v_m_875_);
lean_dec_ref(v_m_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__5(lean_object* v_as_877_, size_t v_sz_878_, size_t v_i_879_, lean_object* v_b_880_){
_start:
{
lean_object* v___y_882_; uint8_t v___x_886_; 
v___x_886_ = lean_usize_dec_lt(v_i_879_, v_sz_878_);
if (v___x_886_ == 0)
{
return v_b_880_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v___y_890_; lean_object* v_i_891_; lean_object* v___y_897_; lean_object* v___y_907_; lean_object* v_i_908_; lean_object* v___x_923_; 
v_a_887_ = lean_array_uget_borrowed(v_as_877_, v_i_879_);
v___x_888_ = lean_box(0);
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_880_, v_a_887_);
switch(lean_obj_tag(v___x_923_))
{
case 0:
{
lean_dec_ref_known(v___x_923_, 3);
v___y_882_ = v_b_880_;
goto v___jp_881_;
}
case 1:
{
lean_object* v_index_924_; lean_object* v_size_925_; lean_object* v_keyArray_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_index_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_index_924_);
lean_dec_ref_known(v___x_923_, 1);
v_size_925_ = lean_ctor_get(v_b_880_, 0);
v_keyArray_926_ = lean_ctor_get(v_b_880_, 1);
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_size_925_, v___x_927_);
v___x_929_ = lean_array_get_size(v_keyArray_926_);
v___x_930_ = lean_nat_dec_lt(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_dec(v___x_928_);
lean_dec(v_index_924_);
goto v___jp_913_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_931_ = lean_unsigned_to_nat(4u);
v___x_932_ = lean_nat_mul(v___x_928_, v___x_931_);
v___x_933_ = lean_unsigned_to_nat(3u);
v___x_934_ = lean_nat_mul(v___x_929_, v___x_933_);
v___x_935_ = lean_nat_dec_le(v___x_932_, v___x_934_);
lean_dec(v___x_934_);
lean_dec(v___x_932_);
if (v___x_935_ == 0)
{
lean_dec(v___x_928_);
lean_dec(v_index_924_);
goto v___jp_913_;
}
else
{
lean_object* v___x_936_; 
lean_inc(v_a_887_);
v___x_936_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_880_, v___x_928_, v_index_924_, v_a_887_, v___x_888_);
lean_dec(v_index_924_);
v___y_882_ = v___x_936_;
goto v___jp_881_;
}
}
}
default: 
{
lean_object* v_size_937_; lean_object* v_keyArray_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_size_937_ = lean_ctor_get(v_b_880_, 0);
v_keyArray_938_ = lean_ctor_get(v_b_880_, 1);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_size_937_, v___x_939_);
v___x_941_ = lean_array_get_size(v_keyArray_938_);
v___x_942_ = lean_nat_dec_lt(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v___x_940_);
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg(v_b_880_);
lean_dec_ref(v_b_880_);
v___y_897_ = v___x_943_;
goto v___jp_896_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_944_ = lean_unsigned_to_nat(4u);
v___x_945_ = lean_nat_mul(v___x_940_, v___x_944_);
lean_dec(v___x_940_);
v___x_946_ = lean_unsigned_to_nat(3u);
v___x_947_ = lean_nat_mul(v___x_941_, v___x_946_);
v___x_948_ = lean_nat_dec_le(v___x_945_, v___x_947_);
lean_dec(v___x_947_);
lean_dec(v___x_945_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg(v_b_880_);
lean_dec_ref(v_b_880_);
v___y_897_ = v___x_949_;
goto v___jp_896_;
}
else
{
v___y_897_ = v_b_880_;
goto v___jp_896_;
}
}
}
}
v___jp_889_:
{
lean_object* v_size_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_size_892_ = lean_ctor_get(v___y_890_, 0);
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_size_892_, v___x_893_);
lean_inc(v_a_887_);
v___x_895_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_890_, v___x_894_, v_i_891_, v_a_887_, v___x_888_);
lean_dec(v_i_891_);
v___y_882_ = v___x_895_;
goto v___jp_881_;
}
v___jp_896_:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v___y_897_, v_a_887_);
switch(lean_obj_tag(v___x_898_))
{
case 0:
{
lean_object* v_index_899_; lean_object* v_size_900_; lean_object* v___x_901_; 
v_index_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_index_899_);
lean_dec_ref_known(v___x_898_, 3);
v_size_900_ = lean_ctor_get(v___y_897_, 0);
lean_inc(v_size_900_);
lean_inc(v_a_887_);
v___x_901_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_897_, v_size_900_, v_index_899_, v_a_887_, v___x_888_);
lean_dec(v_index_899_);
v___y_882_ = v___x_901_;
goto v___jp_881_;
}
case 1:
{
lean_object* v_index_902_; 
v_index_902_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_index_902_);
lean_dec_ref_known(v___x_898_, 1);
v___y_890_ = v___y_897_;
v_i_891_ = v_index_902_;
goto v___jp_889_;
}
default: 
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_897_, v___x_903_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_index_905_; 
v_index_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_index_905_);
lean_dec_ref_known(v___x_904_, 1);
v___y_890_ = v___y_897_;
v_i_891_ = v_index_905_;
goto v___jp_889_;
}
else
{
v___y_882_ = v___y_897_;
goto v___jp_881_;
}
}
}
}
v___jp_906_:
{
lean_object* v_size_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_size_909_ = lean_ctor_get(v___y_907_, 0);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_add(v_size_909_, v___x_910_);
lean_inc(v_a_887_);
v___x_912_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_907_, v___x_911_, v_i_908_, v_a_887_, v___x_888_);
lean_dec(v_i_908_);
v___y_882_ = v___x_912_;
goto v___jp_881_;
}
v___jp_913_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg(v_b_880_);
lean_dec_ref(v_b_880_);
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v___x_914_, v_a_887_);
switch(lean_obj_tag(v___x_915_))
{
case 0:
{
lean_object* v_index_916_; lean_object* v_size_917_; lean_object* v___x_918_; 
v_index_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_index_916_);
lean_dec_ref_known(v___x_915_, 3);
v_size_917_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_size_917_);
lean_inc(v_a_887_);
v___x_918_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_914_, v_size_917_, v_index_916_, v_a_887_, v___x_888_);
lean_dec(v_index_916_);
v___y_882_ = v___x_918_;
goto v___jp_881_;
}
case 1:
{
lean_object* v_index_919_; 
v_index_919_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_index_919_);
lean_dec_ref_known(v___x_915_, 1);
v___y_907_ = v___x_914_;
v_i_908_ = v_index_919_;
goto v___jp_906_;
}
default: 
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_914_, v___x_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_index_922_; 
v_index_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_index_922_);
lean_dec_ref_known(v___x_921_, 1);
v___y_907_ = v___x_914_;
v_i_908_ = v_index_922_;
goto v___jp_906_;
}
else
{
v___y_882_ = v___x_914_;
goto v___jp_881_;
}
}
}
}
}
v___jp_881_:
{
size_t v___x_883_; size_t v___x_884_; 
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_add(v_i_879_, v___x_883_);
v_i_879_ = v___x_884_;
v_b_880_ = v___y_882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__5___boxed(lean_object* v_as_950_, lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_b_953_){
_start:
{
size_t v_sz_boxed_954_; size_t v_i_boxed_955_; lean_object* v_res_956_; 
v_sz_boxed_954_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_955_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__5(v_as_950_, v_sz_boxed_954_, v_i_boxed_955_, v_b_953_);
lean_dec_ref(v_as_950_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_957_, lean_object* v_l_958_){
_start:
{
size_t v_sz_959_; size_t v___x_960_; lean_object* v___x_961_; 
v_sz_959_ = lean_array_size(v_l_958_);
v___x_960_ = ((size_t)0ULL);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__5(v_l_958_, v_sz_959_, v___x_960_, v_m_957_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_962_, lean_object* v_l_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_962_, v_l_963_);
lean_dec_ref(v_l_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_dontRevert_965_, lean_object* v_as_966_, size_t v_i_967_, size_t v_stop_968_, lean_object* v_b_969_){
_start:
{
lean_object* v___y_971_; uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_eq(v_i_967_, v_stop_968_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_976_ = lean_array_uget_borrowed(v_as_966_, v_i_967_);
v___x_977_ = l_Lean_Expr_fvarId_x21(v___x_976_);
lean_inc_ref(v_dontRevert_965_);
v___x_978_ = lean_apply_1(v_dontRevert_965_, v___x_977_);
v___x_979_ = lean_unbox(v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_inc(v___x_976_);
v___x_980_ = lean_array_push(v_b_969_, v___x_976_);
v___y_971_ = v___x_980_;
goto v___jp_970_;
}
else
{
v___y_971_ = v_b_969_;
goto v___jp_970_;
}
}
else
{
lean_dec_ref(v_dontRevert_965_);
return v_b_969_;
}
v___jp_970_:
{
size_t v___x_972_; size_t v___x_973_; 
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_967_, v___x_972_);
v_i_967_ = v___x_973_;
v_b_969_ = v___y_971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_dontRevert_981_, lean_object* v_as_982_, lean_object* v_i_983_, lean_object* v_stop_984_, lean_object* v_b_985_){
_start:
{
size_t v_i_boxed_986_; size_t v_stop_boxed_987_; lean_object* v_res_988_; 
v_i_boxed_986_ = lean_unbox_usize(v_i_983_);
lean_dec(v_i_983_);
v_stop_boxed_987_ = lean_unbox_usize(v_stop_984_);
lean_dec(v_stop_984_);
v_res_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_981_, v_as_982_, v_i_boxed_986_, v_stop_boxed_987_, v_b_985_);
lean_dec_ref(v_as_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_989_, size_t v_i_990_, size_t v_stop_991_, lean_object* v_b_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_eq(v_i_990_, v_stop_991_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; size_t v___x_996_; size_t v___x_997_; 
v___x_994_ = lean_array_uget_borrowed(v_as_989_, v_i_990_);
lean_inc(v___x_994_);
v___x_995_ = l_Lean_collectFVars(v_b_992_, v___x_994_);
v___x_996_ = ((size_t)1ULL);
v___x_997_ = lean_usize_add(v_i_990_, v___x_996_);
v_i_990_ = v___x_997_;
v_b_992_ = v___x_995_;
goto _start;
}
else
{
return v_b_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_999_, lean_object* v_i_1000_, lean_object* v_stop_1001_, lean_object* v_b_1002_){
_start:
{
size_t v_i_boxed_1003_; size_t v_stop_boxed_1004_; lean_object* v_res_1005_; 
v_i_boxed_1003_ = lean_unbox_usize(v_i_1000_);
lean_dec(v_i_1000_);
v_stop_boxed_1004_ = lean_unbox_usize(v_stop_1001_);
lean_dec(v_stop_1001_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_999_, v_i_boxed_1003_, v_stop_boxed_1004_, v_b_1002_);
lean_dec_ref(v_as_999_);
return v_res_1005_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_1008_; lean_object* v___x_1009_; 
v_cellCount_1008_ = lean_unsigned_to_nat(16u);
v___x_1009_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_1010_; lean_object* v___x_1011_; 
v_cellCount_1010_ = lean_unsigned_to_nat(16u);
v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_1013_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_1013_);
lean_ctor_set(v___x_1015_, 2, v___x_1012_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object* v_dontRevert_1016_, lean_object* v_a_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = 0;
v___x_1024_ = 1;
lean_inc_ref(v_a_1017_);
v___x_1025_ = l_Lean_Meta_collectForwardDeps(v_a_1017_, v___x_1023_, v___x_1024_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1099_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1099_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1099_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; size_t v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___x_1044_; lean_object* v___x_1045_; size_t v___y_1047_; lean_object* v___y_1048_; lean_object* v_fvarIds_1049_; size_t v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1063_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_box(1);
v___x_1045_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1090_ = lean_array_get_size(v_a_1026_);
v___x_1091_ = lean_nat_dec_lt(v___x_1030_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_dec(v_a_1026_);
v___y_1063_ = v___x_1045_;
goto v___jp_1062_;
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = lean_nat_dec_le(v___x_1090_, v___x_1090_);
if (v___x_1092_ == 0)
{
if (v___x_1091_ == 0)
{
lean_dec(v_a_1026_);
v___y_1063_ = v___x_1045_;
goto v___jp_1062_;
}
else
{
size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = lean_usize_of_nat(v___x_1090_);
lean_inc_ref(v_dontRevert_1016_);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_1016_, v_a_1026_, v___x_1093_, v___x_1094_, v___x_1045_);
lean_dec(v_a_1026_);
v___y_1063_ = v___x_1095_;
goto v___jp_1062_;
}
}
else
{
size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = ((size_t)0ULL);
v___x_1097_ = lean_usize_of_nat(v___x_1090_);
lean_inc_ref(v_dontRevert_1016_);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_1016_, v_a_1026_, v___x_1096_, v___x_1097_, v___x_1045_);
lean_dec(v_a_1026_);
v___y_1063_ = v___x_1098_;
goto v___jp_1062_;
}
}
v___jp_1031_:
{
size_t v_sz_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_sz_1035_ = lean_array_size(v___y_1034_);
lean_inc_ref(v___y_1034_);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1035_, v___y_1032_, v___y_1034_);
v___x_1037_ = l_Array_append___redArg(v___y_1033_, v___x_1036_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = lean_array_get_size(v___y_1034_);
lean_dec_ref(v___y_1034_);
v___x_1039_ = lean_nat_dec_eq(v___x_1038_, v___x_1030_);
if (v___x_1039_ == 0)
{
lean_del_object(v___x_1028_);
v_a_1017_ = v___x_1037_;
goto _start;
}
else
{
lean_object* v___x_1042_; 
lean_dec_ref(v_dontRevert_1016_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1037_);
v___x_1042_ = v___x_1028_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
v___jp_1046_:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_array_get_size(v_fvarIds_1049_);
v___x_1051_ = lean_nat_dec_lt(v___x_1030_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v_fvarIds_1049_);
v___y_1032_ = v___y_1047_;
v___y_1033_ = v___y_1048_;
v___y_1034_ = v___x_1045_;
goto v___jp_1031_;
}
else
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_nat_dec_le(v___x_1050_, v___x_1050_);
if (v___x_1052_ == 0)
{
if (v___x_1051_ == 0)
{
lean_dec_ref(v_fvarIds_1049_);
v___y_1032_ = v___y_1047_;
v___y_1033_ = v___y_1048_;
v___y_1034_ = v___x_1045_;
goto v___jp_1031_;
}
else
{
size_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_usize_of_nat(v___x_1050_);
lean_inc_ref(v_dontRevert_1016_);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1016_, v_fvarIds_1049_, v___y_1047_, v___x_1053_, v___x_1045_);
lean_dec_ref(v_fvarIds_1049_);
v___y_1032_ = v___y_1047_;
v___y_1033_ = v___y_1048_;
v___y_1034_ = v___x_1054_;
goto v___jp_1031_;
}
}
else
{
size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_usize_of_nat(v___x_1050_);
lean_inc_ref(v_dontRevert_1016_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1016_, v_fvarIds_1049_, v___y_1047_, v___x_1055_, v___x_1045_);
lean_dec_ref(v_fvarIds_1049_);
v___y_1032_ = v___y_1047_;
v___y_1033_ = v___y_1048_;
v___y_1034_ = v___x_1056_;
goto v___jp_1031_;
}
}
}
v___jp_1057_:
{
lean_object* v_fvarIds_1061_; 
v_fvarIds_1061_ = lean_ctor_get(v___y_1060_, 2);
lean_inc_ref(v_fvarIds_1061_);
lean_dec_ref(v___y_1060_);
v___y_1047_ = v___y_1058_;
v___y_1048_ = v___y_1059_;
v_fvarIds_1049_ = v_fvarIds_1061_;
goto v___jp_1046_;
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_array_get_size(v___y_1063_);
v___x_1065_ = lean_array_get_size(v_a_1017_);
lean_dec_ref(v_a_1017_);
v___x_1066_ = lean_nat_dec_eq(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
size_t v_sz_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
v_sz_1067_ = lean_array_size(v___y_1063_);
v___x_1068_ = ((size_t)0ULL);
lean_inc_ref(v___y_1063_);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_1067_, v___x_1068_, v___y_1063_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1071_ = lean_array_get_size(v_a_1070_);
v___x_1072_ = lean_nat_dec_lt(v___x_1030_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec(v_a_1070_);
v___y_1047_ = v___x_1068_;
v___y_1048_ = v___y_1063_;
v_fvarIds_1049_ = v___x_1045_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1073_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3);
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_1073_, v___y_1063_);
v___x_1075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1044_);
lean_ctor_set(v___x_1075_, 2, v___x_1045_);
v___x_1076_ = lean_nat_dec_le(v___x_1071_, v___x_1071_);
if (v___x_1076_ == 0)
{
if (v___x_1072_ == 0)
{
lean_dec_ref_known(v___x_1075_, 3);
lean_dec(v_a_1070_);
v___y_1047_ = v___x_1068_;
v___y_1048_ = v___y_1063_;
v_fvarIds_1049_ = v___x_1045_;
goto v___jp_1046_;
}
else
{
size_t v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_usize_of_nat(v___x_1071_);
v___x_1078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_1070_, v___x_1068_, v___x_1077_, v___x_1075_);
lean_dec(v_a_1070_);
v___y_1058_ = v___x_1068_;
v___y_1059_ = v___y_1063_;
v___y_1060_ = v___x_1078_;
goto v___jp_1057_;
}
}
else
{
size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_usize_of_nat(v___x_1071_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_1070_, v___x_1068_, v___x_1079_, v___x_1075_);
lean_dec(v_a_1070_);
v___y_1058_ = v___x_1068_;
v___y_1059_ = v___y_1063_;
v___y_1060_ = v___x_1080_;
goto v___jp_1057_;
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v___y_1063_);
lean_del_object(v___x_1028_);
lean_dec_ref(v_dontRevert_1016_);
v_a_1081_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1069_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1069_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v___x_1089_; 
lean_del_object(v___x_1028_);
lean_dec_ref(v_dontRevert_1016_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___y_1063_);
return v___x_1089_;
}
}
}
}
else
{
lean_dec_ref(v_a_1017_);
lean_dec_ref(v_dontRevert_1016_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object* v_dontRevert_1100_, lean_object* v_a_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1100_, v_a_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1107_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1109_ = lean_box(1);
v___x_1110_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__3);
v___x_1111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1109_);
lean_ctor_set(v___x_1111_, 2, v___x_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_1112_, lean_object* v_dontRevert_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___y_1120_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_fvarIds_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1127_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_1128_ = l_Lean_collectFVars(v___x_1127_, v_e_1112_);
v_fvarIds_1129_ = lean_ctor_get(v___x_1128_, 2);
lean_inc_ref(v_fvarIds_1129_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = lean_array_get_size(v_fvarIds_1129_);
v___x_1131_ = lean_nat_dec_lt(v___x_1125_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_dec_ref(v_fvarIds_1129_);
v___y_1120_ = v___x_1126_;
goto v___jp_1119_;
}
else
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_nat_dec_le(v___x_1130_, v___x_1130_);
if (v___x_1132_ == 0)
{
if (v___x_1131_ == 0)
{
lean_dec_ref(v_fvarIds_1129_);
v___y_1120_ = v___x_1126_;
goto v___jp_1119_;
}
else
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = lean_usize_of_nat(v___x_1130_);
lean_inc_ref(v_dontRevert_1113_);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1113_, v_fvarIds_1129_, v___x_1133_, v___x_1134_, v___x_1126_);
lean_dec_ref(v_fvarIds_1129_);
v___y_1120_ = v___x_1135_;
goto v___jp_1119_;
}
}
else
{
size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = ((size_t)0ULL);
v___x_1137_ = lean_usize_of_nat(v___x_1130_);
lean_inc_ref(v_dontRevert_1113_);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1113_, v_fvarIds_1129_, v___x_1136_, v___x_1137_, v___x_1126_);
lean_dec_ref(v_fvarIds_1129_);
v___y_1120_ = v___x_1138_;
goto v___jp_1119_;
}
}
v___jp_1119_:
{
size_t v_sz_1121_; size_t v___x_1122_; lean_object* v_xs_1123_; lean_object* v___x_1124_; 
v_sz_1121_ = lean_array_size(v___y_1120_);
v___x_1122_ = ((size_t)0ULL);
v_xs_1123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1121_, v___x_1122_, v___y_1120_);
v___x_1124_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1113_, v_xs_1123_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1139_, lean_object* v_dontRevert_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1139_, v_dontRevert_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_1147_, lean_object* v_inst_1148_, lean_object* v_a_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1147_, v_a_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_1156_, lean_object* v_inst_1157_, lean_object* v_a_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1156_, v_inst_1157_, v_a_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1165_, lean_object* v_m_1166_, lean_object* v_query_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1166_, v_query_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1169_, lean_object* v_m_1170_, lean_object* v_query_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(v_00_u03b2_1169_, v_m_1170_, v_query_1171_);
lean_dec_ref(v_query_1171_);
lean_dec_ref(v_m_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_00_u03b2_1173_, lean_object* v_m_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___redArg(v_m_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1176_, lean_object* v_m_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_00_u03b2_1176_, v_m_1177_);
lean_dec_ref(v_m_1177_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1179_, lean_object* v_m_1180_, lean_object* v_query_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_m_1180_, v_query_1181_, v_x_1182_, v_x_1183_, v_x_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1187_, lean_object* v_m_1188_, lean_object* v_query_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1187_, v_m_1188_, v_query_1189_, v_x_1190_, v_x_1191_, v_x_1192_, v_x_1193_);
lean_dec_ref(v_query_1189_);
lean_dec_ref(v_m_1188_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1195_, lean_object* v_init_1196_, lean_object* v_b_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___redArg(v_init_1196_, v_b_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1199_, lean_object* v_init_1200_, lean_object* v_b_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6(v_00_u03b2_1199_, v_init_1200_, v_b_1201_);
lean_dec_ref(v_b_1201_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1203_, lean_object* v_b_1204_, lean_object* v_acc_1205_, lean_object* v_i_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___redArg(v_b_1204_, v_acc_1205_, v_i_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1208_, lean_object* v_b_1209_, lean_object* v_acc_1210_, lean_object* v_i_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4_spec__6_spec__10(v_00_u03b2_1208_, v_b_1209_, v_acc_1210_, v_i_1211_);
lean_dec_ref(v_b_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1219_, lean_object* v___x_1220_, lean_object* v___x_1221_, lean_object* v_i_1222_, lean_object* v_a_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_zero_1229_; uint8_t v_isZero_1230_; 
v_zero_1229_ = lean_unsigned_to_nat(0u);
v_isZero_1230_ = lean_nat_dec_eq(v_i_1222_, v_zero_1229_);
if (v_isZero_1230_ == 1)
{
lean_object* v___x_1231_; 
lean_dec(v_i_1222_);
lean_dec(v___x_1221_);
lean_dec_ref(v___x_1220_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_a_1223_);
return v___x_1231_;
}
else
{
lean_object* v_one_1232_; lean_object* v_n_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_one_1232_ = lean_unsigned_to_nat(1u);
v_n_1233_ = lean_nat_sub(v_i_1222_, v_one_1232_);
lean_dec(v_i_1222_);
v___x_1234_ = lean_array_fget_borrowed(v_a_1219_, v_n_1233_);
lean_inc_ref(v___x_1220_);
v___x_1235_ = l_Lean_LocalContext_getFVar_x21(v___x_1220_, v___x_1234_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_userName_1236_; lean_object* v_type_1237_; uint8_t v_bi_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_userName_1236_ = lean_ctor_get(v___x_1235_, 2);
lean_inc(v_userName_1236_);
v_type_1237_ = lean_ctor_get(v___x_1235_, 3);
lean_inc_ref(v_type_1237_);
v_bi_1238_ = lean_ctor_get_uint8(v___x_1235_, sizeof(void*)*4);
lean_dec_ref_known(v___x_1235_, 4);
v___x_1239_ = l_Lean_Expr_headBeta(v_type_1237_);
v___x_1240_ = lean_expr_abstract_range(v___x_1239_, v_n_1233_, v_a_1219_);
lean_dec_ref(v___x_1239_);
lean_inc_ref(v___x_1240_);
v___x_1241_ = l_Lean_Meta_getLevel(v___x_1240_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1244_ = lean_box(0);
lean_inc_n(v___x_1221_, 2);
v___x_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1221_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1242_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_Lean_mkConst(v___x_1243_, v___x_1246_);
v___x_1248_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1221_);
lean_inc_ref(v___x_1240_);
v___x_1249_ = l_Lean_mkLambda(v_userName_1236_, v_bi_1238_, v___x_1240_, v_a_1223_);
v___x_1250_ = l_Lean_mkApp3(v___x_1247_, v___x_1240_, v___x_1248_, v___x_1249_);
v_i_1222_ = v_n_1233_;
v_a_1223_ = v___x_1250_;
goto _start;
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v___x_1240_);
lean_dec(v_userName_1236_);
lean_dec(v_n_1233_);
lean_dec_ref(v_a_1223_);
lean_dec(v___x_1221_);
lean_dec_ref(v___x_1220_);
v_a_1252_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1241_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1241_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
else
{
uint8_t v_nondep_1260_; 
v_nondep_1260_ = lean_ctor_get_uint8(v___x_1235_, sizeof(void*)*5);
if (v_nondep_1260_ == 0)
{
lean_object* v_userName_1261_; lean_object* v_type_1262_; lean_object* v_value_1263_; uint8_t v___x_1264_; 
v_userName_1261_ = lean_ctor_get(v___x_1235_, 2);
lean_inc(v_userName_1261_);
v_type_1262_ = lean_ctor_get(v___x_1235_, 3);
lean_inc_ref(v_type_1262_);
v_value_1263_ = lean_ctor_get(v___x_1235_, 4);
lean_inc_ref(v_value_1263_);
lean_dec_ref_known(v___x_1235_, 5);
v___x_1264_ = lean_expr_has_loose_bvar(v_a_1223_, v_zero_1229_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref(v_value_1263_);
lean_dec_ref(v_type_1262_);
lean_dec(v_userName_1261_);
v___x_1265_ = lean_expr_lower_loose_bvars(v_a_1223_, v_one_1232_, v_one_1232_);
lean_dec_ref(v_a_1223_);
v_i_1222_ = v_n_1233_;
v_a_1223_ = v___x_1265_;
goto _start;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = l_Lean_Expr_headBeta(v_type_1262_);
v___x_1268_ = lean_expr_abstract_range(v___x_1267_, v_n_1233_, v_a_1219_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = lean_expr_abstract_range(v_value_1263_, v_n_1233_, v_a_1219_);
lean_dec_ref(v_value_1263_);
v___x_1270_ = l_Lean_Expr_letE___override(v_userName_1261_, v___x_1268_, v___x_1269_, v_a_1223_, v_nondep_1260_);
v_i_1222_ = v_n_1233_;
v_a_1223_ = v___x_1270_;
goto _start;
}
}
else
{
lean_object* v_userName_1272_; lean_object* v_type_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_userName_1272_ = lean_ctor_get(v___x_1235_, 2);
lean_inc(v_userName_1272_);
v_type_1273_ = lean_ctor_get(v___x_1235_, 3);
lean_inc_ref(v_type_1273_);
lean_dec_ref_known(v___x_1235_, 5);
v___x_1274_ = l_Lean_Expr_headBeta(v_type_1273_);
v___x_1275_ = lean_expr_abstract_range(v___x_1274_, v_n_1233_, v_a_1219_);
lean_dec_ref(v___x_1274_);
lean_inc_ref(v___x_1275_);
v___x_1276_ = l_Lean_Meta_getLevel(v___x_1275_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1279_ = lean_box(0);
lean_inc_n(v___x_1221_, 2);
v___x_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1221_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1281_, 0, v_a_1277_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_mkConst(v___x_1278_, v___x_1281_);
v___x_1283_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1221_);
v___x_1284_ = 0;
lean_inc_ref(v___x_1275_);
v___x_1285_ = l_Lean_mkLambda(v_userName_1272_, v___x_1284_, v___x_1275_, v_a_1223_);
v___x_1286_ = l_Lean_mkApp3(v___x_1282_, v___x_1275_, v___x_1283_, v___x_1285_);
v_i_1222_ = v_n_1233_;
v_a_1223_ = v___x_1286_;
goto _start;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v___x_1275_);
lean_dec(v_userName_1272_);
lean_dec(v_n_1233_);
lean_dec_ref(v_a_1223_);
lean_dec(v___x_1221_);
lean_dec_ref(v___x_1220_);
v_a_1288_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1276_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1276_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1296_, lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v_i_1299_, lean_object* v_a_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1296_, v___x_1297_, v___x_1298_, v_i_1299_, v_a_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec_ref(v_a_1296_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1311_, lean_object* v_dontRevert_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1318_; 
lean_inc_ref(v_e_1311_);
v___x_1318_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1311_, v_dontRevert_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v_lctx_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v_lctx_1320_ = lean_ctor_get(v_a_1313_, 2);
lean_inc(v_a_1316_);
lean_inc_ref(v_a_1315_);
lean_inc(v_a_1314_);
lean_inc_ref(v_a_1313_);
lean_inc_ref(v_e_1311_);
v___x_1321_ = lean_infer_type(v_e_1311_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1344_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1344_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1344_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = l_Lean_Expr_cleanupAnnotations(v_a_1322_);
v___x_1327_ = l_Lean_Expr_isApp(v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1329_; 
lean_dec_ref(v___x_1326_);
lean_dec(v_a_1319_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_e_1311_);
v___x_1329_ = v___x_1324_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_e_1311_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1326_);
v___x_1332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1333_ = l_Lean_Expr_isConstOf(v___x_1331_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1335_; 
lean_dec_ref(v___x_1331_);
lean_dec(v_a_1319_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_e_1311_);
v___x_1335_ = v___x_1324_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_e_1311_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1324_);
v___x_1337_ = lean_box(0);
v___x_1338_ = l_Lean_Expr_constLevels_x21(v___x_1331_);
lean_dec_ref(v___x_1331_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = l_List_get_x21Internal___redArg(v___x_1337_, v___x_1338_, v___x_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_array_get_size(v_a_1319_);
v___x_1342_ = lean_expr_abstract(v_e_1311_, v_a_1319_);
lean_dec_ref(v_e_1311_);
lean_inc_ref(v_lctx_1320_);
v___x_1343_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1319_, v_lctx_1320_, v___x_1340_, v___x_1341_, v___x_1342_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1319_);
return v___x_1343_;
}
}
}
}
else
{
lean_dec(v_a_1319_);
lean_dec_ref(v_e_1311_);
return v___x_1321_;
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_e_1311_);
v_a_1345_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1318_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1318_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1353_, lean_object* v_dontRevert_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1353_, v_dontRevert_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1361_, lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v_n_1364_, lean_object* v_i_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1361_, v___x_1362_, v___x_1363_, v_i_1365_, v_a_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1374_, lean_object* v___x_1375_, lean_object* v___x_1376_, lean_object* v_n_1377_, lean_object* v_i_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1374_, v___x_1375_, v___x_1376_, v_n_1377_, v_i_1378_, v_a_1379_, v_a_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v_n_1377_);
lean_dec_ref(v_a_1374_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1393_, lean_object* v_lhs_1394_, lean_object* v_rhs_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1397_ = lean_box(0);
lean_inc(v_lvl_1393_);
v___x_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_lvl_1393_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = l_Lean_mkConst(v___x_1396_, v___x_1398_);
v___x_1400_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1393_);
v___x_1401_ = l_Lean_mkApp3(v___x_1399_, v___x_1400_, v_lhs_1394_, v_rhs_1395_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1408_, lean_object* v_lhs_1409_, lean_object* v_rhs_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1412_ = lean_box(0);
lean_inc(v_lvl_1408_);
v___x_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1413_, 0, v_lvl_1408_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_mkConst(v___x_1411_, v___x_1413_);
v___x_1415_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1408_);
v___x_1416_ = l_Lean_mkApp3(v___x_1414_, v___x_1415_, v_lhs_1409_, v_rhs_1410_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1417_){
_start:
{
lean_object* v_lvl_1418_; lean_object* v_cursorPred_1419_; lean_object* v_letMutsPred_1420_; lean_object* v___x_1421_; 
v_lvl_1418_ = lean_ctor_get(v_p_1417_, 0);
lean_inc(v_lvl_1418_);
v_cursorPred_1419_ = lean_ctor_get(v_p_1417_, 1);
lean_inc_ref(v_cursorPred_1419_);
v_letMutsPred_1420_ = lean_ctor_get(v_p_1417_, 2);
lean_inc_ref(v_letMutsPred_1420_);
lean_dec_ref(v_p_1417_);
v___x_1421_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1418_, v_cursorPred_1419_, v_letMutsPred_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(lean_object* v_x_1422_){
_start:
{
switch(lean_obj_tag(v_x_1422_))
{
case 0:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
return v___x_1423_;
}
case 1:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_unsigned_to_nat(1u);
return v___x_1424_;
}
case 2:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_unsigned_to_nat(2u);
return v___x_1425_;
}
default: 
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_unsigned_to_nat(3u);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___boxed(lean_object* v_x_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(v_x_1427_);
lean_dec(v_x_1427_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1429_, lean_object* v_k_1430_){
_start:
{
if (lean_obj_tag(v_t_1429_) == 3)
{
lean_object* v_e_1431_; lean_object* v___x_1432_; 
v_e_1431_ = lean_ctor_get(v_t_1429_, 0);
lean_inc_ref(v_e_1431_);
lean_dec_ref_known(v_t_1429_, 1);
v___x_1432_ = lean_apply_1(v_k_1430_, v_e_1431_);
return v___x_1432_;
}
else
{
lean_dec(v_t_1429_);
return v_k_1430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1433_, lean_object* v_ctorIdx_1434_, lean_object* v_t_1435_, lean_object* v_h_1436_, lean_object* v_k_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1435_, v_k_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1439_, lean_object* v_ctorIdx_1440_, lean_object* v_t_1441_, lean_object* v_h_1442_, lean_object* v_k_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1439_, v_ctorIdx_1440_, v_t_1441_, v_h_1442_, v_k_1443_);
lean_dec(v_ctorIdx_1440_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1445_, lean_object* v_punit_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1445_, v_punit_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1448_, lean_object* v_t_1449_, lean_object* v_h_1450_, lean_object* v_punit_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1449_, v_punit_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1453_, lean_object* v_false_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1453_, v_false_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1456_, lean_object* v_t_1457_, lean_object* v_h_1458_, lean_object* v_false_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1457_, v_false_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1461_, lean_object* v_true_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1461_, v_true_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1464_, lean_object* v_t_1465_, lean_object* v_h_1466_, lean_object* v_true_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1465_, v_true_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1469_, lean_object* v_other_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1469_, v_other_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1472_, lean_object* v_t_1473_, lean_object* v_h_1474_, lean_object* v_other_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1473_, v_other_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1477_){
_start:
{
lean_object* v_snd_1479_; lean_object* v_fst_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1519_; 
v_snd_1479_ = lean_ctor_get(v_a_1477_, 1);
v_fst_1480_ = lean_ctor_get(v_a_1477_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_a_1477_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1482_ = v_a_1477_;
v_isShared_1483_ = v_isSharedCheck_1519_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snd_1479_);
lean_inc(v_fst_1480_);
lean_dec(v_a_1477_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1519_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1518_; 
v_fst_1484_ = lean_ctor_get(v_snd_1479_, 0);
v_snd_1485_ = lean_ctor_get(v_snd_1479_, 1);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_snd_1479_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1487_ = v_snd_1479_;
v_isShared_1488_ = v_isSharedCheck_1518_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_snd_1485_);
lean_inc(v_fst_1484_);
lean_dec(v_snd_1479_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1518_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1489_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1490_ = lean_unsigned_to_nat(4u);
v___x_1491_ = l_Lean_Expr_isAppOfArity(v_fst_1484_, v___x_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1493_; 
if (v_isShared_1488_ == 0)
{
v___x_1493_ = v___x_1487_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_fst_1484_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_snd_1485_);
v___x_1493_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1493_);
v___x_1495_ = v___x_1482_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_fst_1480_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1499_ = lean_unsigned_to_nat(3u);
v___x_1500_ = lean_unsigned_to_nat(2u);
v___x_1501_ = l_Lean_Expr_getAppNumArgs(v_fst_1484_);
v___x_1502_ = lean_nat_sub(v___x_1501_, v___x_1500_);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_sub(v___x_1502_, v___x_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = l_Lean_Expr_getRevArg_x21(v_fst_1484_, v___x_1504_);
v___x_1506_ = lean_array_push(v_snd_1485_, v___x_1505_);
v___x_1507_ = lean_nat_add(v_fst_1480_, v___x_1503_);
lean_dec(v_fst_1480_);
v___x_1508_ = lean_nat_sub(v___x_1501_, v___x_1499_);
lean_dec(v___x_1501_);
v___x_1509_ = lean_nat_sub(v___x_1508_, v___x_1503_);
lean_dec(v___x_1508_);
v___x_1510_ = l_Lean_Expr_getRevArg_x21(v_fst_1484_, v___x_1509_);
lean_dec(v_fst_1484_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1506_);
lean_ctor_set(v___x_1487_, 0, v___x_1510_);
v___x_1512_ = v___x_1487_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1506_);
v___x_1512_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1512_);
lean_ctor_set(v___x_1482_, 0, v___x_1507_);
v___x_1514_ = v___x_1482_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
v_a_1477_ = v___x_1514_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1520_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_fst_1523_, lean_object* v_p_1524_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_inc(v_fst_1523_);
v___x_1525_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1523_);
v___x_1526_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1523_, v___x_1525_, v_p_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_letMutsTuple_1527_, lean_object* v___x_1528_, uint8_t v___x_1529_, lean_object* v_fvarId_1530_){
_start:
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1527_);
v___x_1532_ = l_Lean_instBEqFVarId_beq(v_fvarId_1530_, v___x_1531_);
lean_dec(v___x_1531_);
if (v___x_1532_ == 0)
{
uint8_t v___x_1533_; 
v___x_1533_ = l_Lean_LocalContext_contains(v___x_1528_, v_fvarId_1530_);
return v___x_1533_;
}
else
{
return v___x_1529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1534_, lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v_fvarId_1537_){
_start:
{
uint8_t v___x_11385__boxed_1538_; uint8_t v_res_1539_; lean_object* v_r_1540_; 
v___x_11385__boxed_1538_ = lean_unbox(v___x_1536_);
v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1534_, v___x_1535_, v___x_11385__boxed_1538_, v_fvarId_1537_);
lean_dec(v_fvarId_1537_);
lean_dec_ref(v___x_1535_);
lean_dec_ref(v_letMutsTuple_1534_);
v_r_1540_ = lean_box(v_res_1539_);
return v_r_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1560_, lean_object* v___x_1561_, lean_object* v_xs_1562_, lean_object* v_letMuts_1563_, lean_object* v_as_1564_, size_t v_sz_1565_, size_t v_i_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_a_1574_; uint8_t v___x_1578_; 
v___x_1578_ = lean_usize_dec_lt(v_i_1566_, v_sz_1565_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v_b_1567_);
return v___x_1579_;
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_array_uget_borrowed(v_as_1564_, v_i_1566_);
lean_inc(v_a_1580_);
v___x_1581_ = l_Lean_MVarId_getType(v_a_1580_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_snd_1582_; lean_object* v_a_1583_; lean_object* v_fst_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1926_; 
v_snd_1582_ = lean_ctor_get(v_b_1567_, 1);
lean_inc(v_snd_1582_);
v_a_1583_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1581_, 1);
v_fst_1584_ = lean_ctor_get(v_b_1567_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_b_1567_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v_b_1567_, 1);
lean_dec(v_unused_1927_);
v___x_1586_ = v_b_1567_;
v_isShared_1587_ = v_isSharedCheck_1926_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_fst_1584_);
lean_dec(v_b_1567_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1926_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_fst_1588_; lean_object* v_snd_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1925_; 
v_fst_1588_ = lean_ctor_get(v_snd_1582_, 0);
v_snd_1589_ = lean_ctor_get(v_snd_1582_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_snd_1582_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1591_ = v_snd_1582_;
v_isShared_1592_ = v_isSharedCheck_1925_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_snd_1589_);
lean_inc(v_fst_1588_);
lean_dec(v_snd_1582_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1925_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; uint8_t v___y_1607_; lean_object* v___y_1707_; lean_object* v_prefixPoint_x3f_1708_; lean_object* v_suffixPoint_x3f_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; uint8_t v___y_1748_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v_prefixPoint_x3f_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v_a_1835_; lean_object* v_a_1840_; lean_object* v___x_1913_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1595_ = lean_box(0);
v___x_1913_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1583_, v___y_1569_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l_Lean_Expr_consumeMData(v_a_1914_);
lean_dec(v_a_1914_);
v_a_1840_ = v___x_1915_;
goto v___jp_1839_;
}
else
{
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1916_; 
v_a_1916_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1913_, 1);
v_a_1840_ = v_a_1916_;
goto v___jp_1839_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_del_object(v___x_1586_);
lean_dec(v_fst_1584_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1917_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1913_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1913_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
v___jp_1596_:
{
if (v___y_1607_ == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref(v___y_1603_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___y_1601_);
v___x_1609_ = v___x_1591_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___y_1601_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_snd_1589_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v___x_1609_);
lean_ctor_set(v___x_1586_, 0, v___y_1598_);
v___x_1611_ = v___x_1586_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___y_1598_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
v_a_1574_ = v___x_1611_;
goto v___jp_1573_;
}
}
}
else
{
lean_object* v___x_1615_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 1, v___x_1594_);
lean_ctor_set(v___x_1591_, 0, v___y_1603_);
v___x_1615_ = v___x_1591_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___y_1603_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1594_);
v___x_1615_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1617_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v___x_1615_);
lean_ctor_set(v___x_1586_, 0, v___x_1593_);
v___x_1617_ = v___x_1586_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1617_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v_snd_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1694_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v_snd_1620_ = lean_ctor_get(v_a_1619_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_a_1619_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v_a_1619_, 0);
lean_dec(v_unused_1695_);
v___x_1622_ = v_a_1619_;
v_isShared_1623_ = v_isSharedCheck_1694_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_snd_1620_);
lean_dec(v_a_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1694_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v_fst_1624_; lean_object* v_snd_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1693_; 
v_fst_1624_ = lean_ctor_get(v_snd_1620_, 0);
v_snd_1625_ = lean_ctor_get(v_snd_1620_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_snd_1620_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1627_ = v_snd_1620_;
v_isShared_1628_ = v_isSharedCheck_1693_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_snd_1625_);
lean_inc(v_fst_1624_);
lean_dec(v_snd_1620_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1693_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_points_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v_points_1629_ = lean_ctor_get(v_snd_1589_, 0);
v___x_1630_ = lean_array_get_size(v_points_1629_);
v___x_1631_ = lean_array_get_size(v_snd_1625_);
v___x_1632_ = lean_nat_dec_lt(v___x_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v_snd_1625_);
lean_dec(v_fst_1624_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v_snd_1589_);
lean_ctor_set(v___x_1627_, 0, v___y_1601_);
v___x_1634_ = v___x_1627_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___y_1601_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_snd_1589_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1634_);
lean_ctor_set(v___x_1622_, 0, v___y_1598_);
v___x_1636_ = v___x_1622_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___y_1598_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
v_a_1574_ = v___x_1636_;
goto v___jp_1573_;
}
}
}
else
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1690_; 
v_isSharedCheck_1690_ = !lean_is_exclusive(v_snd_1589_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; lean_object* v_unused_1692_; 
v_unused_1691_ = lean_ctor_get(v_snd_1589_, 1);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_snd_1589_, 0);
lean_dec(v_unused_1692_);
v___x_1640_ = v_snd_1589_;
v_isShared_1641_ = v_isSharedCheck_1690_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_snd_1589_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1690_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2));
v___x_1643_ = l_Lean_Expr_isConstOf(v_fst_1624_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3));
lean_inc_ref(v___y_1602_);
lean_inc_ref(v___y_1604_);
lean_inc_ref(v___y_1606_);
v___x_1645_ = l_Lean_Name_mkStr4(v___y_1606_, v___y_1604_, v___y_1602_, v___x_1644_);
v___x_1646_ = lean_unsigned_to_nat(1u);
v___x_1647_ = l_Lean_Expr_isAppOfArity(v_fst_1624_, v___x_1645_, v___x_1646_);
lean_dec(v___x_1645_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
lean_inc_ref(v___y_1602_);
lean_inc_ref(v___y_1604_);
lean_inc_ref(v___y_1606_);
v___x_1649_ = l_Lean_Name_mkStr4(v___y_1606_, v___y_1604_, v___y_1602_, v___x_1648_);
v___x_1650_ = l_Lean_Expr_isAppOfArity(v_fst_1624_, v___x_1649_, v___x_1646_);
lean_dec(v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_fst_1624_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___x_1651_);
lean_ctor_set(v___x_1640_, 0, v_snd_1625_);
v___x_1653_ = v___x_1640_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_snd_1625_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1653_);
lean_ctor_set(v___x_1627_, 0, v___y_1601_);
v___x_1655_ = v___x_1627_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___y_1601_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1657_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1655_);
lean_ctor_set(v___x_1622_, 0, v___y_1598_);
v___x_1657_ = v___x_1622_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___y_1598_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
v_a_1574_ = v___x_1657_;
goto v___jp_1573_;
}
}
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_fst_1624_);
v___x_1661_ = lean_box(2);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___x_1661_);
lean_ctor_set(v___x_1640_, 0, v_snd_1625_);
v___x_1663_ = v___x_1640_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_snd_1625_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1663_);
lean_ctor_set(v___x_1627_, 0, v___y_1601_);
v___x_1665_ = v___x_1627_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___y_1601_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1665_);
lean_ctor_set(v___x_1622_, 0, v___y_1598_);
v___x_1667_ = v___x_1622_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___y_1598_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
v_a_1574_ = v___x_1667_;
goto v___jp_1573_;
}
}
}
}
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
lean_dec(v_fst_1624_);
v___x_1671_ = lean_box(1);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___x_1671_);
lean_ctor_set(v___x_1640_, 0, v_snd_1625_);
v___x_1673_ = v___x_1640_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_snd_1625_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1673_);
lean_ctor_set(v___x_1627_, 0, v___y_1601_);
v___x_1675_ = v___x_1627_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___y_1601_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1675_);
lean_ctor_set(v___x_1622_, 0, v___y_1598_);
v___x_1677_ = v___x_1622_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___y_1598_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
v_a_1574_ = v___x_1677_;
goto v___jp_1573_;
}
}
}
}
}
else
{
lean_object* v___x_1682_; 
lean_dec(v_fst_1624_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___x_1595_);
lean_ctor_set(v___x_1640_, 0, v_snd_1625_);
v___x_1682_ = v___x_1640_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_snd_1625_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1595_);
v___x_1682_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1684_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1682_);
lean_ctor_set(v___x_1627_, 0, v___y_1601_);
v___x_1684_ = v___x_1627_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___y_1601_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1686_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1684_);
lean_ctor_set(v___x_1622_, 0, v___y_1598_);
v___x_1686_ = v___x_1622_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___y_1598_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
v_a_1574_ = v___x_1686_;
goto v___jp_1573_;
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
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v___y_1601_);
lean_dec(v___y_1598_);
lean_dec(v_snd_1589_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1696_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1618_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1618_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
}
v___jp_1706_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_1715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_1716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_1717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1718_ = lean_unsigned_to_nat(3u);
v___x_1719_ = l_Lean_Expr_isAppOfArity(v___y_1707_, v___x_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec_ref(v___y_1707_);
lean_del_object(v___x_1591_);
lean_del_object(v___x_1586_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_suffixPoint_x3f_1709_);
lean_ctor_set(v___x_1720_, 1, v_snd_1589_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_prefixPoint_x3f_1708_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v_a_1574_ = v___x_1721_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1722_ = l_Lean_Expr_appFn_x21(v___y_1707_);
v___x_1723_ = l_Lean_Expr_appArg_x21(v___x_1722_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = l_Lean_Expr_appArg_x21(v___y_1707_);
lean_dec_ref(v___y_1707_);
v___x_1725_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1726_ = l_Lean_Expr_isAppOfArity(v___x_1723_, v___x_1725_, v___x_1718_);
if (v___x_1726_ == 0)
{
lean_dec_ref(v___x_1723_);
v___y_1597_ = v___y_1712_;
v___y_1598_ = v_prefixPoint_x3f_1708_;
v___y_1599_ = v___y_1710_;
v___y_1600_ = v___y_1711_;
v___y_1601_ = v_suffixPoint_x3f_1709_;
v___y_1602_ = v___x_1716_;
v___y_1603_ = v___x_1724_;
v___y_1604_ = v___x_1715_;
v___y_1605_ = v___y_1713_;
v___y_1606_ = v___x_1714_;
v___y_1607_ = v___x_1726_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1727_ = lean_unsigned_to_nat(2u);
v___x_1728_ = l_Lean_Expr_getAppNumArgs(v___x_1723_);
v___x_1729_ = lean_nat_sub(v___x_1728_, v___x_1727_);
lean_dec(v___x_1728_);
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_sub(v___x_1729_, v___x_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = l_Lean_Expr_getRevArg_x21(v___x_1723_, v___x_1731_);
lean_dec_ref(v___x_1723_);
lean_inc(v_inv_1560_);
v___x_1733_ = l_Lean_mkMVar(v_inv_1560_);
v___x_1734_ = lean_expr_eqv(v___x_1732_, v___x_1733_);
lean_dec_ref(v___x_1733_);
lean_dec_ref(v___x_1732_);
v___y_1597_ = v___y_1712_;
v___y_1598_ = v_prefixPoint_x3f_1708_;
v___y_1599_ = v___y_1710_;
v___y_1600_ = v___y_1711_;
v___y_1601_ = v_suffixPoint_x3f_1709_;
v___y_1602_ = v___x_1716_;
v___y_1603_ = v___x_1724_;
v___y_1604_ = v___x_1715_;
v___y_1605_ = v___y_1713_;
v___y_1606_ = v___x_1714_;
v___y_1607_ = v___x_1734_;
goto v___jp_1596_;
}
}
}
v___jp_1735_:
{
if (v___y_1748_ == 0)
{
lean_dec_ref(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1737_);
v___y_1707_ = v___y_1738_;
v_prefixPoint_x3f_1708_ = v___y_1744_;
v_suffixPoint_x3f_1709_ = v_fst_1588_;
v___y_1710_ = v___y_1741_;
v___y_1711_ = v___y_1736_;
v___y_1712_ = v___y_1745_;
v___y_1713_ = v___y_1742_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc_ref(v_xs_1562_);
v___x_1750_ = l_Lean_Meta_mkProjection(v_xs_1562_, v___x_1749_, v___y_1741_, v___y_1736_, v___y_1745_, v___y_1742_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = l_Lean_Meta_mkEq(v_a_1751_, v___y_1737_, v___y_1741_, v___y_1736_, v___y_1745_, v___y_1742_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1754_, 0, v___y_1747_);
lean_closure_set(v___x_1754_, 1, v___y_1746_);
lean_inc(v_a_1580_);
v___x_1755_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1580_, v___x_1754_, v___y_1741_, v___y_1736_, v___y_1745_, v___y_1742_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v___x_1757_ = l_Lean_Expr_replaceFVar(v_a_1756_, v___y_1743_, v_letMuts_1563_);
lean_dec(v_a_1756_);
if (lean_obj_tag(v_fst_1588_) == 1)
{
lean_object* v_val_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1753_);
lean_dec_ref(v___y_1739_);
v_val_1758_ = lean_ctor_get(v_fst_1588_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_fst_1588_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1760_ = v_fst_1588_;
v_isShared_1761_ = v_isSharedCheck_1776_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_val_1758_);
lean_dec(v_fst_1588_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1776_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_lvl_1762_; lean_object* v_cursorPred_1763_; lean_object* v_letMutsPred_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1775_; 
v_lvl_1762_ = lean_ctor_get(v_val_1758_, 0);
v_cursorPred_1763_ = lean_ctor_get(v_val_1758_, 1);
v_letMutsPred_1764_ = lean_ctor_get(v_val_1758_, 2);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_val_1758_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1766_ = v_val_1758_;
v_isShared_1767_ = v_isSharedCheck_1775_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_letMutsPred_1764_);
lean_inc(v_cursorPred_1763_);
lean_inc(v_lvl_1762_);
lean_dec(v_val_1758_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1775_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1740_, v_letMutsPred_1764_, v___x_1757_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 2, v___x_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_lvl_1762_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_cursorPred_1763_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1770_);
v___x_1772_ = v___x_1760_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
v___y_1707_ = v___y_1738_;
v_prefixPoint_x3f_1708_ = v___y_1744_;
v_suffixPoint_x3f_1709_ = v___x_1772_;
v___y_1710_ = v___y_1741_;
v___y_1711_ = v___y_1736_;
v___y_1712_ = v___y_1745_;
v___y_1713_ = v___y_1742_;
goto v___jp_1706_;
}
}
}
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v_fst_1588_);
v___x_1777_ = lean_apply_1(v___y_1739_, v_a_1753_);
v___x_1778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1740_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
lean_ctor_set(v___x_1778_, 2, v___x_1757_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
v___y_1707_ = v___y_1738_;
v_prefixPoint_x3f_1708_ = v___y_1744_;
v_suffixPoint_x3f_1709_ = v___x_1779_;
v___y_1710_ = v___y_1741_;
v___y_1711_ = v___y_1736_;
v___y_1712_ = v___y_1745_;
v___y_1713_ = v___y_1742_;
goto v___jp_1706_;
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_a_1753_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1780_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1755_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1755_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1788_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1752_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1752_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1796_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1750_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1750_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
v___jp_1804_:
{
lean_object* v___x_1815_; 
lean_inc(v_inv_1560_);
v___x_1815_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v___y_1806_, v_inv_1560_);
lean_dec_ref(v___y_1806_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_invariantUse_1816_; lean_object* v_conditionIdx_1817_; lean_object* v_cursorSuffix_1818_; lean_object* v_letMutsTuple_1819_; uint8_t v___x_1820_; 
v_invariantUse_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc_ref(v_invariantUse_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v_conditionIdx_1817_ = lean_ctor_get(v_invariantUse_1816_, 0);
lean_inc(v_conditionIdx_1817_);
v_cursorSuffix_1818_ = lean_ctor_get(v_invariantUse_1816_, 2);
lean_inc_ref(v_cursorSuffix_1818_);
v_letMutsTuple_1819_ = lean_ctor_get(v_invariantUse_1816_, 4);
lean_inc_ref(v_letMutsTuple_1819_);
lean_dec_ref(v_invariantUse_1816_);
v___x_1820_ = lean_nat_dec_eq(v_conditionIdx_1817_, v___x_1593_);
lean_dec(v_conditionIdx_1817_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v_letMutsTuple_1819_);
lean_dec_ref(v_cursorSuffix_1818_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1805_);
lean_del_object(v___x_1591_);
lean_del_object(v___x_1586_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v_fst_1588_);
lean_ctor_set(v___x_1821_, 1, v_snd_1589_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v_prefixPoint_x3f_1810_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v_a_1574_ = v___x_1822_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1823_ = lean_box(v___x_1820_);
lean_inc_ref(v___x_1561_);
lean_inc_ref(v_letMutsTuple_1819_);
v___f_1824_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1824_, 0, v_letMutsTuple_1819_);
lean_closure_set(v___f_1824_, 1, v___x_1561_);
lean_closure_set(v___f_1824_, 2, v___x_1823_);
v___x_1825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_1826_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1818_, v___x_1825_);
if (v___x_1826_ == 0)
{
v___y_1736_ = v___y_1812_;
v___y_1737_ = v_cursorSuffix_1818_;
v___y_1738_ = v___y_1807_;
v___y_1739_ = v___y_1808_;
v___y_1740_ = v___y_1805_;
v___y_1741_ = v___y_1811_;
v___y_1742_ = v___y_1814_;
v___y_1743_ = v_letMutsTuple_1819_;
v___y_1744_ = v_prefixPoint_x3f_1810_;
v___y_1745_ = v___y_1813_;
v___y_1746_ = v___f_1824_;
v___y_1747_ = v___y_1809_;
v___y_1748_ = v___x_1826_;
goto v___jp_1735_;
}
else
{
uint8_t v___x_1827_; 
v___x_1827_ = l_Lean_Expr_isFVar(v_letMutsTuple_1819_);
v___y_1736_ = v___y_1812_;
v___y_1737_ = v_cursorSuffix_1818_;
v___y_1738_ = v___y_1807_;
v___y_1739_ = v___y_1808_;
v___y_1740_ = v___y_1805_;
v___y_1741_ = v___y_1811_;
v___y_1742_ = v___y_1814_;
v___y_1743_ = v_letMutsTuple_1819_;
v___y_1744_ = v_prefixPoint_x3f_1810_;
v___y_1745_ = v___y_1813_;
v___y_1746_ = v___f_1824_;
v___y_1747_ = v___y_1809_;
v___y_1748_ = v___x_1827_;
goto v___jp_1735_;
}
}
}
else
{
lean_dec(v___x_1815_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1805_);
v___y_1707_ = v___y_1807_;
v_prefixPoint_x3f_1708_ = v_prefixPoint_x3f_1810_;
v_suffixPoint_x3f_1709_ = v_fst_1588_;
v___y_1710_ = v___y_1811_;
v___y_1711_ = v___y_1812_;
v___y_1712_ = v___y_1813_;
v___y_1713_ = v___y_1814_;
goto v___jp_1706_;
}
}
v___jp_1828_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_inc_ref(v___y_1833_);
v___x_1836_ = lean_apply_1(v___y_1833_, v___y_1832_);
lean_inc(v___y_1829_);
v___x_1837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1837_, 0, v___y_1829_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
lean_ctor_set(v___x_1837_, 2, v_a_1835_);
v___x_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
v___y_1805_ = v___y_1829_;
v___y_1806_ = v___y_1830_;
v___y_1807_ = v___y_1831_;
v___y_1808_ = v___y_1833_;
v___y_1809_ = v___y_1834_;
v_prefixPoint_x3f_1810_ = v___x_1838_;
v___y_1811_ = v___y_1568_;
v___y_1812_ = v___y_1569_;
v___y_1813_ = v___y_1570_;
v___y_1814_ = v___y_1571_;
goto v___jp_1804_;
}
v___jp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_inc_ref(v_a_1840_);
v___x_1841_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1841_, 0, v_a_1840_);
lean_inc(v_a_1580_);
v___x_1842_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1580_, v___x_1841_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
if (lean_obj_tag(v_a_1843_) == 1)
{
lean_object* v_val_1844_; lean_object* v_snd_1845_; lean_object* v_fst_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1904_; 
v_val_1844_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_val_1844_);
lean_dec_ref_known(v_a_1843_, 1);
v_snd_1845_ = lean_ctor_get(v_val_1844_, 1);
v_fst_1846_ = lean_ctor_get(v_val_1844_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_val_1844_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1848_ = v_val_1844_;
v_isShared_1849_ = v_isSharedCheck_1904_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_snd_1845_);
lean_inc(v_fst_1846_);
lean_dec(v_val_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1904_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_fst_1850_; lean_object* v_snd_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1903_; 
v_fst_1850_ = lean_ctor_get(v_snd_1845_, 0);
v_snd_1851_ = lean_ctor_get(v_snd_1845_, 1);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_snd_1845_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1853_ = v_snd_1845_;
v_isShared_1854_ = v_isSharedCheck_1903_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_snd_1851_);
lean_inc(v_fst_1850_);
lean_dec(v_snd_1845_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1903_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___f_1855_; lean_object* v___x_1856_; 
lean_inc(v_fst_1846_);
v___f_1855_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_1855_, 0, v_fst_1846_);
lean_inc(v_inv_1560_);
v___x_1856_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1851_, v_inv_1560_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_invariantUse_1857_; lean_object* v_conditionIdx_1858_; lean_object* v_cursorPrefix_1859_; lean_object* v_letMutsTuple_1860_; uint8_t v___x_1861_; 
v_invariantUse_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc_ref(v_invariantUse_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v_conditionIdx_1858_ = lean_ctor_get(v_invariantUse_1857_, 0);
lean_inc(v_conditionIdx_1858_);
v_cursorPrefix_1859_ = lean_ctor_get(v_invariantUse_1857_, 1);
lean_inc_ref(v_cursorPrefix_1859_);
v_letMutsTuple_1860_ = lean_ctor_get(v_invariantUse_1857_, 4);
lean_inc_ref(v_letMutsTuple_1860_);
lean_dec_ref(v_invariantUse_1857_);
v___x_1861_ = lean_nat_dec_eq(v_conditionIdx_1858_, v___x_1593_);
lean_dec(v_conditionIdx_1858_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1863_; 
lean_dec_ref(v_letMutsTuple_1860_);
lean_dec_ref(v_cursorPrefix_1859_);
lean_dec_ref(v___f_1855_);
lean_dec(v_snd_1851_);
lean_dec(v_fst_1850_);
lean_dec(v_fst_1846_);
lean_dec_ref(v_a_1840_);
lean_del_object(v___x_1591_);
lean_del_object(v___x_1586_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v_snd_1589_);
lean_ctor_set(v___x_1853_, 0, v_fst_1588_);
v___x_1863_ = v___x_1853_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_fst_1588_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_snd_1589_);
v___x_1863_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1865_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___x_1863_);
lean_ctor_set(v___x_1848_, 0, v_fst_1584_);
v___x_1865_ = v___x_1848_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_fst_1584_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v_a_1574_ = v___x_1865_;
goto v___jp_1573_;
}
}
}
else
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
lean_del_object(v___x_1853_);
lean_del_object(v___x_1848_);
v___x_1868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_1869_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1859_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_dec_ref(v_letMutsTuple_1860_);
lean_dec_ref(v_cursorPrefix_1859_);
v___y_1805_ = v_fst_1846_;
v___y_1806_ = v_fst_1850_;
v___y_1807_ = v_a_1840_;
v___y_1808_ = v___f_1855_;
v___y_1809_ = v_snd_1851_;
v_prefixPoint_x3f_1810_ = v_fst_1584_;
v___y_1811_ = v___y_1568_;
v___y_1812_ = v___y_1569_;
v___y_1813_ = v___y_1570_;
v___y_1814_ = v___y_1571_;
goto v___jp_1804_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec(v_fst_1584_);
v___x_1870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1562_);
v___x_1871_ = l_Lean_Meta_mkProjection(v_xs_1562_, v___x_1870_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = l_Lean_Meta_mkEq(v_a_1872_, v_cursorPrefix_1859_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1875_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
lean_inc_ref(v_letMuts_1563_);
v___x_1875_ = l_Lean_Meta_mkEq(v_letMuts_1563_, v_letMutsTuple_1860_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1877_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
lean_inc(v_fst_1846_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_fst_1846_, v_a_1876_);
v___y_1829_ = v_fst_1846_;
v___y_1830_ = v_fst_1850_;
v___y_1831_ = v_a_1840_;
v___y_1832_ = v_a_1874_;
v___y_1833_ = v___f_1855_;
v___y_1834_ = v_snd_1851_;
v_a_1835_ = v___x_1877_;
goto v___jp_1828_;
}
else
{
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1878_; 
v_a_1878_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1875_, 1);
v___y_1829_ = v_fst_1846_;
v___y_1830_ = v_fst_1850_;
v___y_1831_ = v_a_1840_;
v___y_1832_ = v_a_1874_;
v___y_1833_ = v___f_1855_;
v___y_1834_ = v_snd_1851_;
v_a_1835_ = v_a_1878_;
goto v___jp_1828_;
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_a_1874_);
lean_dec_ref(v___f_1855_);
lean_dec(v_snd_1851_);
lean_dec(v_fst_1850_);
lean_dec(v_fst_1846_);
lean_dec_ref(v_a_1840_);
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1879_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1875_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1875_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v_letMutsTuple_1860_);
lean_dec_ref(v___f_1855_);
lean_dec(v_snd_1851_);
lean_dec(v_fst_1850_);
lean_dec(v_fst_1846_);
lean_dec_ref(v_a_1840_);
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1887_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1873_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1873_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_letMutsTuple_1860_);
lean_dec_ref(v_cursorPrefix_1859_);
lean_dec_ref(v___f_1855_);
lean_dec(v_snd_1851_);
lean_dec(v_fst_1850_);
lean_dec(v_fst_1846_);
lean_dec_ref(v_a_1840_);
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_del_object(v___x_1586_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1895_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1871_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1871_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1856_);
lean_del_object(v___x_1853_);
lean_del_object(v___x_1848_);
v___y_1805_ = v_fst_1846_;
v___y_1806_ = v_fst_1850_;
v___y_1807_ = v_a_1840_;
v___y_1808_ = v___f_1855_;
v___y_1809_ = v_snd_1851_;
v_prefixPoint_x3f_1810_ = v_fst_1584_;
v___y_1811_ = v___y_1568_;
v___y_1812_ = v___y_1569_;
v___y_1813_ = v___y_1570_;
v___y_1814_ = v___y_1571_;
goto v___jp_1804_;
}
}
}
}
else
{
lean_dec(v_a_1843_);
v___y_1707_ = v_a_1840_;
v_prefixPoint_x3f_1708_ = v_fst_1584_;
v_suffixPoint_x3f_1709_ = v_fst_1588_;
v___y_1710_ = v___y_1568_;
v___y_1711_ = v___y_1569_;
v___y_1712_ = v___y_1570_;
v___y_1713_ = v___y_1571_;
goto v___jp_1706_;
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_a_1840_);
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_del_object(v___x_1586_);
lean_dec(v_fst_1584_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1905_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1842_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1842_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v_b_1567_);
lean_dec_ref(v_letMuts_1563_);
lean_dec_ref(v_xs_1562_);
lean_dec_ref(v___x_1561_);
lean_dec(v_inv_1560_);
v_a_1928_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1581_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1581_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
v___jp_1573_:
{
size_t v___x_1575_; size_t v___x_1576_; 
v___x_1575_ = ((size_t)1ULL);
v___x_1576_ = lean_usize_add(v_i_1566_, v___x_1575_);
v_i_1566_ = v___x_1576_;
v_b_1567_ = v_a_1574_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1936_, lean_object* v___x_1937_, lean_object* v_xs_1938_, lean_object* v_letMuts_1939_, lean_object* v_as_1940_, lean_object* v_sz_1941_, lean_object* v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
size_t v_sz_boxed_1949_; size_t v_i_boxed_1950_; lean_object* v_res_1951_; 
v_sz_boxed_1949_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1950_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1936_, v___x_1937_, v_xs_1938_, v_letMuts_1939_, v_as_1940_, v_sz_boxed_1949_, v_i_boxed_1950_, v_b_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_as_1940_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1961_, lean_object* v_inv_1962_, lean_object* v_xs_1963_, lean_object* v_letMuts_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_lctx_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; size_t v_sz_1973_; size_t v___x_1974_; lean_object* v___x_1975_; 
v_lctx_1970_ = lean_ctor_get(v_a_1965_, 2);
v___x_1971_ = lean_box(0);
v___x_1972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1973_ = lean_array_size(v_vcs_1961_);
v___x_1974_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1970_);
v___x_1975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1962_, v_lctx_1970_, v_xs_1963_, v_letMuts_1964_, v_vcs_1961_, v_sz_1973_, v___x_1974_, v___x_1972_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2019_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_2019_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2019_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_snd_1984_; lean_object* v_fst_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2018_; 
v_snd_1984_ = lean_ctor_get(v_a_1976_, 1);
v_fst_1985_ = lean_ctor_get(v_a_1976_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_1976_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1987_ = v_a_1976_;
v_isShared_1988_ = v_isSharedCheck_2018_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_snd_1984_);
lean_inc(v_fst_1985_);
lean_dec(v_a_1976_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2018_;
goto v_resetjp_1986_;
}
v___jp_1980_:
{
lean_object* v___x_1982_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1971_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1971_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
v_resetjp_1986_:
{
if (lean_obj_tag(v_fst_1985_) == 0)
{
lean_del_object(v___x_1987_);
lean_dec(v_snd_1984_);
goto v___jp_1980_;
}
else
{
lean_object* v_fst_1989_; 
v_fst_1989_ = lean_ctor_get(v_snd_1984_, 0);
lean_inc(v_fst_1989_);
if (lean_obj_tag(v_fst_1989_) == 0)
{
lean_dec_ref_known(v_fst_1985_, 1);
lean_del_object(v___x_1987_);
lean_dec(v_snd_1984_);
goto v___jp_1980_;
}
else
{
lean_object* v_snd_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2016_; 
lean_del_object(v___x_1978_);
v_snd_1990_ = lean_ctor_get(v_snd_1984_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_snd_1984_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v_snd_1984_, 0);
lean_dec(v_unused_2017_);
v___x_1992_ = v_snd_1984_;
v_isShared_1993_ = v_isSharedCheck_2016_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_snd_1990_);
lean_dec(v_snd_1984_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2016_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_val_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2015_; 
v_val_1994_ = lean_ctor_get(v_fst_1985_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_fst_1985_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1996_ = v_fst_1985_;
v_isShared_1997_ = v_isSharedCheck_2015_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_val_1994_);
lean_dec(v_fst_1985_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2015_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_val_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2014_; 
v_val_1998_ = lean_ctor_get(v_fst_1989_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_fst_1989_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2000_ = v_fst_1989_;
v_isShared_2001_ = v_isSharedCheck_2014_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_val_1998_);
lean_dec(v_fst_1989_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2014_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v_val_1998_);
v___x_2003_ = v___x_1992_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_val_1998_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_snd_1990_);
v___x_2003_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v___x_2003_);
lean_ctor_set(v___x_1987_, 0, v_val_1994_);
v___x_2005_ = v___x_1987_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_val_1994_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2005_);
v___x_2007_ = v___x_2000_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2009_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 0);
lean_ctor_set(v___x_1996_, 0, v___x_2007_);
v___x_2009_ = v___x_1996_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
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
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_a_2020_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1975_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1975_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_2028_, lean_object* v_inv_2029_, lean_object* v_xs_2030_, lean_object* v_letMuts_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_2028_, v_inv_2029_, v_xs_2030_, v_letMuts_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec_ref(v_vcs_2028_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_2038_, lean_object* v_a_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_2039_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_2046_, lean_object* v_a_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_2046_, v_a_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_MVarId_getDecl(v_m_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v_userName_2062_; lean_object* v_lctx_2063_; lean_object* v_type_2064_; lean_object* v_localInstances_2065_; uint8_t v_kind_2066_; lean_object* v_numScopeArgs_2067_; lean_object* v___x_2068_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v_userName_2062_ = lean_ctor_get(v_a_2061_, 0);
lean_inc(v_userName_2062_);
v_lctx_2063_ = lean_ctor_get(v_a_2061_, 1);
lean_inc_ref(v_lctx_2063_);
v_type_2064_ = lean_ctor_get(v_a_2061_, 2);
lean_inc_ref(v_type_2064_);
v_localInstances_2065_ = lean_ctor_get(v_a_2061_, 4);
lean_inc_ref(v_localInstances_2065_);
v_kind_2066_ = lean_ctor_get_uint8(v_a_2061_, sizeof(void*)*7);
v_numScopeArgs_2067_ = lean_ctor_get(v_a_2061_, 5);
lean_inc(v_numScopeArgs_2067_);
lean_dec(v_a_2061_);
v___x_2068_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_2063_, v_localInstances_2065_, v_type_2064_, v_kind_2066_, v_userName_2062_, v_numScopeArgs_2067_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2077_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = l_Lean_Expr_mvarId_x21(v_a_2069_);
lean_dec(v_a_2069_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2073_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_a_2078_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2068_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2068_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
v_a_2086_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2060_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2060_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_2101_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = l_String_instInhabitedSlice;
v___x_2103_ = lean_panic_fn_borrowed(v___x_2102_, v_msg_2101_);
return v___x_2103_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_2104_, lean_object* v_a_2105_, uint8_t v_b_2106_){
_start:
{
lean_object* v_str_2107_; lean_object* v_startInclusive_2108_; lean_object* v_endExclusive_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_str_2107_ = lean_ctor_get(v_s_2104_, 0);
v_startInclusive_2108_ = lean_ctor_get(v_s_2104_, 1);
v_endExclusive_2109_ = lean_ctor_get(v_s_2104_, 2);
v___x_2110_ = lean_nat_sub(v_endExclusive_2109_, v_startInclusive_2108_);
v___x_2111_ = lean_nat_dec_eq(v_a_2105_, v___x_2110_);
lean_dec(v___x_2110_);
if (v___x_2111_ == 0)
{
uint32_t v___x_2112_; lean_object* v___x_2113_; uint32_t v___x_2114_; uint8_t v___x_2115_; 
v___x_2112_ = 64;
v___x_2113_ = lean_nat_add(v_startInclusive_2108_, v_a_2105_);
lean_dec(v_a_2105_);
v___x_2114_ = lean_string_utf8_get_fast(v_str_2107_, v___x_2113_);
v___x_2115_ = lean_uint32_dec_eq(v___x_2114_, v___x_2112_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_string_utf8_next_fast(v_str_2107_, v___x_2113_);
lean_dec(v___x_2113_);
v___x_2117_ = lean_nat_sub(v___x_2116_, v_startInclusive_2108_);
v_a_2105_ = v___x_2117_;
v_b_2106_ = v___x_2115_;
goto _start;
}
else
{
lean_dec(v___x_2113_);
return v___x_2115_;
}
}
else
{
lean_dec(v_a_2105_);
return v_b_2106_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object* v_s_2119_, lean_object* v_a_2120_, lean_object* v_b_2121_){
_start:
{
uint8_t v_b_boxed_2122_; uint8_t v_res_2123_; lean_object* v_r_2124_; 
v_b_boxed_2122_ = lean_unbox(v_b_2121_);
v_res_2123_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2119_, v_a_2120_, v_b_boxed_2122_);
lean_dec_ref(v_s_2119_);
v_r_2124_ = lean_box(v_res_2123_);
return v_r_2124_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_2125_){
_start:
{
lean_object* v_searcher_2126_; uint8_t v___x_2127_; uint8_t v___x_2128_; 
v_searcher_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = 0;
v___x_2128_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2125_, v_searcher_2126_, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_2129_){
_start:
{
uint8_t v_res_2130_; lean_object* v_r_2131_; 
v_res_2130_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_2129_);
lean_dec_ref(v_s_2129_);
v_r_2131_ = lean_box(v_res_2130_);
return v_r_2131_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_2136_ = lean_unsigned_to_nat(14u);
v___x_2137_ = lean_unsigned_to_nat(22u);
v___x_2138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_2139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_2140_ = l_mkPanicMessageWithDecl(v___x_2139_, v___x_2138_, v___x_2137_, v___x_2136_, v___x_2135_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_2141_){
_start:
{
switch(lean_obj_tag(v_x_2141_))
{
case 1:
{
lean_object* v_info_2142_; lean_object* v_kind_2143_; lean_object* v_args_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2154_; 
v_info_2142_ = lean_ctor_get(v_x_2141_, 0);
v_kind_2143_ = lean_ctor_get(v_x_2141_, 1);
v_args_2144_ = lean_ctor_get(v_x_2141_, 2);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2146_ = v_x_2141_;
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_args_2144_);
lean_inc(v_kind_2143_);
lean_inc(v_info_2142_);
lean_dec(v_x_2141_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
size_t v_sz_2148_; size_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v_sz_2148_ = lean_array_size(v_args_2144_);
v___x_2149_ = ((size_t)0ULL);
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_2148_, v___x_2149_, v_args_2144_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 2, v___x_2150_);
v___x_2152_ = v___x_2146_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_info_2142_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_kind_2143_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
case 3:
{
lean_object* v_info_2155_; lean_object* v_rawVal_2156_; lean_object* v_val_2157_; lean_object* v_preresolved_2158_; uint8_t v___y_2160_; lean_object* v_str_2177_; lean_object* v_startPos_2178_; lean_object* v_stopPos_2179_; uint8_t v___x_2180_; 
v_info_2155_ = lean_ctor_get(v_x_2141_, 0);
v_rawVal_2156_ = lean_ctor_get(v_x_2141_, 1);
v_val_2157_ = lean_ctor_get(v_x_2141_, 2);
v_preresolved_2158_ = lean_ctor_get(v_x_2141_, 3);
v_str_2177_ = lean_ctor_get(v_rawVal_2156_, 0);
v_startPos_2178_ = lean_ctor_get(v_rawVal_2156_, 1);
v_stopPos_2179_ = lean_ctor_get(v_rawVal_2156_, 2);
v___x_2180_ = lean_string_is_valid_pos(v_str_2177_, v_startPos_2178_);
if (v___x_2180_ == 0)
{
goto v___jp_2173_;
}
else
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_string_is_valid_pos(v_str_2177_, v_stopPos_2179_);
if (v___x_2181_ == 0)
{
goto v___jp_2173_;
}
else
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_nat_dec_le(v_startPos_2178_, v_stopPos_2179_);
if (v___x_2182_ == 0)
{
goto v___jp_2173_;
}
else
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
lean_inc(v_stopPos_2179_);
lean_inc(v_startPos_2178_);
lean_inc_ref(v_str_2177_);
v___x_2183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2183_, 0, v_str_2177_);
lean_ctor_set(v___x_2183_, 1, v_startPos_2178_);
lean_ctor_set(v___x_2183_, 2, v_stopPos_2179_);
v___x_2184_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2183_);
lean_dec_ref_known(v___x_2183_, 3);
v___y_2160_ = v___x_2184_;
goto v___jp_2159_;
}
}
}
v___jp_2159_:
{
if (v___y_2160_ == 0)
{
lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2168_; 
lean_inc(v_preresolved_2158_);
lean_inc(v_val_2157_);
lean_inc_ref(v_rawVal_2156_);
lean_inc(v_info_2155_);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; lean_object* v_unused_2170_; lean_object* v_unused_2171_; lean_object* v_unused_2172_; 
v_unused_2169_ = lean_ctor_get(v_x_2141_, 3);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_x_2141_, 2);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v_x_2141_, 1);
lean_dec(v_unused_2171_);
v_unused_2172_ = lean_ctor_get(v_x_2141_, 0);
lean_dec(v_unused_2172_);
v___x_2162_ = v_x_2141_;
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
else
{
lean_dec(v_x_2141_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = l_Lean_Name_eraseMacroScopes(v_val_2157_);
lean_dec(v_val_2157_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 2, v___x_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_info_2155_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_rawVal_2156_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_preresolved_2158_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
else
{
return v_x_2141_;
}
}
v___jp_2173_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2174_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_2175_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_2174_);
v___x_2176_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2175_);
lean_dec_ref(v___x_2175_);
v___y_2160_ = v___x_2176_;
goto v___jp_2159_;
}
}
default: 
{
return v_x_2141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_2185_, size_t v_i_2186_, lean_object* v_bs_2187_){
_start:
{
uint8_t v___x_2188_; 
v___x_2188_ = lean_usize_dec_lt(v_i_2186_, v_sz_2185_);
if (v___x_2188_ == 0)
{
return v_bs_2187_;
}
else
{
lean_object* v_v_2189_; lean_object* v___x_2190_; lean_object* v_bs_x27_2191_; lean_object* v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v_v_2189_ = lean_array_uget(v_bs_2187_, v_i_2186_);
v___x_2190_ = lean_unsigned_to_nat(0u);
v_bs_x27_2191_ = lean_array_uset(v_bs_2187_, v_i_2186_, v___x_2190_);
v___x_2192_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_2189_);
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2186_, v___x_2193_);
v___x_2195_ = lean_array_uset(v_bs_x27_2191_, v_i_2186_, v___x_2192_);
v_i_2186_ = v___x_2194_;
v_bs_2187_ = v___x_2195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2197_, lean_object* v_i_2198_, lean_object* v_bs_2199_){
_start:
{
size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2197_);
lean_dec(v_sz_2197_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2198_);
lean_dec(v_i_2198_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2200_, v_i_boxed_2201_, v_bs_2199_);
return v_res_2202_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2203_, lean_object* v_inst_2204_, lean_object* v_R_2205_, lean_object* v_a_2206_, uint8_t v_b_2207_, lean_object* v_c_2208_){
_start:
{
uint8_t v___x_2209_; 
v___x_2209_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2203_, v_a_2206_, v_b_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2210_, lean_object* v_inst_2211_, lean_object* v_R_2212_, lean_object* v_a_2213_, lean_object* v_b_2214_, lean_object* v_c_2215_){
_start:
{
uint8_t v_b_boxed_2216_; uint8_t v_res_2217_; lean_object* v_r_2218_; 
v_b_boxed_2216_ = lean_unbox(v_b_2214_);
v_res_2217_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2210_, v_inst_2211_, v_R_2212_, v_a_2213_, v_b_boxed_2216_, v_c_2215_);
lean_dec_ref(v_s_2210_);
v_r_2218_ = lean_box(v_res_2217_);
return v_r_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2219_, lean_object* v_h__1_2220_, lean_object* v_h__2_2221_, lean_object* v_h__3_2222_, lean_object* v_h__4_2223_){
_start:
{
switch(lean_obj_tag(v_x_2219_))
{
case 0:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v_h__3_2222_);
lean_dec(v_h__2_2221_);
lean_dec(v_h__1_2220_);
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_apply_1(v_h__4_2223_, v___x_2224_);
return v___x_2225_;
}
case 1:
{
lean_object* v_info_2226_; lean_object* v_kind_2227_; lean_object* v_args_2228_; lean_object* v___x_2229_; 
lean_dec(v_h__4_2223_);
lean_dec(v_h__3_2222_);
lean_dec(v_h__1_2220_);
v_info_2226_ = lean_ctor_get(v_x_2219_, 0);
lean_inc(v_info_2226_);
v_kind_2227_ = lean_ctor_get(v_x_2219_, 1);
lean_inc(v_kind_2227_);
v_args_2228_ = lean_ctor_get(v_x_2219_, 2);
lean_inc_ref(v_args_2228_);
lean_dec_ref_known(v_x_2219_, 3);
v___x_2229_ = lean_apply_3(v_h__2_2221_, v_info_2226_, v_kind_2227_, v_args_2228_);
return v___x_2229_;
}
case 2:
{
lean_object* v_info_2230_; lean_object* v_val_2231_; lean_object* v___x_2232_; 
lean_dec(v_h__4_2223_);
lean_dec(v_h__2_2221_);
lean_dec(v_h__1_2220_);
v_info_2230_ = lean_ctor_get(v_x_2219_, 0);
lean_inc(v_info_2230_);
v_val_2231_ = lean_ctor_get(v_x_2219_, 1);
lean_inc_ref(v_val_2231_);
lean_dec_ref_known(v_x_2219_, 2);
v___x_2232_ = lean_apply_2(v_h__3_2222_, v_info_2230_, v_val_2231_);
return v___x_2232_;
}
default: 
{
lean_object* v_info_2233_; lean_object* v_rawVal_2234_; lean_object* v_val_2235_; lean_object* v_preresolved_2236_; lean_object* v___x_2237_; 
lean_dec(v_h__4_2223_);
lean_dec(v_h__3_2222_);
lean_dec(v_h__2_2221_);
v_info_2233_ = lean_ctor_get(v_x_2219_, 0);
lean_inc(v_info_2233_);
v_rawVal_2234_ = lean_ctor_get(v_x_2219_, 1);
lean_inc_ref(v_rawVal_2234_);
v_val_2235_ = lean_ctor_get(v_x_2219_, 2);
lean_inc(v_val_2235_);
v_preresolved_2236_ = lean_ctor_get(v_x_2219_, 3);
lean_inc(v_preresolved_2236_);
lean_dec_ref_known(v_x_2219_, 4);
v___x_2237_ = lean_apply_4(v_h__1_2220_, v_info_2233_, v_rawVal_2234_, v_val_2235_, v_preresolved_2236_);
return v___x_2237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2238_, lean_object* v_x_2239_, lean_object* v_h__1_2240_, lean_object* v_h__2_2241_, lean_object* v_h__3_2242_, lean_object* v_h__4_2243_){
_start:
{
switch(lean_obj_tag(v_x_2239_))
{
case 0:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec(v_h__3_2242_);
lean_dec(v_h__2_2241_);
lean_dec(v_h__1_2240_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_apply_1(v_h__4_2243_, v___x_2244_);
return v___x_2245_;
}
case 1:
{
lean_object* v_info_2246_; lean_object* v_kind_2247_; lean_object* v_args_2248_; lean_object* v___x_2249_; 
lean_dec(v_h__4_2243_);
lean_dec(v_h__3_2242_);
lean_dec(v_h__1_2240_);
v_info_2246_ = lean_ctor_get(v_x_2239_, 0);
lean_inc(v_info_2246_);
v_kind_2247_ = lean_ctor_get(v_x_2239_, 1);
lean_inc(v_kind_2247_);
v_args_2248_ = lean_ctor_get(v_x_2239_, 2);
lean_inc_ref(v_args_2248_);
lean_dec_ref_known(v_x_2239_, 3);
v___x_2249_ = lean_apply_3(v_h__2_2241_, v_info_2246_, v_kind_2247_, v_args_2248_);
return v___x_2249_;
}
case 2:
{
lean_object* v_info_2250_; lean_object* v_val_2251_; lean_object* v___x_2252_; 
lean_dec(v_h__4_2243_);
lean_dec(v_h__2_2241_);
lean_dec(v_h__1_2240_);
v_info_2250_ = lean_ctor_get(v_x_2239_, 0);
lean_inc(v_info_2250_);
v_val_2251_ = lean_ctor_get(v_x_2239_, 1);
lean_inc_ref(v_val_2251_);
lean_dec_ref_known(v_x_2239_, 2);
v___x_2252_ = lean_apply_2(v_h__3_2242_, v_info_2250_, v_val_2251_);
return v___x_2252_;
}
default: 
{
lean_object* v_info_2253_; lean_object* v_rawVal_2254_; lean_object* v_val_2255_; lean_object* v_preresolved_2256_; lean_object* v___x_2257_; 
lean_dec(v_h__4_2243_);
lean_dec(v_h__3_2242_);
lean_dec(v_h__2_2241_);
v_info_2253_ = lean_ctor_get(v_x_2239_, 0);
lean_inc(v_info_2253_);
v_rawVal_2254_ = lean_ctor_get(v_x_2239_, 1);
lean_inc_ref(v_rawVal_2254_);
v_val_2255_ = lean_ctor_get(v_x_2239_, 2);
lean_inc(v_val_2255_);
v_preresolved_2256_ = lean_ctor_get(v_x_2239_, 3);
lean_inc(v_preresolved_2256_);
lean_dec_ref_known(v_x_2239_, 4);
v___x_2257_ = lean_apply_4(v_h__1_2240_, v_info_2253_, v_rawVal_2254_, v_val_2255_, v_preresolved_2256_);
return v___x_2257_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2258_, lean_object* v_h__1_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_apply_2(v_h__1_2259_, v_x_2258_, lean_box(0));
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2261_, lean_object* v_P_2262_, lean_object* v_motive_2263_, lean_object* v_x_2264_, lean_object* v_h__1_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_apply_2(v_h__1_2265_, v_x_2264_, lean_box(0));
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2269_, lean_object* v_syn_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2272_, lean_object* v_syn_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2272_, v_syn_2273_);
lean_dec(v_name_2272_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2281_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2309_ = lean_unsigned_to_nat(2u);
v___x_2310_ = l_Lean_Expr_isAppOfArity(v_e_2281_, v___x_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2312_ = lean_unsigned_to_nat(3u);
v___x_2313_ = l_Lean_Expr_isAppOfArity(v_e_2281_, v___x_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2315_ = l_Lean_Expr_isAppOfArity(v_e_2281_, v___x_2314_, v___x_2312_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2317_ = l_Lean_Expr_isAppOfArity(v_e_2281_, v___x_2316_, v___x_2312_);
if (v___x_2317_ == 0)
{
goto v___jp_2282_;
}
else
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Expr_appArg_x21(v_e_2281_);
if (lean_obj_tag(v___x_2318_) == 6)
{
lean_object* v_binderName_2319_; lean_object* v_binderType_2320_; lean_object* v_body_2321_; uint8_t v_binderInfo_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_e_2281_);
v_binderName_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_binderName_2319_);
v_binderType_2320_ = lean_ctor_get(v___x_2318_, 1);
lean_inc_ref(v_binderType_2320_);
v_body_2321_ = lean_ctor_get(v___x_2318_, 2);
lean_inc_ref(v_body_2321_);
v_binderInfo_2322_ = lean_ctor_get_uint8(v___x_2318_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_2318_, 3);
v___x_2323_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2321_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_dec_ref(v_binderType_2320_);
lean_dec(v_binderName_2319_);
return v___x_2323_;
}
else
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2341_; 
v_val_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2341_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2341_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_fst_2328_; lean_object* v_snd_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2340_; 
v_fst_2328_ = lean_ctor_get(v_val_2324_, 0);
v_snd_2329_ = lean_ctor_get(v_val_2324_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_val_2324_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2331_ = v_val_2324_;
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_snd_2329_);
lean_inc(v_fst_2328_);
lean_dec(v_val_2324_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = l_Lean_mkForall(v_binderName_2319_, v_binderInfo_2322_, v_binderType_2320_, v_snd_2329_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_fst_2328_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2335_);
v___x_2337_ = v___x_2326_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2318_);
goto v___jp_2282_;
}
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2342_ = l_Lean_Expr_appFn_x21(v_e_2281_);
v___x_2343_ = l_Lean_Expr_appArg_x21(v___x_2342_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2343_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_dec_ref(v_e_2281_);
return v___x_2344_;
}
else
{
lean_object* v_val_2345_; lean_object* v_snd_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_val_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_val_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v_snd_2346_ = lean_ctor_get(v_val_2345_, 1);
lean_inc(v_snd_2346_);
lean_dec(v_val_2345_);
v___x_2347_ = l_Lean_Expr_appArg_x21(v_e_2281_);
lean_dec_ref(v_e_2281_);
v___x_2348_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_dec(v_snd_2346_);
return v___x_2348_;
}
else
{
lean_object* v_val_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2366_; 
v_val_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2366_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_val_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2366_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_fst_2353_; lean_object* v_snd_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2365_; 
v_fst_2353_ = lean_ctor_get(v_val_2349_, 0);
v_snd_2354_ = lean_ctor_get(v_val_2349_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_val_2349_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2356_ = v_val_2349_;
v_isShared_2357_ = v_isSharedCheck_2365_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_snd_2354_);
lean_inc(v_fst_2353_);
lean_dec(v_val_2349_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2365_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = l_Lean_mkOr(v_snd_2346_, v_snd_2354_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 1, v___x_2358_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_fst_2353_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2360_);
v___x_2362_ = v___x_2351_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
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
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = l_Lean_Expr_appFn_x21(v_e_2281_);
v___x_2368_ = l_Lean_Expr_appArg_x21(v___x_2367_);
lean_dec_ref(v___x_2367_);
v___x_2369_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2368_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_dec_ref(v_e_2281_);
return v___x_2369_;
}
else
{
lean_object* v_val_2370_; lean_object* v_snd_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_val_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_val_2370_);
lean_dec_ref_known(v___x_2369_, 1);
v_snd_2371_ = lean_ctor_get(v_val_2370_, 1);
lean_inc(v_snd_2371_);
lean_dec(v_val_2370_);
v___x_2372_ = l_Lean_Expr_appArg_x21(v_e_2281_);
lean_dec_ref(v_e_2281_);
v___x_2373_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_dec(v_snd_2371_);
return v___x_2373_;
}
else
{
lean_object* v_val_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2391_; 
v_val_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2391_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_val_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2391_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v_fst_2378_; lean_object* v_snd_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2390_; 
v_fst_2378_ = lean_ctor_get(v_val_2374_, 0);
v_snd_2379_ = lean_ctor_get(v_val_2374_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_val_2374_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2381_ = v_val_2374_;
v_isShared_2382_ = v_isSharedCheck_2390_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_snd_2379_);
lean_inc(v_fst_2378_);
lean_dec(v_val_2374_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2390_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = l_Lean_mkAnd(v_snd_2371_, v_snd_2379_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 1, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_fst_2378_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2385_);
v___x_2387_ = v___x_2376_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
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
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2392_ = lean_box(0);
v___x_2393_ = l_Lean_Expr_getAppFn(v_e_2281_);
v___x_2394_ = l_Lean_Expr_constLevels_x21(v___x_2393_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = lean_unsigned_to_nat(0u);
v___x_2396_ = l_List_get_x21Internal___redArg(v___x_2392_, v___x_2394_, v___x_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = l_Lean_Expr_getAppNumArgs(v_e_2281_);
v___x_2399_ = lean_nat_sub(v___x_2398_, v___x_2397_);
lean_dec(v___x_2398_);
v___x_2400_ = lean_nat_sub(v___x_2399_, v___x_2397_);
lean_dec(v___x_2399_);
v___x_2401_ = l_Lean_Expr_getRevArg_x21(v_e_2281_, v___x_2400_);
lean_dec_ref(v_e_2281_);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2396_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
return v___x_2403_;
}
v___jp_2282_:
{
if (lean_obj_tag(v_e_2281_) == 8)
{
lean_object* v_declName_2283_; lean_object* v_type_2284_; lean_object* v_value_2285_; lean_object* v_body_2286_; uint8_t v_nondep_2287_; lean_object* v___x_2288_; 
v_declName_2283_ = lean_ctor_get(v_e_2281_, 0);
lean_inc(v_declName_2283_);
v_type_2284_ = lean_ctor_get(v_e_2281_, 1);
lean_inc_ref(v_type_2284_);
v_value_2285_ = lean_ctor_get(v_e_2281_, 2);
lean_inc_ref(v_value_2285_);
v_body_2286_ = lean_ctor_get(v_e_2281_, 3);
lean_inc_ref(v_body_2286_);
v_nondep_2287_ = lean_ctor_get_uint8(v_e_2281_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2281_, 4);
v___x_2288_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2286_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_dec_ref(v_value_2285_);
lean_dec_ref(v_type_2284_);
lean_dec(v_declName_2283_);
return v___x_2288_;
}
else
{
lean_object* v_val_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2306_; 
v_val_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2306_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_val_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2306_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_fst_2293_; lean_object* v_snd_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2305_; 
v_fst_2293_ = lean_ctor_get(v_val_2289_, 0);
v_snd_2294_ = lean_ctor_get(v_val_2289_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_val_2289_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2296_ = v_val_2289_;
v_isShared_2297_ = v_isSharedCheck_2305_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_snd_2294_);
lean_inc(v_fst_2293_);
lean_dec(v_val_2289_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2305_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = l_Lean_Expr_letE___override(v_declName_2283_, v_type_2284_, v_value_2285_, v_snd_2294_, v_nondep_2287_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_fst_2293_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2300_);
v___x_2302_ = v___x_2291_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
}
else
{
lean_object* v___x_2307_; 
lean_dec_ref(v_e_2281_);
v___x_2307_ = lean_box(0);
return v___x_2307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2404_){
_start:
{
lean_object* v___x_2405_; 
lean_inc_ref(v_e_2404_);
v___x_2405_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2404_);
if (lean_obj_tag(v___x_2405_) == 0)
{
return v_e_2404_;
}
else
{
lean_object* v_val_2406_; lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec_ref(v_e_2404_);
v_val_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_val_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v_fst_2407_ = lean_ctor_get(v_val_2406_, 0);
lean_inc_n(v_fst_2407_, 2);
v_snd_2408_ = lean_ctor_get(v_val_2406_, 1);
lean_inc(v_snd_2408_);
lean_dec(v_val_2406_);
v___x_2409_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2407_);
v___x_2410_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2407_, v___x_2409_, v_snd_2408_);
return v___x_2410_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Array_mkArray0(lean_box(0));
return v___x_2421_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2460_ = l_String_toRawSubstring_x27(v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2477_ = l_String_toRawSubstring_x27(v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2492_, lean_object* v_default_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; lean_object* v_handlers_2500_; 
v___x_2499_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2500_ = l_Lean_Syntax_SepArray_ofElems(v___x_2499_, v_handlers_2492_);
switch(lean_obj_tag(v_default_2493_))
{
case 0:
{
lean_object* v_ref_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_ref_2501_ = lean_ctor_get(v_a_2496_, 5);
v___x_2502_ = 0;
v___x_2503_ = l_Lean_SourceInfo_fromRef(v_ref_2501_, v___x_2502_);
v___x_2504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2503_, 3);
v___x_2506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2503_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2508_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2509_ = l_Array_append___redArg(v___x_2508_, v_handlers_2500_);
lean_dec_ref(v_handlers_2500_);
v___x_2510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2503_);
lean_ctor_set(v___x_2510_, 1, v___x_2507_);
lean_ctor_set(v___x_2510_, 2, v___x_2509_);
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2503_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = l_Lean_Syntax_node3(v___x_2503_, v___x_2504_, v___x_2506_, v___x_2510_, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
return v___x_2514_;
}
case 1:
{
lean_object* v_ref_2515_; lean_object* v_quotContext_2516_; lean_object* v_currMacroScope_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_ref_2515_ = lean_ctor_get(v_a_2496_, 5);
v_quotContext_2516_ = lean_ctor_get(v_a_2496_, 10);
v_currMacroScope_2517_ = lean_ctor_get(v_a_2496_, 11);
v___x_2518_ = 0;
v___x_2519_ = l_Lean_SourceInfo_fromRef(v_ref_2515_, v___x_2518_);
v___x_2520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2519_, 12);
v___x_2522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2519_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2519_);
lean_ctor_set(v___x_2528_, 1, v___x_2526_);
v___x_2529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2519_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2533_ = l_Array_append___redArg(v___x_2532_, v_handlers_2500_);
lean_dec_ref(v_handlers_2500_);
v___x_2534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2519_);
lean_ctor_set(v___x_2534_, 1, v___x_2499_);
v___x_2535_ = lean_array_push(v___x_2533_, v___x_2534_);
v___x_2536_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2517_);
lean_inc(v_quotContext_2516_);
v___x_2538_ = l_Lean_addMacroScope(v_quotContext_2516_, v___x_2537_, v_currMacroScope_2517_);
v___x_2539_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2540_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2519_);
lean_ctor_set(v___x_2540_, 1, v___x_2536_);
lean_ctor_set(v___x_2540_, 2, v___x_2538_);
lean_ctor_set(v___x_2540_, 3, v___x_2539_);
v___x_2541_ = lean_array_push(v___x_2535_, v___x_2540_);
v___x_2542_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2519_);
lean_ctor_set(v___x_2542_, 1, v___x_2525_);
lean_ctor_set(v___x_2542_, 2, v___x_2541_);
v___x_2543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2519_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Lean_Syntax_node3(v___x_2519_, v___x_2529_, v___x_2531_, v___x_2542_, v___x_2544_);
v___x_2546_ = l_Lean_Syntax_node2(v___x_2519_, v___x_2527_, v___x_2528_, v___x_2545_);
v___x_2547_ = l_Lean_Syntax_node1(v___x_2519_, v___x_2525_, v___x_2546_);
v___x_2548_ = l_Lean_Syntax_node1(v___x_2519_, v___x_2524_, v___x_2547_);
v___x_2549_ = l_Lean_Syntax_node1(v___x_2519_, v___x_2523_, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_node2(v___x_2519_, v___x_2520_, v___x_2522_, v___x_2549_);
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
case 2:
{
lean_object* v_ref_2552_; lean_object* v_quotContext_2553_; lean_object* v_currMacroScope_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_ref_2552_ = lean_ctor_get(v_a_2496_, 5);
v_quotContext_2553_ = lean_ctor_get(v_a_2496_, 10);
v_currMacroScope_2554_ = lean_ctor_get(v_a_2496_, 11);
v___x_2555_ = 0;
v___x_2556_ = l_Lean_SourceInfo_fromRef(v_ref_2552_, v___x_2555_);
v___x_2557_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2556_, 12);
v___x_2559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2556_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2561_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2556_);
lean_ctor_set(v___x_2565_, 1, v___x_2563_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2556_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2570_ = l_Array_append___redArg(v___x_2569_, v_handlers_2500_);
lean_dec_ref(v_handlers_2500_);
v___x_2571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2556_);
lean_ctor_set(v___x_2571_, 1, v___x_2499_);
v___x_2572_ = lean_array_push(v___x_2570_, v___x_2571_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
lean_inc(v_currMacroScope_2554_);
lean_inc(v_quotContext_2553_);
v___x_2575_ = l_Lean_addMacroScope(v_quotContext_2553_, v___x_2574_, v_currMacroScope_2554_);
v___x_2576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
v___x_2577_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2556_);
lean_ctor_set(v___x_2577_, 1, v___x_2573_);
lean_ctor_set(v___x_2577_, 2, v___x_2575_);
lean_ctor_set(v___x_2577_, 3, v___x_2576_);
v___x_2578_ = lean_array_push(v___x_2572_, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2556_);
lean_ctor_set(v___x_2579_, 1, v___x_2562_);
lean_ctor_set(v___x_2579_, 2, v___x_2578_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2556_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Lean_Syntax_node3(v___x_2556_, v___x_2566_, v___x_2568_, v___x_2579_, v___x_2581_);
v___x_2583_ = l_Lean_Syntax_node2(v___x_2556_, v___x_2564_, v___x_2565_, v___x_2582_);
v___x_2584_ = l_Lean_Syntax_node1(v___x_2556_, v___x_2562_, v___x_2583_);
v___x_2585_ = l_Lean_Syntax_node1(v___x_2556_, v___x_2561_, v___x_2584_);
v___x_2586_ = l_Lean_Syntax_node1(v___x_2556_, v___x_2560_, v___x_2585_);
v___x_2587_ = l_Lean_Syntax_node2(v___x_2556_, v___x_2557_, v___x_2559_, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
default: 
{
lean_object* v_e_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_e_2589_ = lean_ctor_get(v_default_2493_, 0);
lean_inc_ref(v_e_2589_);
lean_dec_ref_known(v_default_2493_, 1);
v___x_2590_ = lean_box(1);
v___x_2591_ = l_Lean_PrettyPrinter_delab(v_e_2589_, v___x_2590_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2628_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2628_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2628_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_ref_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v_ref_2596_ = lean_ctor_get(v_a_2496_, 5);
v___x_2597_ = 0;
v___x_2598_ = l_Lean_SourceInfo_fromRef(v_ref_2596_, v___x_2597_);
v___x_2599_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2598_, 11);
v___x_2601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2598_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2604_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2598_);
lean_ctor_set(v___x_2607_, 1, v___x_2605_);
v___x_2608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2598_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2612_ = l_Array_append___redArg(v___x_2611_, v_handlers_2500_);
lean_dec_ref(v_handlers_2500_);
v___x_2613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2598_);
lean_ctor_set(v___x_2613_, 1, v___x_2499_);
v___x_2614_ = lean_array_push(v___x_2612_, v___x_2613_);
v___x_2615_ = lean_array_push(v___x_2614_, v_a_2592_);
v___x_2616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2598_);
lean_ctor_set(v___x_2616_, 1, v___x_2604_);
lean_ctor_set(v___x_2616_, 2, v___x_2615_);
v___x_2617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2598_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = l_Lean_Syntax_node3(v___x_2598_, v___x_2608_, v___x_2610_, v___x_2616_, v___x_2618_);
v___x_2620_ = l_Lean_Syntax_node2(v___x_2598_, v___x_2606_, v___x_2607_, v___x_2619_);
v___x_2621_ = l_Lean_Syntax_node1(v___x_2598_, v___x_2604_, v___x_2620_);
v___x_2622_ = l_Lean_Syntax_node1(v___x_2598_, v___x_2603_, v___x_2621_);
v___x_2623_ = l_Lean_Syntax_node1(v___x_2598_, v___x_2602_, v___x_2622_);
v___x_2624_ = l_Lean_Syntax_node2(v___x_2598_, v___x_2599_, v___x_2601_, v___x_2623_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2624_);
v___x_2626_ = v___x_2594_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
lean_dec_ref(v_handlers_2500_);
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2629_, lean_object* v_default_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2629_, v_default_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec_ref(v_handlers_2629_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2637_, lean_object* v___y_2638_){
_start:
{
uint8_t v___x_2640_; 
v___x_2640_ = l_Lean_Expr_hasMVar(v_e_2637_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_e_2637_);
return v___x_2641_;
}
else
{
lean_object* v___x_2642_; lean_object* v_mctx_2643_; lean_object* v___x_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v___x_2647_; lean_object* v_cache_2648_; lean_object* v_zetaDeltaFVarIds_2649_; lean_object* v_postponed_2650_; lean_object* v_diag_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2660_; 
v___x_2642_ = lean_st_ref_get(v___y_2638_);
v_mctx_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc_ref(v_mctx_2643_);
lean_dec(v___x_2642_);
v___x_2644_ = l_Lean_instantiateMVarsCore(v_mctx_2643_, v_e_2637_);
v_fst_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_fst_2645_);
v_snd_2646_ = lean_ctor_get(v___x_2644_, 1);
lean_inc(v_snd_2646_);
lean_dec_ref(v___x_2644_);
v___x_2647_ = lean_st_ref_take(v___y_2638_);
v_cache_2648_ = lean_ctor_get(v___x_2647_, 1);
v_zetaDeltaFVarIds_2649_ = lean_ctor_get(v___x_2647_, 2);
v_postponed_2650_ = lean_ctor_get(v___x_2647_, 3);
v_diag_2651_ = lean_ctor_get(v___x_2647_, 4);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v___x_2647_, 0);
lean_dec(v_unused_2661_);
v___x_2653_ = v___x_2647_;
v_isShared_2654_ = v_isSharedCheck_2660_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_diag_2651_);
lean_inc(v_postponed_2650_);
lean_inc(v_zetaDeltaFVarIds_2649_);
lean_inc(v_cache_2648_);
lean_dec(v___x_2647_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2660_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v_snd_2646_);
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_snd_2646_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_cache_2648_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_zetaDeltaFVarIds_2649_);
lean_ctor_set(v_reuseFailAlloc_2659_, 3, v_postponed_2650_);
lean_ctor_set(v_reuseFailAlloc_2659_, 4, v_diag_2651_);
v___x_2656_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_st_ref_put(v___y_2638_, v___x_2656_);
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_fst_2645_);
return v___x_2658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2662_, v___y_2663_);
lean_dec(v___y_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2666_, v___y_2672_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; 
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v___y_2690_);
lean_inc_ref(v___y_2689_);
v___x_2698_ = lean_apply_9(v_x_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, lean_box(0));
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2710_, lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___f_2721_; lean_object* v___x_2722_; 
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
v___f_2721_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2721_, 0, v_x_2711_);
lean_closure_set(v___f_2721_, 1, v___y_2712_);
lean_closure_set(v___f_2721_, 2, v___y_2713_);
lean_closure_set(v___f_2721_, 3, v___y_2714_);
lean_closure_set(v___f_2721_, 4, v___y_2715_);
v___x_2722_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2710_, v___f_2721_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2722_) == 0)
{
return v___x_2722_;
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2731_, lean_object* v_x_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2731_, v_x_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2743_, lean_object* v_mvarId_2744_, lean_object* v_x_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2744_, v_x_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2756_, lean_object* v_mvarId_2757_, lean_object* v_x_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2756_, v_mvarId_2757_, v_x_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2769_, lean_object* v_inv_2770_, lean_object* v_xs_2771_, uint8_t v___x_2772_, lean_object* v___x_2773_, lean_object* v_letMuts_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
lean_inc_ref(v_letMuts_2774_);
lean_inc_ref(v_xs_2771_);
v___x_2784_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2769_, v_inv_2770_, v_xs_2771_, v_letMuts_2774_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2861_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2861_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2861_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
if (lean_obj_tag(v_a_2785_) == 1)
{
lean_object* v_val_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2787_);
v_val_2789_ = lean_ctor_get(v_a_2785_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_a_2785_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2791_ = v_a_2785_;
v_isShared_2792_ = v_isSharedCheck_2856_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_val_2789_);
lean_dec(v_a_2785_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2856_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v_snd_2793_; lean_object* v_fst_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2855_; 
v_snd_2793_ = lean_ctor_get(v_val_2789_, 1);
v_fst_2794_ = lean_ctor_get(v_val_2789_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_val_2789_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2796_ = v_val_2789_;
v_isShared_2797_ = v_isSharedCheck_2855_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_snd_2793_);
lean_inc(v_fst_2794_);
lean_dec(v_val_2789_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2855_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v_fst_2798_; lean_object* v_snd_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2854_; 
v_fst_2798_ = lean_ctor_get(v_snd_2793_, 0);
v_snd_2799_ = lean_ctor_get(v_snd_2793_, 1);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_snd_2793_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2801_ = v_snd_2793_;
v_isShared_2802_ = v_isSharedCheck_2854_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_snd_2799_);
lean_inc(v_fst_2798_);
lean_dec(v_snd_2793_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2854_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v_lvl_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; 
v_lvl_2803_ = lean_ctor_get(v_fst_2794_, 0);
lean_inc(v_lvl_2803_);
v___x_2804_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2794_);
lean_inc(v_fst_2798_);
v___x_2805_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2798_);
v___x_2806_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2803_, v___x_2804_, v___x_2805_);
v___x_2807_ = lean_unsigned_to_nat(2u);
v___x_2808_ = lean_mk_empty_array_with_capacity(v___x_2807_);
v___x_2809_ = lean_array_push(v___x_2808_, v_xs_2771_);
lean_inc_ref(v_letMuts_2774_);
v___x_2810_ = lean_array_push(v___x_2809_, v_letMuts_2774_);
v___x_2811_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2806_);
v___x_2812_ = 0;
v___x_2813_ = 1;
v___x_2814_ = l_Lean_Meta_mkLambdaFVars(v___x_2810_, v___x_2811_, v___x_2812_, v___x_2772_, v___x_2812_, v___x_2772_, v___x_2813_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec_ref(v___x_2810_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v_letMutsPred_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v_letMutsPred_2816_ = lean_ctor_get(v_fst_2798_, 2);
lean_inc_ref(v_letMutsPred_2816_);
lean_dec(v_fst_2798_);
v___x_2817_ = lean_mk_empty_array_with_capacity(v___x_2773_);
v___x_2818_ = lean_array_push(v___x_2817_, v_letMuts_2774_);
v___x_2819_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2816_);
v___x_2820_ = l_Lean_Meta_mkLambdaFVars(v___x_2818_, v___x_2819_, v___x_2812_, v___x_2772_, v___x_2812_, v___x_2772_, v___x_2813_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec_ref(v___x_2818_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2837_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2837_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2837_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v_a_2821_);
v___x_2826_ = v___x_2801_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2821_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_snd_2799_);
v___x_2826_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2828_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2826_);
lean_ctor_set(v___x_2796_, 0, v_a_2815_);
v___x_2828_ = v___x_2796_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2815_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2828_);
v___x_2830_ = v___x_2791_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2832_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2830_);
v___x_2832_ = v___x_2823_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_a_2815_);
lean_del_object(v___x_2801_);
lean_dec(v_snd_2799_);
lean_del_object(v___x_2796_);
lean_del_object(v___x_2791_);
v_a_2838_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2820_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2820_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_del_object(v___x_2801_);
lean_dec(v_snd_2799_);
lean_dec(v_fst_2798_);
lean_del_object(v___x_2796_);
lean_del_object(v___x_2791_);
lean_dec_ref(v_letMuts_2774_);
v_a_2846_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2814_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2814_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_dec(v_a_2785_);
lean_dec_ref(v_letMuts_2774_);
lean_dec_ref(v_xs_2771_);
v___x_2857_ = lean_box(0);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2857_);
v___x_2859_ = v___x_2787_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v_letMuts_2774_);
lean_dec_ref(v_xs_2771_);
v_a_2862_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2784_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2784_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2870_, lean_object* v_inv_2871_, lean_object* v_xs_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, lean_object* v_letMuts_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
uint8_t v___x_92046__boxed_2885_; lean_object* v_res_2886_; 
v___x_92046__boxed_2885_ = lean_unbox(v___x_2873_);
v_res_2886_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2870_, v_inv_2871_, v_xs_2872_, v___x_92046__boxed_2885_, v___x_2874_, v_letMuts_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___x_2874_);
lean_dec_ref(v_a_2870_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v_b_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; 
lean_inc(v___y_2896_);
lean_inc_ref(v___y_2895_);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2891_);
lean_inc_ref(v___y_2890_);
lean_inc(v___y_2889_);
lean_inc_ref(v___y_2888_);
v___x_2898_ = lean_apply_10(v_k_2887_, v_b_2892_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, lean_box(0));
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v_b_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v_b_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2911_, uint8_t v_bi_2912_, lean_object* v_type_2913_, lean_object* v_k_2914_, uint8_t v_kind_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___f_2925_; lean_object* v___x_2926_; 
lean_inc(v___y_2919_);
lean_inc_ref(v___y_2918_);
lean_inc(v___y_2917_);
lean_inc_ref(v___y_2916_);
v___f_2925_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2925_, 0, v_k_2914_);
lean_closure_set(v___f_2925_, 1, v___y_2916_);
lean_closure_set(v___f_2925_, 2, v___y_2917_);
lean_closure_set(v___f_2925_, 3, v___y_2918_);
lean_closure_set(v___f_2925_, 4, v___y_2919_);
v___x_2926_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2911_, v_bi_2912_, v_type_2913_, v___f_2925_, v_kind_2915_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2926_) == 0)
{
return v___x_2926_;
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2935_, lean_object* v_bi_2936_, lean_object* v_type_2937_, lean_object* v_k_2938_, lean_object* v_kind_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v_bi_boxed_2949_; uint8_t v_kind_boxed_2950_; lean_object* v_res_2951_; 
v_bi_boxed_2949_ = lean_unbox(v_bi_2936_);
v_kind_boxed_2950_ = lean_unbox(v_kind_2939_);
v_res_2951_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2935_, v_bi_boxed_2949_, v_type_2937_, v_k_2938_, v_kind_boxed_2950_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2952_, lean_object* v_type_2953_, lean_object* v_k_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
uint8_t v___x_2964_; uint8_t v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = 0;
v___x_2965_ = 0;
v___x_2966_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2952_, v___x_2964_, v_type_2953_, v_k_2954_, v___x_2965_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2967_, lean_object* v_type_2968_, lean_object* v_k_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2967_, v_type_2968_, v_k_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2983_, lean_object* v_inv_2984_, uint8_t v___x_2985_, lean_object* v___x_2986_, lean_object* v_arg_2987_, lean_object* v_xs_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v___f_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2998_ = lean_box(v___x_2985_);
v___f_2999_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2999_, 0, v_a_2983_);
lean_closure_set(v___f_2999_, 1, v_inv_2984_);
lean_closure_set(v___f_2999_, 2, v_xs_2988_);
lean_closure_set(v___f_2999_, 3, v___x_2998_);
lean_closure_set(v___f_2999_, 4, v___x_2986_);
v___x_3000_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3001_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3000_, v_arg_2987_, v___f_2999_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_3002_, lean_object* v_inv_3003_, lean_object* v___x_3004_, lean_object* v___x_3005_, lean_object* v_arg_3006_, lean_object* v_xs_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
uint8_t v___x_92366__boxed_3017_; lean_object* v_res_3018_; 
v___x_92366__boxed_3017_ = lean_unbox(v___x_3004_);
v_res_3018_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_3002_, v_inv_3003_, v___x_92366__boxed_3017_, v___x_3005_, v_arg_3006_, v_xs_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
return v_res_3018_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3022_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
return v___x_3024_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = lean_unsigned_to_nat(32u);
v___x_3026_ = lean_mk_empty_array_with_capacity(v___x_3025_);
v___x_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_3028_, lean_object* v_r_3029_, uint8_t v___x_3030_, lean_object* v___x_3031_, lean_object* v___x_3032_, lean_object* v_xs_3033_, lean_object* v_fst_3034_, lean_object* v_fst_3035_, lean_object* v_letMuts_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v___x_3046_; 
lean_inc_ref(v_fst_3028_);
v___x_3046_ = l_Lean_Meta_mkNone(v_fst_3028_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
v___x_3048_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_3049_ = lean_unsigned_to_nat(2u);
v___x_3050_ = lean_mk_empty_array_with_capacity(v___x_3049_);
lean_inc_ref(v___x_3050_);
v___x_3051_ = lean_array_push(v___x_3050_, v_a_3047_);
lean_inc_ref(v_letMuts_3036_);
v___x_3052_ = lean_array_push(v___x_3051_, v_letMuts_3036_);
v___x_3053_ = l_Lean_Meta_mkAppM(v___x_3048_, v___x_3052_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = l_Lean_Meta_mkSome(v_fst_3028_, v_r_3029_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
lean_inc_ref(v___x_3050_);
v___x_3057_ = lean_array_push(v___x_3050_, v_a_3056_);
v___x_3058_ = lean_array_push(v___x_3057_, v_letMuts_3036_);
v___x_3059_ = l_Lean_Meta_mkAppM(v___x_3048_, v___x_3058_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_3044_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3063_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref_known(v___x_3061_, 1);
v___x_3063_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3044_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3063_, 1);
v___x_3065_ = lean_unsigned_to_nat(100000u);
v___x_3066_ = 0;
v___x_3067_ = 0;
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3069_, 0, v___x_3065_);
lean_ctor_set(v___x_3069_, 1, v___x_3049_);
lean_ctor_set(v___x_3069_, 2, v___x_3068_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 1, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 2, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 3, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 4, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 5, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 6, v___x_3067_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 7, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 8, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 9, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 10, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 11, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 12, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 13, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 14, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 15, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 16, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 17, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 18, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 19, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 20, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 21, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 22, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 23, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 24, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 25, v___x_3030_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 26, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 27, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 28, v___x_3066_);
v___x_3070_ = lean_mk_empty_array_with_capacity(v___x_3031_);
lean_inc_ref(v___x_3070_);
v___x_3071_ = lean_array_push(v___x_3070_, v_a_3062_);
v___x_3072_ = l_Lean_Options_empty;
v___x_3073_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3069_, v___x_3071_, v_a_3064_, v___x_3072_, v___y_3041_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
v___x_3075_ = lean_mk_empty_array_with_capacity(v___x_3032_);
v___x_3076_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_3077_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_3075_, v___x_3076_, v___x_3066_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; size_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_n(v_a_3078_, 2);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = lean_array_push(v___x_3050_, v_xs_3033_);
v___x_3080_ = lean_array_push(v___x_3079_, v_a_3054_);
v___x_3081_ = l_Lean_Expr_beta(v_fst_3034_, v___x_3080_);
v___x_3082_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_3032_, 2);
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___x_3032_);
v___x_3084_ = lean_unsigned_to_nat(32u);
v___x_3085_ = lean_mk_empty_array_with_capacity(v___x_3084_);
v___x_3086_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_3087_ = ((size_t)5ULL);
v___x_3088_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3088_, 0, v___x_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_3085_);
lean_ctor_set(v___x_3088_, 2, v___x_3032_);
lean_ctor_set(v___x_3088_, 3, v___x_3032_);
lean_ctor_set_usize(v___x_3088_, 4, v___x_3087_);
v___x_3089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3082_);
lean_ctor_set(v___x_3089_, 1, v___x_3082_);
lean_ctor_set(v___x_3089_, 2, v___x_3082_);
lean_ctor_set(v___x_3089_, 3, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3083_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
lean_inc(v_a_3074_);
v___x_3091_ = l_Lean_Meta_simp(v___x_3081_, v_a_3074_, v_a_3078_, v___x_3068_, v___x_3090_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v_fst_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v___x_3091_, 1);
v_fst_3093_ = lean_ctor_get(v_a_3092_, 0);
lean_inc(v_fst_3093_);
lean_dec(v_a_3092_);
v___x_3094_ = lean_array_push(v___x_3070_, v_a_3060_);
v___x_3095_ = l_Lean_Expr_beta(v_fst_3035_, v___x_3094_);
v___x_3096_ = l_Lean_Meta_simp(v___x_3095_, v_a_3074_, v_a_3078_, v___x_3068_, v___x_3090_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec_ref_known(v___x_3090_, 2);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v_fst_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3135_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v_fst_3098_ = lean_ctor_get(v_a_3097_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_a_3097_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v_a_3097_, 1);
lean_dec(v_unused_3136_);
v___x_3100_ = v_a_3097_;
v_isShared_3101_ = v_isSharedCheck_3135_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_fst_3098_);
lean_dec(v_a_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3135_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v_expr_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_expr_3102_ = lean_ctor_get(v_fst_3093_, 0);
lean_inc_ref(v_expr_3102_);
lean_dec(v_fst_3093_);
v___x_3103_ = lean_box(1);
v___x_3104_ = l_Lean_PrettyPrinter_delab(v_expr_3102_, v___x_3103_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_expr_3106_; lean_object* v___x_3107_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v_expr_3106_ = lean_ctor_get(v_fst_3098_, 0);
lean_inc_ref(v_expr_3106_);
lean_dec(v_fst_3098_);
v___x_3107_ = l_Lean_PrettyPrinter_delab(v_expr_3106_, v___x_3103_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3118_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3118_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3118_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 1, v_a_3108_);
lean_ctor_set(v___x_3100_, 0, v_a_3105_);
v___x_3113_ = v___x_3100_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3105_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3115_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3113_);
v___x_3115_ = v___x_3110_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_a_3105_);
lean_del_object(v___x_3100_);
v_a_3119_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3107_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3107_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_del_object(v___x_3100_);
lean_dec(v_fst_3098_);
v_a_3127_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3104_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3104_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_fst_3093_);
v_a_3137_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3096_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3096_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref_known(v___x_3090_, 2);
lean_dec(v_a_3078_);
lean_dec(v_a_3074_);
lean_dec_ref(v___x_3070_);
lean_dec(v_a_3060_);
lean_dec_ref(v_fst_3035_);
v_a_3145_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3091_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3091_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_a_3074_);
lean_dec_ref(v___x_3070_);
lean_dec(v_a_3060_);
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_fst_3035_);
lean_dec_ref(v_fst_3034_);
lean_dec_ref(v_xs_3033_);
lean_dec(v___x_3032_);
v_a_3153_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3077_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3077_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec_ref(v___x_3070_);
lean_dec(v_a_3060_);
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_fst_3035_);
lean_dec_ref(v_fst_3034_);
lean_dec_ref(v_xs_3033_);
lean_dec(v___x_3032_);
v_a_3161_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3073_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3073_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_a_3062_);
lean_dec(v_a_3060_);
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_fst_3035_);
lean_dec_ref(v_fst_3034_);
lean_dec_ref(v_xs_3033_);
lean_dec(v___x_3032_);
v_a_3169_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3063_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3063_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_a_3060_);
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_fst_3035_);
lean_dec_ref(v_fst_3034_);
lean_dec_ref(v_xs_3033_);
lean_dec(v___x_3032_);
v_a_3177_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3061_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3061_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_fst_3035_);
lean_dec_ref(v_fst_3034_);
lean_dec_ref(v_xs_3033_);
lean_dec(v___x_3032_);
v_a_3185_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3059_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3059_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_letMuts_3036_);
lean_dec_ref(v_fst_3035_);
lean_dec_ref(v_fst_3034_);
lean_dec_ref(v_xs_3033_);
lean_dec(v___x_3032_);
v_a_3193_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3055_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3055_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_letMuts_3036_);
lean_dec_ref(v_fst_3035_);
lean_dec_ref(v_fst_3034_);
lean_dec_ref(v_xs_3033_);
lean_dec(v___x_3032_);
lean_dec_ref(v_r_3029_);
lean_dec_ref(v_fst_3028_);
v_a_3201_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3053_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3053_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v_letMuts_3036_);
lean_dec_ref(v_fst_3035_);
lean_dec_ref(v_fst_3034_);
lean_dec_ref(v_xs_3033_);
lean_dec(v___x_3032_);
lean_dec_ref(v_r_3029_);
lean_dec_ref(v_fst_3028_);
v_a_3209_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3046_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3046_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3217_ = _args[0];
lean_object* v_r_3218_ = _args[1];
lean_object* v___x_3219_ = _args[2];
lean_object* v___x_3220_ = _args[3];
lean_object* v___x_3221_ = _args[4];
lean_object* v_xs_3222_ = _args[5];
lean_object* v_fst_3223_ = _args[6];
lean_object* v_fst_3224_ = _args[7];
lean_object* v_letMuts_3225_ = _args[8];
lean_object* v___y_3226_ = _args[9];
lean_object* v___y_3227_ = _args[10];
lean_object* v___y_3228_ = _args[11];
lean_object* v___y_3229_ = _args[12];
lean_object* v___y_3230_ = _args[13];
lean_object* v___y_3231_ = _args[14];
lean_object* v___y_3232_ = _args[15];
lean_object* v___y_3233_ = _args[16];
lean_object* v___y_3234_ = _args[17];
_start:
{
uint8_t v___x_92439__boxed_3235_; lean_object* v_res_3236_; 
v___x_92439__boxed_3235_ = lean_unbox(v___x_3219_);
v_res_3236_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3217_, v_r_3218_, v___x_92439__boxed_3235_, v___x_3220_, v___x_3221_, v_xs_3222_, v_fst_3223_, v_fst_3224_, v_letMuts_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___x_3220_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3237_, uint8_t v___x_3238_, lean_object* v___x_3239_, lean_object* v___x_3240_, lean_object* v_xs_3241_, lean_object* v_fst_3242_, lean_object* v_fst_3243_, lean_object* v_snd_3244_, lean_object* v_r_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v___x_3255_; lean_object* v___f_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3255_ = lean_box(v___x_3238_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3256_, 0, v_fst_3237_);
lean_closure_set(v___f_3256_, 1, v_r_3245_);
lean_closure_set(v___f_3256_, 2, v___x_3255_);
lean_closure_set(v___f_3256_, 3, v___x_3239_);
lean_closure_set(v___f_3256_, 4, v___x_3240_);
lean_closure_set(v___f_3256_, 5, v_xs_3241_);
lean_closure_set(v___f_3256_, 6, v_fst_3242_);
lean_closure_set(v___f_3256_, 7, v_fst_3243_);
v___x_3257_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3258_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3257_, v_snd_3244_, v___f_3256_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3259_ = _args[0];
lean_object* v___x_3260_ = _args[1];
lean_object* v___x_3261_ = _args[2];
lean_object* v___x_3262_ = _args[3];
lean_object* v_xs_3263_ = _args[4];
lean_object* v_fst_3264_ = _args[5];
lean_object* v_fst_3265_ = _args[6];
lean_object* v_snd_3266_ = _args[7];
lean_object* v_r_3267_ = _args[8];
lean_object* v___y_3268_ = _args[9];
lean_object* v___y_3269_ = _args[10];
lean_object* v___y_3270_ = _args[11];
lean_object* v___y_3271_ = _args[12];
lean_object* v___y_3272_ = _args[13];
lean_object* v___y_3273_ = _args[14];
lean_object* v___y_3274_ = _args[15];
lean_object* v___y_3275_ = _args[16];
lean_object* v___y_3276_ = _args[17];
_start:
{
uint8_t v___x_92835__boxed_3277_; lean_object* v_res_3278_; 
v___x_92835__boxed_3277_ = lean_unbox(v___x_3260_);
v_res_3278_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3259_, v___x_92835__boxed_3277_, v___x_3261_, v___x_3262_, v_xs_3263_, v_fst_3264_, v_fst_3265_, v_snd_3266_, v_r_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3282_, uint8_t v___x_3283_, lean_object* v___x_3284_, lean_object* v___x_3285_, lean_object* v_fst_3286_, lean_object* v_fst_3287_, lean_object* v_snd_3288_, lean_object* v_xs_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; lean_object* v___f_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3299_ = lean_box(v___x_3283_);
lean_inc_ref(v_fst_3282_);
v___f_3300_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3300_, 0, v_fst_3282_);
lean_closure_set(v___f_3300_, 1, v___x_3299_);
lean_closure_set(v___f_3300_, 2, v___x_3284_);
lean_closure_set(v___f_3300_, 3, v___x_3285_);
lean_closure_set(v___f_3300_, 4, v_xs_3289_);
lean_closure_set(v___f_3300_, 5, v_fst_3286_);
lean_closure_set(v___f_3300_, 6, v_fst_3287_);
lean_closure_set(v___f_3300_, 7, v_snd_3288_);
v___x_3301_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3302_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3301_, v_fst_3282_, v___f_3300_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3303_ = _args[0];
lean_object* v___x_3304_ = _args[1];
lean_object* v___x_3305_ = _args[2];
lean_object* v___x_3306_ = _args[3];
lean_object* v_fst_3307_ = _args[4];
lean_object* v_fst_3308_ = _args[5];
lean_object* v_snd_3309_ = _args[6];
lean_object* v_xs_3310_ = _args[7];
lean_object* v___y_3311_ = _args[8];
lean_object* v___y_3312_ = _args[9];
lean_object* v___y_3313_ = _args[10];
lean_object* v___y_3314_ = _args[11];
lean_object* v___y_3315_ = _args[12];
lean_object* v___y_3316_ = _args[13];
lean_object* v___y_3317_ = _args[14];
lean_object* v___y_3318_ = _args[15];
lean_object* v___y_3319_ = _args[16];
_start:
{
uint8_t v___x_92898__boxed_3320_; lean_object* v_res_3321_; 
v___x_92898__boxed_3320_ = lean_unbox(v___x_3304_);
v_res_3321_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3303_, v___x_92898__boxed_3320_, v___x_3305_, v___x_3306_, v_fst_3307_, v_fst_3308_, v_snd_3309_, v_xs_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3322_, size_t v_sz_3323_, size_t v_i_3324_, lean_object* v_b_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_usize_dec_lt(v_i_3324_, v_sz_3323_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3332_, 0, v_b_3325_);
return v___x_3332_;
}
else
{
lean_object* v___x_3333_; lean_object* v_a_3334_; lean_object* v___x_3335_; 
v___x_3333_ = lean_box(1);
v_a_3334_ = lean_array_uget_borrowed(v_as_3322_, v_i_3324_);
lean_inc(v_a_3334_);
v___x_3335_ = l_Lean_PrettyPrinter_delab(v_a_3334_, v___x_3333_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; size_t v___x_3338_; size_t v___x_3339_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = lean_array_push(v_b_3325_, v_a_3336_);
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3324_, v___x_3338_);
v_i_3324_ = v___x_3339_;
v_b_3325_ = v___x_3337_;
goto _start;
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v_b_3325_);
v_a_3341_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3335_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3335_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3349_, lean_object* v_sz_3350_, lean_object* v_i_3351_, lean_object* v_b_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
size_t v_sz_boxed_3358_; size_t v_i_boxed_3359_; lean_object* v_res_3360_; 
v_sz_boxed_3358_ = lean_unbox_usize(v_sz_3350_);
lean_dec(v_sz_3350_);
v_i_boxed_3359_ = lean_unbox_usize(v_i_3351_);
lean_dec(v_i_3351_);
v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3349_, v_sz_boxed_3358_, v_i_boxed_3359_, v_b_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec_ref(v_as_3349_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3381_, lean_object* v_fst_3382_, lean_object* v_snd_3383_, lean_object* v___x_3384_, lean_object* v___x_3385_, lean_object* v___x_3386_, lean_object* v___x_3387_, lean_object* v___x_3388_, lean_object* v___x_3389_, lean_object* v___x_3390_, uint8_t v___x_3391_, lean_object* v___x_3392_, lean_object* v_letMuts_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3403_ = lean_unsigned_to_nat(2u);
v___x_3404_ = lean_mk_empty_array_with_capacity(v___x_3403_);
v___x_3405_ = lean_array_push(v___x_3404_, v_xs_3381_);
v___x_3406_ = lean_array_push(v___x_3405_, v_letMuts_3393_);
v___x_3407_ = l_Lean_Expr_beta(v_fst_3382_, v___x_3406_);
v___x_3408_ = lean_box(1);
v___x_3409_ = l_Lean_PrettyPrinter_delab(v___x_3407_, v___x_3408_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3548_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3548_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3548_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
uint8_t v___y_3415_; lean_object* v_points_3451_; lean_object* v_default_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3547_; 
v_points_3451_ = lean_ctor_get(v_snd_3383_, 0);
v_default_3452_ = lean_ctor_get(v_snd_3383_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_snd_3383_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3454_ = v_snd_3383_;
v_isShared_3455_ = v_isSharedCheck_3547_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_default_3452_);
lean_inc(v_points_3451_);
lean_dec(v_snd_3383_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3547_;
goto v_resetjp_3453_;
}
v___jp_3414_:
{
lean_object* v_ref_3416_; lean_object* v_quotContext_3417_; lean_object* v_currMacroScope_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
v_ref_3416_ = lean_ctor_get(v___y_3400_, 5);
v_quotContext_3417_ = lean_ctor_get(v___y_3400_, 10);
v_currMacroScope_3418_ = lean_ctor_get(v___y_3400_, 11);
v___x_3419_ = l_Lean_SourceInfo_fromRef(v_ref_3416_, v___y_3415_);
v___x_3420_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3421_ = l_Lean_Name_mkStr3(v___x_3384_, v___x_3385_, v___x_3420_);
v___x_3422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3423_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3419_, 11);
v___x_3424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3419_);
lean_ctor_set(v___x_3424_, 1, v___x_3422_);
lean_ctor_set(v___x_3424_, 2, v___x_3423_);
v___x_3425_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3419_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3419_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_String_toRawSubstring_x27(v___x_3386_);
lean_inc_n(v_currMacroScope_3418_, 2);
lean_inc_n(v_quotContext_3417_, 2);
v___x_3432_ = l_Lean_addMacroScope(v_quotContext_3417_, v___x_3387_, v_currMacroScope_3418_);
v___x_3433_ = lean_box(0);
v___x_3434_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3419_);
lean_ctor_set(v___x_3434_, 1, v___x_3431_);
lean_ctor_set(v___x_3434_, 2, v___x_3432_);
lean_ctor_set(v___x_3434_, 3, v___x_3433_);
v___x_3435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3419_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = l_String_toRawSubstring_x27(v___x_3388_);
v___x_3438_ = l_Lean_addMacroScope(v_quotContext_3417_, v___x_3389_, v_currMacroScope_3418_);
v___x_3439_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3419_);
lean_ctor_set(v___x_3439_, 1, v___x_3437_);
lean_ctor_set(v___x_3439_, 2, v___x_3438_);
lean_ctor_set(v___x_3439_, 3, v___x_3433_);
v___x_3440_ = l_Lean_Syntax_node3(v___x_3419_, v___x_3427_, v___x_3434_, v___x_3436_, v___x_3439_);
v___x_3441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3419_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = l_Lean_Syntax_node3(v___x_3419_, v___x_3428_, v___x_3430_, v___x_3440_, v___x_3442_);
v___x_3444_ = l_Lean_Syntax_node1(v___x_3419_, v___x_3427_, v___x_3443_);
v___x_3445_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3419_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = l_Lean_Syntax_node5(v___x_3419_, v___x_3421_, v___x_3424_, v___x_3426_, v___x_3444_, v___x_3446_, v_a_3410_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3447_);
v___x_3449_ = v___x_3412_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
v_resetjp_3453_:
{
uint8_t v___y_3457_; uint8_t v___y_3508_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3544_ = lean_array_get_size(v_points_3451_);
v___x_3545_ = lean_nat_dec_eq(v___x_3544_, v___x_3392_);
if (v___x_3545_ == 0)
{
v___y_3508_ = v___x_3545_;
goto v___jp_3507_;
}
else
{
if (lean_obj_tag(v_default_3452_) == 3)
{
if (v___x_3545_ == 0)
{
v___y_3508_ = v___x_3545_;
goto v___jp_3507_;
}
else
{
uint8_t v___x_3546_; 
lean_del_object(v___x_3412_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3384_);
v___x_3546_ = 0;
v___y_3457_ = v___x_3546_;
goto v___jp_3456_;
}
}
else
{
v___y_3508_ = v___x_3545_;
goto v___jp_3507_;
}
}
v___jp_3456_:
{
lean_object* v_ref_3458_; lean_object* v_quotContext_3459_; lean_object* v_currMacroScope_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v_ref_3458_ = lean_ctor_get(v___y_3400_, 5);
v_quotContext_3459_ = lean_ctor_get(v___y_3400_, 10);
v_currMacroScope_3460_ = lean_ctor_get(v___y_3400_, 11);
v___x_3461_ = l_Lean_SourceInfo_fromRef(v_ref_3458_, v___y_3457_);
v___x_3462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3463_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3461_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set_tag(v___x_3454_, 2);
lean_ctor_set(v___x_3454_, 1, v___x_3462_);
lean_ctor_set(v___x_3454_, 0, v___x_3461_);
v___x_3465_ = v___x_3454_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3462_);
v___x_3465_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; size_t v_sz_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3466_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3461_, 11);
v___x_3470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3461_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_String_toRawSubstring_x27(v___x_3386_);
lean_inc_n(v_currMacroScope_3460_, 2);
lean_inc_n(v_quotContext_3459_, 2);
v___x_3472_ = l_Lean_addMacroScope(v_quotContext_3459_, v___x_3387_, v_currMacroScope_3460_);
v___x_3473_ = lean_box(0);
v___x_3474_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3461_);
lean_ctor_set(v___x_3474_, 1, v___x_3471_);
lean_ctor_set(v___x_3474_, 2, v___x_3472_);
lean_ctor_set(v___x_3474_, 3, v___x_3473_);
v___x_3475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3461_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l_String_toRawSubstring_x27(v___x_3388_);
v___x_3478_ = l_Lean_addMacroScope(v_quotContext_3459_, v___x_3389_, v_currMacroScope_3460_);
v___x_3479_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3461_);
lean_ctor_set(v___x_3479_, 1, v___x_3477_);
lean_ctor_set(v___x_3479_, 2, v___x_3478_);
lean_ctor_set(v___x_3479_, 3, v___x_3473_);
v___x_3480_ = l_Lean_Syntax_node3(v___x_3461_, v___x_3467_, v___x_3474_, v___x_3476_, v___x_3479_);
v___x_3481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3461_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = l_Lean_Syntax_node3(v___x_3461_, v___x_3468_, v___x_3470_, v___x_3480_, v___x_3482_);
v___x_3484_ = l_Lean_Syntax_node1(v___x_3461_, v___x_3467_, v___x_3483_);
v___x_3485_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3461_);
lean_ctor_set(v___x_3486_, 1, v___x_3467_);
lean_ctor_set(v___x_3486_, 2, v___x_3485_);
v___x_3487_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3461_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = l_Lean_Syntax_node4(v___x_3461_, v___x_3466_, v___x_3484_, v___x_3486_, v___x_3488_, v_a_3410_);
v___x_3490_ = l_Lean_Syntax_node2(v___x_3461_, v___x_3463_, v___x_3465_, v___x_3489_);
v___x_3491_ = lean_mk_empty_array_with_capacity(v___x_3390_);
v___x_3492_ = lean_array_push(v___x_3491_, v___x_3490_);
v_sz_3493_ = lean_array_size(v_points_3451_);
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3451_, v_sz_3493_, v___x_3494_, v___x_3492_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec_ref(v_points_3451_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3496_, v_default_3452_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v_a_3496_);
return v___x_3497_;
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec(v_default_3452_);
v_a_3498_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3495_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3495_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
v___jp_3507_:
{
if (v___y_3508_ == 0)
{
lean_del_object(v___x_3412_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3384_);
v___y_3457_ = v___y_3508_;
goto v___jp_3456_;
}
else
{
lean_del_object(v___x_3454_);
lean_dec_ref(v_points_3451_);
if (lean_obj_tag(v_default_3452_) == 2)
{
if (v___x_3391_ == 0)
{
v___y_3415_ = v___x_3391_;
goto v___jp_3414_;
}
else
{
lean_object* v_ref_3509_; lean_object* v_quotContext_3510_; lean_object* v_currMacroScope_3511_; uint8_t v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_del_object(v___x_3412_);
v_ref_3509_ = lean_ctor_get(v___y_3400_, 5);
v_quotContext_3510_ = lean_ctor_get(v___y_3400_, 10);
v_currMacroScope_3511_ = lean_ctor_get(v___y_3400_, 11);
v___x_3512_ = 0;
v___x_3513_ = l_Lean_SourceInfo_fromRef(v_ref_3509_, v___x_3512_);
v___x_3514_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3515_ = l_Lean_Name_mkStr3(v___x_3384_, v___x_3385_, v___x_3514_);
v___x_3516_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3513_, 11);
v___x_3518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3513_);
lean_ctor_set(v___x_3518_, 1, v___x_3516_);
lean_ctor_set(v___x_3518_, 2, v___x_3517_);
v___x_3519_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3513_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3513_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_String_toRawSubstring_x27(v___x_3386_);
lean_inc_n(v_currMacroScope_3511_, 2);
lean_inc_n(v_quotContext_3510_, 2);
v___x_3526_ = l_Lean_addMacroScope(v_quotContext_3510_, v___x_3387_, v_currMacroScope_3511_);
v___x_3527_ = lean_box(0);
v___x_3528_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3513_);
lean_ctor_set(v___x_3528_, 1, v___x_3525_);
lean_ctor_set(v___x_3528_, 2, v___x_3526_);
lean_ctor_set(v___x_3528_, 3, v___x_3527_);
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3513_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = l_String_toRawSubstring_x27(v___x_3388_);
v___x_3532_ = l_Lean_addMacroScope(v_quotContext_3510_, v___x_3389_, v_currMacroScope_3511_);
v___x_3533_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3513_);
lean_ctor_set(v___x_3533_, 1, v___x_3531_);
lean_ctor_set(v___x_3533_, 2, v___x_3532_);
lean_ctor_set(v___x_3533_, 3, v___x_3527_);
v___x_3534_ = l_Lean_Syntax_node3(v___x_3513_, v___x_3521_, v___x_3528_, v___x_3530_, v___x_3533_);
v___x_3535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3513_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = l_Lean_Syntax_node3(v___x_3513_, v___x_3522_, v___x_3524_, v___x_3534_, v___x_3536_);
v___x_3538_ = l_Lean_Syntax_node1(v___x_3513_, v___x_3521_, v___x_3537_);
v___x_3539_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3513_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = l_Lean_Syntax_node5(v___x_3513_, v___x_3515_, v___x_3518_, v___x_3520_, v___x_3538_, v___x_3540_, v_a_3410_);
v___x_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
return v___x_3542_;
}
}
else
{
uint8_t v___x_3543_; 
lean_dec(v_default_3452_);
v___x_3543_ = 0;
v___y_3415_ = v___x_3543_;
goto v___jp_3414_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3389_);
lean_dec_ref(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v___x_3386_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3384_);
lean_dec_ref(v_snd_3383_);
return v___x_3409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3549_ = _args[0];
lean_object* v_fst_3550_ = _args[1];
lean_object* v_snd_3551_ = _args[2];
lean_object* v___x_3552_ = _args[3];
lean_object* v___x_3553_ = _args[4];
lean_object* v___x_3554_ = _args[5];
lean_object* v___x_3555_ = _args[6];
lean_object* v___x_3556_ = _args[7];
lean_object* v___x_3557_ = _args[8];
lean_object* v___x_3558_ = _args[9];
lean_object* v___x_3559_ = _args[10];
lean_object* v___x_3560_ = _args[11];
lean_object* v_letMuts_3561_ = _args[12];
lean_object* v___y_3562_ = _args[13];
lean_object* v___y_3563_ = _args[14];
lean_object* v___y_3564_ = _args[15];
lean_object* v___y_3565_ = _args[16];
lean_object* v___y_3566_ = _args[17];
lean_object* v___y_3567_ = _args[18];
lean_object* v___y_3568_ = _args[19];
lean_object* v___y_3569_ = _args[20];
lean_object* v___y_3570_ = _args[21];
_start:
{
uint8_t v___x_93107__boxed_3571_; lean_object* v_res_3572_; 
v___x_93107__boxed_3571_ = lean_unbox(v___x_3559_);
v_res_3572_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3549_, v_fst_3550_, v_snd_3551_, v___x_3552_, v___x_3553_, v___x_3554_, v___x_3555_, v___x_3556_, v___x_3557_, v___x_3558_, v___x_93107__boxed_3571_, v___x_3560_, v_letMuts_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___x_3560_);
lean_dec(v___x_3558_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3573_, lean_object* v_snd_3574_, lean_object* v___x_3575_, lean_object* v___x_3576_, lean_object* v___x_3577_, lean_object* v___x_3578_, lean_object* v___x_3579_, uint8_t v___x_3580_, lean_object* v___x_3581_, lean_object* v_arg_3582_, lean_object* v_xs_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___f_3596_; lean_object* v___x_3597_; 
v___x_3593_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3594_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3595_ = lean_box(v___x_3580_);
v___f_3596_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3596_, 0, v_xs_3583_);
lean_closure_set(v___f_3596_, 1, v_fst_3573_);
lean_closure_set(v___f_3596_, 2, v_snd_3574_);
lean_closure_set(v___f_3596_, 3, v___x_3575_);
lean_closure_set(v___f_3596_, 4, v___x_3576_);
lean_closure_set(v___f_3596_, 5, v___x_3577_);
lean_closure_set(v___f_3596_, 6, v___x_3578_);
lean_closure_set(v___f_3596_, 7, v___x_3593_);
lean_closure_set(v___f_3596_, 8, v___x_3594_);
lean_closure_set(v___f_3596_, 9, v___x_3579_);
lean_closure_set(v___f_3596_, 10, v___x_3595_);
lean_closure_set(v___f_3596_, 11, v___x_3581_);
v___x_3597_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3594_, v_arg_3582_, v___f_3596_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3598_ = _args[0];
lean_object* v_snd_3599_ = _args[1];
lean_object* v___x_3600_ = _args[2];
lean_object* v___x_3601_ = _args[3];
lean_object* v___x_3602_ = _args[4];
lean_object* v___x_3603_ = _args[5];
lean_object* v___x_3604_ = _args[6];
lean_object* v___x_3605_ = _args[7];
lean_object* v___x_3606_ = _args[8];
lean_object* v_arg_3607_ = _args[9];
lean_object* v_xs_3608_ = _args[10];
lean_object* v___y_3609_ = _args[11];
lean_object* v___y_3610_ = _args[12];
lean_object* v___y_3611_ = _args[13];
lean_object* v___y_3612_ = _args[14];
lean_object* v___y_3613_ = _args[15];
lean_object* v___y_3614_ = _args[16];
lean_object* v___y_3615_ = _args[17];
lean_object* v___y_3616_ = _args[18];
lean_object* v___y_3617_ = _args[19];
_start:
{
uint8_t v___x_93457__boxed_3618_; lean_object* v_res_3619_; 
v___x_93457__boxed_3618_ = lean_unbox(v___x_3605_);
v_res_3619_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3598_, v_snd_3599_, v___x_3600_, v___x_3601_, v___x_3602_, v___x_3603_, v___x_3604_, v___x_93457__boxed_3618_, v___x_3606_, v_arg_3607_, v_xs_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3620_, size_t v_sz_3621_, size_t v_i_3622_, lean_object* v_b_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
uint8_t v___x_3629_; 
v___x_3629_ = lean_usize_dec_lt(v_i_3622_, v_sz_3621_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; 
v___x_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3630_, 0, v_b_3623_);
return v___x_3630_;
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_a_3631_ = lean_array_uget_borrowed(v_as_3620_, v_i_3622_);
v___x_3632_ = lean_box(1);
lean_inc(v_a_3631_);
v___x_3633_ = l_Lean_PrettyPrinter_delab(v_a_3631_, v___x_3632_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; size_t v___x_3636_; size_t v___x_3637_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___x_3635_ = lean_array_push(v_b_3623_, v_a_3634_);
v___x_3636_ = ((size_t)1ULL);
v___x_3637_ = lean_usize_add(v_i_3622_, v___x_3636_);
v_i_3622_ = v___x_3637_;
v_b_3623_ = v___x_3635_;
goto _start;
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v_b_3623_);
v_a_3639_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3633_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3633_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3647_, lean_object* v_sz_3648_, lean_object* v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
size_t v_sz_boxed_3656_; size_t v_i_boxed_3657_; lean_object* v_res_3658_; 
v_sz_boxed_3656_ = lean_unbox_usize(v_sz_3648_);
lean_dec(v_sz_3648_);
v_i_boxed_3657_ = lean_unbox_usize(v_i_3649_);
lean_dec(v_i_3649_);
v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3647_, v_sz_boxed_3656_, v_i_boxed_3657_, v_b_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_as_3647_);
return v_res_3658_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3667_ = l_String_toRawSubstring_x27(v___x_3666_);
return v___x_3667_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3678_ = l_String_toRawSubstring_x27(v___x_3677_);
return v___x_3678_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3683_ = l_String_toRawSubstring_x27(v___x_3682_);
return v___x_3683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3685_ = l_String_toRawSubstring_x27(v___x_3684_);
return v___x_3685_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3689_ = l_String_toRawSubstring_x27(v___x_3688_);
return v___x_3689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3694_ = l_String_toRawSubstring_x27(v___x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3704_, lean_object* v___x_3705_, lean_object* v___f_3706_, lean_object* v_a_3707_, lean_object* v_inv_3708_, lean_object* v_arg_3709_, uint8_t v___x_3710_, lean_object* v___x_3711_, lean_object* v___x_3712_, lean_object* v___x_3713_, lean_object* v___x_3714_, lean_object* v___x_3715_, lean_object* v___x_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_a_3727_; lean_object* v___y_3731_; lean_object* v___x_3733_; 
lean_inc_ref(v___x_3705_);
lean_inc(v___x_3704_);
v___x_3733_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3704_, v___x_3705_, v___f_3706_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3707_, v_inv_3708_, v_arg_3709_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
if (lean_obj_tag(v_a_3736_) == 1)
{
lean_object* v_val_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_4217_; 
lean_dec_ref(v_arg_3709_);
v_val_3737_ = lean_ctor_get(v_a_3736_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v_a_3736_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_3739_ = v_a_3736_;
v_isShared_3740_ = v_isSharedCheck_4217_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_val_3737_);
lean_dec(v_a_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_4217_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
if (lean_obj_tag(v_a_3734_) == 1)
{
lean_object* v_val_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_4140_; 
lean_del_object(v___x_3739_);
v_val_3741_ = lean_ctor_get(v_a_3734_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_a_3734_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_3743_ = v_a_3734_;
v_isShared_3744_ = v_isSharedCheck_4140_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_val_3741_);
lean_dec(v_a_3734_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_4140_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v_snd_3745_; lean_object* v_fst_3746_; lean_object* v_snd_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_4139_; 
v_snd_3745_ = lean_ctor_get(v_val_3741_, 1);
lean_inc(v_snd_3745_);
v_fst_3746_ = lean_ctor_get(v_val_3737_, 0);
v_snd_3747_ = lean_ctor_get(v_val_3737_, 1);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_val_3737_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_3749_ = v_val_3737_;
v_isShared_3750_ = v_isSharedCheck_4139_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_snd_3747_);
lean_inc(v_fst_3746_);
lean_dec(v_val_3737_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_4139_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v_fst_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_4137_; 
v_fst_3751_ = lean_ctor_get(v_val_3741_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_val_3741_);
if (v_isSharedCheck_4137_ == 0)
{
lean_object* v_unused_4138_; 
v_unused_4138_ = lean_ctor_get(v_val_3741_, 1);
lean_dec(v_unused_4138_);
v___x_3753_ = v_val_3741_;
v_isShared_3754_ = v_isSharedCheck_4137_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_fst_3751_);
lean_dec(v_val_3741_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_4137_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v_fst_3755_; lean_object* v_snd_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_4136_; 
v_fst_3755_ = lean_ctor_get(v_snd_3745_, 0);
v_snd_3756_ = lean_ctor_get(v_snd_3745_, 1);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_snd_3745_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_3758_ = v_snd_3745_;
v_isShared_3759_ = v_isSharedCheck_4136_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_snd_3756_);
lean_inc(v_fst_3755_);
lean_dec(v_snd_3745_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_4136_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3760_; lean_object* v___f_3761_; lean_object* v___x_3762_; 
v___x_3760_ = lean_box(v___x_3710_);
lean_inc(v___x_3712_);
v___f_3761_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3761_, 0, v_fst_3746_);
lean_closure_set(v___f_3761_, 1, v___x_3760_);
lean_closure_set(v___f_3761_, 2, v___x_3711_);
lean_closure_set(v___f_3761_, 3, v___x_3712_);
lean_closure_set(v___f_3761_, 4, v_fst_3751_);
lean_closure_set(v___f_3761_, 5, v_fst_3755_);
lean_closure_set(v___f_3761_, 6, v_snd_3747_);
lean_inc(v___x_3704_);
v___x_3762_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3704_, v___x_3705_, v___f_3761_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v_fst_3764_; lean_object* v_snd_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_4127_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref_known(v___x_3762_, 1);
v_fst_3764_ = lean_ctor_get(v_a_3763_, 0);
v_snd_3765_ = lean_ctor_get(v_a_3763_, 1);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_a_3763_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_3767_ = v_a_3763_;
v_isShared_3768_ = v_isSharedCheck_4127_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_snd_3765_);
lean_inc(v_fst_3764_);
lean_dec(v_a_3763_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_4127_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v_points_3769_; lean_object* v_default_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_4126_; 
v_points_3769_ = lean_ctor_get(v_snd_3756_, 0);
v_default_3770_ = lean_ctor_get(v_snd_3756_, 1);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_snd_3756_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_3772_ = v_snd_3756_;
v_isShared_3773_ = v_isSharedCheck_4126_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_default_3770_);
lean_inc(v_points_3769_);
lean_dec(v_snd_3756_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_4126_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; uint8_t v___x_3775_; 
v___x_3774_ = lean_array_get_size(v_points_3769_);
v___x_3775_ = lean_nat_dec_eq(v___x_3774_, v___x_3712_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; size_t v_sz_3777_; size_t v___x_3778_; lean_object* v___x_3779_; 
lean_del_object(v___x_3743_);
v___x_3776_ = lean_mk_empty_array_with_capacity(v___x_3712_);
lean_dec(v___x_3712_);
v_sz_3777_ = lean_array_size(v_points_3769_);
v___x_3778_ = ((size_t)0ULL);
v___x_3779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3769_, v_sz_3777_, v___x_3778_, v___x_3776_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec_ref(v_points_3769_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3780_, v_default_3770_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v_a_3780_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3864_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3784_ = v___x_3781_;
v_isShared_3785_ = v_isSharedCheck_3864_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3864_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v_ref_3786_; lean_object* v_quotContext_3787_; lean_object* v_currMacroScope_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3798_; 
v_ref_3786_ = lean_ctor_get(v___y_3723_, 5);
lean_inc(v_ref_3786_);
v_quotContext_3787_ = lean_ctor_get(v___y_3723_, 10);
lean_inc_n(v_quotContext_3787_, 2);
v_currMacroScope_3788_ = lean_ctor_get(v___y_3723_, 11);
lean_inc_n(v_currMacroScope_3788_, 2);
lean_dec_ref(v___y_3723_);
v___x_3789_ = l_Lean_SourceInfo_fromRef(v_ref_3786_, v___x_3775_);
lean_dec(v_ref_3786_);
v___x_3790_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3791_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3792_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3713_);
v___x_3793_ = l_Lean_Name_mkStr2(v___x_3713_, v___x_3792_);
v___x_3794_ = l_Lean_addMacroScope(v_quotContext_3787_, v___x_3793_, v_currMacroScope_3788_);
v___x_3795_ = l_Lean_Name_mkStr4(v___x_3714_, v___x_3715_, v___x_3713_, v___x_3792_);
v___x_3796_ = lean_box(0);
lean_inc(v___x_3795_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set_tag(v___x_3772_, 1);
lean_ctor_set(v___x_3772_, 1, v___x_3796_);
lean_ctor_set(v___x_3772_, 0, v___x_3795_);
v___x_3798_ = v___x_3772_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3800_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3795_);
v___x_3800_ = v___x_3784_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3795_);
v___x_3800_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3802_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set_tag(v___x_3767_, 1);
lean_ctor_set(v___x_3767_, 1, v___x_3796_);
lean_ctor_set(v___x_3767_, 0, v___x_3800_);
v___x_3802_ = v___x_3767_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3800_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v___x_3796_);
v___x_3802_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3804_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 1);
lean_ctor_set(v___x_3758_, 1, v___x_3802_);
lean_ctor_set(v___x_3758_, 0, v___x_3798_);
v___x_3804_ = v___x_3758_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3810_; 
lean_inc_n(v___x_3789_, 2);
v___x_3805_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3789_);
lean_ctor_set(v___x_3805_, 1, v___x_3791_);
lean_ctor_set(v___x_3805_, 2, v___x_3794_);
lean_ctor_set(v___x_3805_, 3, v___x_3804_);
v___x_3806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3807_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3808_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3754_ == 0)
{
lean_ctor_set_tag(v___x_3753_, 2);
lean_ctor_set(v___x_3753_, 1, v___x_3808_);
lean_ctor_set(v___x_3753_, 0, v___x_3789_);
v___x_3810_ = v___x_3753_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3859_, 1, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3811_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3812_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3788_);
lean_inc(v_quotContext_3787_);
v___x_3813_ = l_Lean_addMacroScope(v_quotContext_3787_, v___x_3812_, v_currMacroScope_3788_);
lean_inc_n(v___x_3789_, 2);
v___x_3814_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3789_);
lean_ctor_set(v___x_3814_, 1, v___x_3811_);
lean_ctor_set(v___x_3814_, 2, v___x_3813_);
lean_ctor_set(v___x_3814_, 3, v___x_3796_);
v___x_3815_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 2);
lean_ctor_set(v___x_3749_, 1, v___x_3815_);
lean_ctor_set(v___x_3749_, 0, v___x_3789_);
v___x_3817_ = v___x_3749_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3818_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3819_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3789_, 19);
v___x_3820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3789_);
lean_ctor_set(v___x_3820_, 1, v___x_3818_);
v___x_3821_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3822_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3823_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3788_, 4);
lean_inc_n(v_quotContext_3787_, 4);
v___x_3824_ = l_Lean_addMacroScope(v_quotContext_3787_, v___x_3823_, v_currMacroScope_3788_);
v___x_3825_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3789_);
lean_ctor_set(v___x_3825_, 1, v___x_3822_);
lean_ctor_set(v___x_3825_, 2, v___x_3824_);
lean_ctor_set(v___x_3825_, 3, v___x_3796_);
v___x_3826_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3827_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3828_ = l_Lean_addMacroScope(v_quotContext_3787_, v___x_3827_, v_currMacroScope_3788_);
v___x_3829_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3789_);
lean_ctor_set(v___x_3829_, 1, v___x_3826_);
lean_ctor_set(v___x_3829_, 2, v___x_3828_);
lean_ctor_set(v___x_3829_, 3, v___x_3796_);
lean_inc_ref(v___x_3829_);
v___x_3830_ = l_Lean_Syntax_node2(v___x_3789_, v___x_3806_, v___x_3825_, v___x_3829_);
v___x_3831_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3789_);
lean_ctor_set(v___x_3832_, 1, v___x_3806_);
lean_ctor_set(v___x_3832_, 2, v___x_3831_);
v___x_3833_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3789_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
lean_inc_ref(v___x_3834_);
lean_inc_ref(v___x_3832_);
v___x_3835_ = l_Lean_Syntax_node4(v___x_3789_, v___x_3821_, v___x_3830_, v___x_3832_, v___x_3834_, v_snd_3765_);
lean_inc_ref(v___x_3820_);
v___x_3836_ = l_Lean_Syntax_node2(v___x_3789_, v___x_3819_, v___x_3820_, v___x_3835_);
v___x_3837_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3789_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
lean_inc_ref_n(v___x_3838_, 2);
lean_inc_ref_n(v___x_3817_, 2);
lean_inc_ref_n(v___x_3810_, 2);
v___x_3839_ = l_Lean_Syntax_node5(v___x_3789_, v___x_3807_, v___x_3810_, v___x_3814_, v___x_3817_, v___x_3836_, v___x_3838_);
v___x_3840_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3841_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3842_ = l_Lean_addMacroScope(v_quotContext_3787_, v___x_3841_, v_currMacroScope_3788_);
v___x_3843_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3789_);
lean_ctor_set(v___x_3843_, 1, v___x_3840_);
lean_ctor_set(v___x_3843_, 2, v___x_3842_);
lean_ctor_set(v___x_3843_, 3, v___x_3796_);
v___x_3844_ = l_String_toRawSubstring_x27(v___x_3716_);
v___x_3845_ = l_Lean_addMacroScope(v_quotContext_3787_, v___x_3704_, v_currMacroScope_3788_);
v___x_3846_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3789_);
lean_ctor_set(v___x_3846_, 1, v___x_3844_);
lean_ctor_set(v___x_3846_, 2, v___x_3845_);
lean_ctor_set(v___x_3846_, 3, v___x_3796_);
v___x_3847_ = l_Lean_Syntax_node2(v___x_3789_, v___x_3806_, v___x_3846_, v___x_3829_);
v___x_3848_ = l_Lean_Syntax_node4(v___x_3789_, v___x_3821_, v___x_3847_, v___x_3832_, v___x_3834_, v_fst_3764_);
v___x_3849_ = l_Lean_Syntax_node2(v___x_3789_, v___x_3819_, v___x_3820_, v___x_3848_);
v___x_3850_ = l_Lean_Syntax_node5(v___x_3789_, v___x_3807_, v___x_3810_, v___x_3843_, v___x_3817_, v___x_3849_, v___x_3838_);
v___x_3851_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3852_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3853_ = l_Lean_addMacroScope(v_quotContext_3787_, v___x_3852_, v_currMacroScope_3788_);
v___x_3854_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3789_);
lean_ctor_set(v___x_3854_, 1, v___x_3851_);
lean_ctor_set(v___x_3854_, 2, v___x_3853_);
lean_ctor_set(v___x_3854_, 3, v___x_3796_);
v___x_3855_ = l_Lean_Syntax_node5(v___x_3789_, v___x_3807_, v___x_3810_, v___x_3854_, v___x_3817_, v_a_3782_, v___x_3838_);
v___x_3856_ = l_Lean_Syntax_node3(v___x_3789_, v___x_3806_, v___x_3839_, v___x_3850_, v___x_3855_);
v___x_3857_ = l_Lean_Syntax_node2(v___x_3789_, v___x_3790_, v___x_3805_, v___x_3856_);
v_a_3727_ = v___x_3857_;
goto v___jp_3726_;
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
lean_del_object(v___x_3772_);
lean_del_object(v___x_3767_);
lean_dec(v_snd_3765_);
lean_dec(v_fst_3764_);
lean_del_object(v___x_3758_);
lean_del_object(v___x_3753_);
lean_del_object(v___x_3749_);
lean_dec_ref(v___y_3723_);
lean_dec_ref(v___x_3716_);
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
lean_dec_ref(v___x_3713_);
lean_dec(v___x_3704_);
v___y_3731_ = v___x_3781_;
goto v___jp_3730_;
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_del_object(v___x_3772_);
lean_dec(v_default_3770_);
lean_del_object(v___x_3767_);
lean_dec(v_snd_3765_);
lean_dec(v_fst_3764_);
lean_del_object(v___x_3758_);
lean_del_object(v___x_3753_);
lean_del_object(v___x_3749_);
lean_dec_ref(v___y_3723_);
lean_dec_ref(v___x_3716_);
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
lean_dec_ref(v___x_3713_);
lean_dec(v___x_3704_);
v_a_3865_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3779_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3779_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
else
{
lean_dec_ref(v_points_3769_);
lean_dec(v___x_3712_);
switch(lean_obj_tag(v_default_3770_))
{
case 2:
{
lean_object* v_ref_3873_; lean_object* v_quotContext_3874_; lean_object* v_currMacroScope_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v_ref_3873_ = lean_ctor_get(v___y_3723_, 5);
lean_inc(v_ref_3873_);
v_quotContext_3874_ = lean_ctor_get(v___y_3723_, 10);
lean_inc_n(v_quotContext_3874_, 2);
v_currMacroScope_3875_ = lean_ctor_get(v___y_3723_, 11);
lean_inc_n(v_currMacroScope_3875_, 2);
lean_dec_ref(v___y_3723_);
v___x_3876_ = 0;
v___x_3877_ = l_Lean_SourceInfo_fromRef(v_ref_3873_, v___x_3876_);
lean_dec(v_ref_3873_);
v___x_3878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3879_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3880_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3713_);
v___x_3881_ = l_Lean_Name_mkStr2(v___x_3713_, v___x_3880_);
v___x_3882_ = l_Lean_addMacroScope(v_quotContext_3874_, v___x_3881_, v_currMacroScope_3875_);
lean_inc_ref(v___x_3715_);
lean_inc_ref(v___x_3714_);
v___x_3883_ = l_Lean_Name_mkStr4(v___x_3714_, v___x_3715_, v___x_3713_, v___x_3880_);
v___x_3884_ = lean_box(0);
lean_inc(v___x_3883_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set_tag(v___x_3772_, 1);
lean_ctor_set(v___x_3772_, 1, v___x_3884_);
lean_ctor_set(v___x_3772_, 0, v___x_3883_);
v___x_3886_ = v___x_3772_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3888_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set_tag(v___x_3743_, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3883_);
v___x_3888_ = v___x_3743_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3883_);
v___x_3888_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3890_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set_tag(v___x_3767_, 1);
lean_ctor_set(v___x_3767_, 1, v___x_3884_);
lean_ctor_set(v___x_3767_, 0, v___x_3888_);
v___x_3890_ = v___x_3767_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3884_);
v___x_3890_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3892_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 1);
lean_ctor_set(v___x_3758_, 1, v___x_3890_);
lean_ctor_set(v___x_3758_, 0, v___x_3886_);
v___x_3892_ = v___x_3758_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
lean_inc_n(v___x_3877_, 2);
v___x_3893_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3877_);
lean_ctor_set(v___x_3893_, 1, v___x_3879_);
lean_ctor_set(v___x_3893_, 2, v___x_3882_);
lean_ctor_set(v___x_3893_, 3, v___x_3892_);
v___x_3894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3895_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3754_ == 0)
{
lean_ctor_set_tag(v___x_3753_, 2);
lean_ctor_set(v___x_3753_, 1, v___x_3896_);
lean_ctor_set(v___x_3753_, 0, v___x_3877_);
v___x_3898_ = v___x_3753_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3899_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3900_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3875_);
lean_inc(v_quotContext_3874_);
v___x_3901_ = l_Lean_addMacroScope(v_quotContext_3874_, v___x_3900_, v_currMacroScope_3875_);
lean_inc_n(v___x_3877_, 2);
v___x_3902_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3877_);
lean_ctor_set(v___x_3902_, 1, v___x_3899_);
lean_ctor_set(v___x_3902_, 2, v___x_3901_);
lean_ctor_set(v___x_3902_, 3, v___x_3884_);
v___x_3903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 2);
lean_ctor_set(v___x_3749_, 1, v___x_3903_);
lean_ctor_set(v___x_3749_, 0, v___x_3877_);
v___x_3905_ = v___x_3749_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3906_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3877_, 22);
v___x_3908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3877_);
lean_ctor_set(v___x_3908_, 1, v___x_3906_);
v___x_3909_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3910_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3875_, 5);
lean_inc_n(v_quotContext_3874_, 5);
v___x_3912_ = l_Lean_addMacroScope(v_quotContext_3874_, v___x_3911_, v_currMacroScope_3875_);
v___x_3913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3877_);
lean_ctor_set(v___x_3913_, 1, v___x_3910_);
lean_ctor_set(v___x_3913_, 2, v___x_3912_);
lean_ctor_set(v___x_3913_, 3, v___x_3884_);
v___x_3914_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3915_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3916_ = l_Lean_addMacroScope(v_quotContext_3874_, v___x_3915_, v_currMacroScope_3875_);
v___x_3917_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3877_);
lean_ctor_set(v___x_3917_, 1, v___x_3914_);
lean_ctor_set(v___x_3917_, 2, v___x_3916_);
lean_ctor_set(v___x_3917_, 3, v___x_3884_);
lean_inc_ref(v___x_3917_);
v___x_3918_ = l_Lean_Syntax_node2(v___x_3877_, v___x_3894_, v___x_3913_, v___x_3917_);
v___x_3919_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3920_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3877_);
lean_ctor_set(v___x_3920_, 1, v___x_3894_);
lean_ctor_set(v___x_3920_, 2, v___x_3919_);
v___x_3921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3877_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
lean_inc_ref(v___x_3922_);
lean_inc_ref(v___x_3920_);
v___x_3923_ = l_Lean_Syntax_node4(v___x_3877_, v___x_3909_, v___x_3918_, v___x_3920_, v___x_3922_, v_snd_3765_);
lean_inc_ref(v___x_3908_);
v___x_3924_ = l_Lean_Syntax_node2(v___x_3877_, v___x_3907_, v___x_3908_, v___x_3923_);
v___x_3925_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3877_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
lean_inc_ref_n(v___x_3926_, 2);
lean_inc_ref_n(v___x_3905_, 2);
lean_inc_ref_n(v___x_3898_, 2);
v___x_3927_ = l_Lean_Syntax_node5(v___x_3877_, v___x_3895_, v___x_3898_, v___x_3902_, v___x_3905_, v___x_3924_, v___x_3926_);
v___x_3928_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3930_ = l_Lean_addMacroScope(v_quotContext_3874_, v___x_3929_, v_currMacroScope_3875_);
v___x_3931_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3877_);
lean_ctor_set(v___x_3931_, 1, v___x_3928_);
lean_ctor_set(v___x_3931_, 2, v___x_3930_);
lean_ctor_set(v___x_3931_, 3, v___x_3884_);
v___x_3932_ = l_String_toRawSubstring_x27(v___x_3716_);
v___x_3933_ = l_Lean_addMacroScope(v_quotContext_3874_, v___x_3704_, v_currMacroScope_3875_);
v___x_3934_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3877_);
lean_ctor_set(v___x_3934_, 1, v___x_3932_);
lean_ctor_set(v___x_3934_, 2, v___x_3933_);
lean_ctor_set(v___x_3934_, 3, v___x_3884_);
v___x_3935_ = l_Lean_Syntax_node2(v___x_3877_, v___x_3894_, v___x_3934_, v___x_3917_);
v___x_3936_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3938_ = l_Lean_addMacroScope(v_quotContext_3874_, v___x_3937_, v_currMacroScope_3875_);
v___x_3939_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3877_);
lean_ctor_set(v___x_3939_, 1, v___x_3936_);
lean_ctor_set(v___x_3939_, 2, v___x_3938_);
lean_ctor_set(v___x_3939_, 3, v___x_3884_);
v___x_3940_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3944_ = l_Lean_addMacroScope(v_quotContext_3874_, v___x_3943_, v_currMacroScope_3875_);
v___x_3945_ = l_Lean_Name_mkStr4(v___x_3714_, v___x_3715_, v___x_3941_, v___x_3942_);
v___x_3946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
lean_ctor_set(v___x_3946_, 1, v___x_3884_);
v___x_3947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
lean_ctor_set(v___x_3947_, 1, v___x_3884_);
v___x_3948_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3877_);
lean_ctor_set(v___x_3948_, 1, v___x_3940_);
lean_ctor_set(v___x_3948_, 2, v___x_3944_);
lean_ctor_set(v___x_3948_, 3, v___x_3947_);
v___x_3949_ = l_Lean_Syntax_node5(v___x_3877_, v___x_3895_, v___x_3898_, v___x_3939_, v___x_3905_, v___x_3948_, v___x_3926_);
v___x_3950_ = l_Lean_Syntax_node1(v___x_3877_, v___x_3894_, v___x_3949_);
v___x_3951_ = l_Lean_Syntax_node2(v___x_3877_, v___x_3878_, v_fst_3764_, v___x_3950_);
v___x_3952_ = l_Lean_Syntax_node4(v___x_3877_, v___x_3909_, v___x_3935_, v___x_3920_, v___x_3922_, v___x_3951_);
v___x_3953_ = l_Lean_Syntax_node2(v___x_3877_, v___x_3907_, v___x_3908_, v___x_3952_);
v___x_3954_ = l_Lean_Syntax_node5(v___x_3877_, v___x_3895_, v___x_3898_, v___x_3931_, v___x_3905_, v___x_3953_, v___x_3926_);
v___x_3955_ = l_Lean_Syntax_node2(v___x_3877_, v___x_3894_, v___x_3927_, v___x_3954_);
v___x_3956_ = l_Lean_Syntax_node2(v___x_3877_, v___x_3878_, v___x_3893_, v___x_3955_);
v_a_3727_ = v___x_3956_;
goto v___jp_3726_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_del_object(v___x_3743_);
v_e_3963_ = lean_ctor_get(v_default_3770_, 0);
lean_inc_ref(v_e_3963_);
lean_dec_ref_known(v_default_3770_, 1);
v___x_3964_ = lean_box(1);
v___x_3965_ = l_Lean_PrettyPrinter_delab(v_e_3963_, v___x_3964_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_4051_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_4051_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_4051_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v_ref_3970_; lean_object* v_quotContext_3971_; lean_object* v_currMacroScope_3972_; uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3983_; 
v_ref_3970_ = lean_ctor_get(v___y_3723_, 5);
lean_inc(v_ref_3970_);
v_quotContext_3971_ = lean_ctor_get(v___y_3723_, 10);
lean_inc_n(v_quotContext_3971_, 2);
v_currMacroScope_3972_ = lean_ctor_get(v___y_3723_, 11);
lean_inc_n(v_currMacroScope_3972_, 2);
lean_dec_ref(v___y_3723_);
v___x_3973_ = 0;
v___x_3974_ = l_Lean_SourceInfo_fromRef(v_ref_3970_, v___x_3973_);
lean_dec(v_ref_3970_);
v___x_3975_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3976_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3977_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3713_);
v___x_3978_ = l_Lean_Name_mkStr2(v___x_3713_, v___x_3977_);
v___x_3979_ = l_Lean_addMacroScope(v_quotContext_3971_, v___x_3978_, v_currMacroScope_3972_);
v___x_3980_ = l_Lean_Name_mkStr4(v___x_3714_, v___x_3715_, v___x_3713_, v___x_3977_);
v___x_3981_ = lean_box(0);
lean_inc(v___x_3980_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set_tag(v___x_3772_, 1);
lean_ctor_set(v___x_3772_, 1, v___x_3981_);
lean_ctor_set(v___x_3772_, 0, v___x_3980_);
v___x_3983_ = v___x_3772_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_3980_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_4050_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3985_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3980_);
v___x_3985_ = v___x_3968_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_3980_);
v___x_3985_ = v_reuseFailAlloc_4049_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3987_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set_tag(v___x_3767_, 1);
lean_ctor_set(v___x_3767_, 1, v___x_3981_);
lean_ctor_set(v___x_3767_, 0, v___x_3985_);
v___x_3987_ = v___x_3767_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v___x_3981_);
v___x_3987_ = v_reuseFailAlloc_4048_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3989_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 1);
lean_ctor_set(v___x_3758_, 1, v___x_3987_);
lean_ctor_set(v___x_3758_, 0, v___x_3983_);
v___x_3989_ = v___x_3758_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_3983_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_4047_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3995_; 
lean_inc_n(v___x_3974_, 2);
v___x_3990_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3974_);
lean_ctor_set(v___x_3990_, 1, v___x_3976_);
lean_ctor_set(v___x_3990_, 2, v___x_3979_);
lean_ctor_set(v___x_3990_, 3, v___x_3989_);
v___x_3991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3992_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3993_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3754_ == 0)
{
lean_ctor_set_tag(v___x_3753_, 2);
lean_ctor_set(v___x_3753_, 1, v___x_3993_);
lean_ctor_set(v___x_3753_, 0, v___x_3974_);
v___x_3995_ = v___x_3753_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_4046_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_3996_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3997_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3972_);
lean_inc(v_quotContext_3971_);
v___x_3998_ = l_Lean_addMacroScope(v_quotContext_3971_, v___x_3997_, v_currMacroScope_3972_);
lean_inc_n(v___x_3974_, 2);
v___x_3999_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3974_);
lean_ctor_set(v___x_3999_, 1, v___x_3996_);
lean_ctor_set(v___x_3999_, 2, v___x_3998_);
lean_ctor_set(v___x_3999_, 3, v___x_3981_);
v___x_4000_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 2);
lean_ctor_set(v___x_3749_, 1, v___x_4000_);
lean_ctor_set(v___x_3749_, 0, v___x_3974_);
v___x_4002_ = v___x_3749_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4003_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4004_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3974_, 21);
v___x_4005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_3974_);
lean_ctor_set(v___x_4005_, 1, v___x_4003_);
v___x_4006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4007_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4008_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3972_, 4);
lean_inc_n(v_quotContext_3971_, 4);
v___x_4009_ = l_Lean_addMacroScope(v_quotContext_3971_, v___x_4008_, v_currMacroScope_3972_);
v___x_4010_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4010_, 0, v___x_3974_);
lean_ctor_set(v___x_4010_, 1, v___x_4007_);
lean_ctor_set(v___x_4010_, 2, v___x_4009_);
lean_ctor_set(v___x_4010_, 3, v___x_3981_);
v___x_4011_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4012_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4013_ = l_Lean_addMacroScope(v_quotContext_3971_, v___x_4012_, v_currMacroScope_3972_);
v___x_4014_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4014_, 0, v___x_3974_);
lean_ctor_set(v___x_4014_, 1, v___x_4011_);
lean_ctor_set(v___x_4014_, 2, v___x_4013_);
lean_ctor_set(v___x_4014_, 3, v___x_3981_);
lean_inc_ref(v___x_4014_);
v___x_4015_ = l_Lean_Syntax_node2(v___x_3974_, v___x_3991_, v___x_4010_, v___x_4014_);
v___x_4016_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4017_, 0, v___x_3974_);
lean_ctor_set(v___x_4017_, 1, v___x_3991_);
lean_ctor_set(v___x_4017_, 2, v___x_4016_);
v___x_4018_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_3974_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
lean_inc_ref(v___x_4019_);
lean_inc_ref(v___x_4017_);
v___x_4020_ = l_Lean_Syntax_node4(v___x_3974_, v___x_4006_, v___x_4015_, v___x_4017_, v___x_4019_, v_snd_3765_);
lean_inc_ref(v___x_4005_);
v___x_4021_ = l_Lean_Syntax_node2(v___x_3974_, v___x_4004_, v___x_4005_, v___x_4020_);
v___x_4022_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4023_, 0, v___x_3974_);
lean_ctor_set(v___x_4023_, 1, v___x_4022_);
lean_inc_ref_n(v___x_4023_, 2);
lean_inc_ref_n(v___x_4002_, 2);
lean_inc_ref_n(v___x_3995_, 2);
v___x_4024_ = l_Lean_Syntax_node5(v___x_3974_, v___x_3992_, v___x_3995_, v___x_3999_, v___x_4002_, v___x_4021_, v___x_4023_);
v___x_4025_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4026_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4027_ = l_Lean_addMacroScope(v_quotContext_3971_, v___x_4026_, v_currMacroScope_3972_);
v___x_4028_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4028_, 0, v___x_3974_);
lean_ctor_set(v___x_4028_, 1, v___x_4025_);
lean_ctor_set(v___x_4028_, 2, v___x_4027_);
lean_ctor_set(v___x_4028_, 3, v___x_3981_);
v___x_4029_ = l_String_toRawSubstring_x27(v___x_3716_);
v___x_4030_ = l_Lean_addMacroScope(v_quotContext_3971_, v___x_3704_, v_currMacroScope_3972_);
v___x_4031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4031_, 0, v___x_3974_);
lean_ctor_set(v___x_4031_, 1, v___x_4029_);
lean_ctor_set(v___x_4031_, 2, v___x_4030_);
lean_ctor_set(v___x_4031_, 3, v___x_3981_);
v___x_4032_ = l_Lean_Syntax_node2(v___x_3974_, v___x_3991_, v___x_4031_, v___x_4014_);
v___x_4033_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_4034_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_4035_ = l_Lean_addMacroScope(v_quotContext_3971_, v___x_4034_, v_currMacroScope_3972_);
v___x_4036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4036_, 0, v___x_3974_);
lean_ctor_set(v___x_4036_, 1, v___x_4033_);
lean_ctor_set(v___x_4036_, 2, v___x_4035_);
lean_ctor_set(v___x_4036_, 3, v___x_3981_);
v___x_4037_ = l_Lean_Syntax_node5(v___x_3974_, v___x_3992_, v___x_3995_, v___x_4036_, v___x_4002_, v_a_3966_, v___x_4023_);
v___x_4038_ = l_Lean_Syntax_node1(v___x_3974_, v___x_3991_, v___x_4037_);
v___x_4039_ = l_Lean_Syntax_node2(v___x_3974_, v___x_3975_, v_fst_3764_, v___x_4038_);
v___x_4040_ = l_Lean_Syntax_node4(v___x_3974_, v___x_4006_, v___x_4032_, v___x_4017_, v___x_4019_, v___x_4039_);
v___x_4041_ = l_Lean_Syntax_node2(v___x_3974_, v___x_4004_, v___x_4005_, v___x_4040_);
v___x_4042_ = l_Lean_Syntax_node5(v___x_3974_, v___x_3992_, v___x_3995_, v___x_4028_, v___x_4002_, v___x_4041_, v___x_4023_);
v___x_4043_ = l_Lean_Syntax_node2(v___x_3974_, v___x_3991_, v___x_4024_, v___x_4042_);
v___x_4044_ = l_Lean_Syntax_node2(v___x_3974_, v___x_3975_, v___x_3990_, v___x_4043_);
v_a_3727_ = v___x_4044_;
goto v___jp_3726_;
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
lean_del_object(v___x_3772_);
lean_del_object(v___x_3767_);
lean_dec(v_snd_3765_);
lean_dec(v_fst_3764_);
lean_del_object(v___x_3758_);
lean_del_object(v___x_3753_);
lean_del_object(v___x_3749_);
lean_dec_ref(v___y_3723_);
lean_dec_ref(v___x_3716_);
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
lean_dec_ref(v___x_3713_);
lean_dec(v___x_3704_);
v___y_3731_ = v___x_3965_;
goto v___jp_3730_;
}
}
default: 
{
lean_object* v_ref_4052_; lean_object* v_quotContext_4053_; lean_object* v_currMacroScope_4054_; uint8_t v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
lean_dec(v_default_3770_);
v_ref_4052_ = lean_ctor_get(v___y_3723_, 5);
lean_inc(v_ref_4052_);
v_quotContext_4053_ = lean_ctor_get(v___y_3723_, 10);
lean_inc_n(v_quotContext_4053_, 2);
v_currMacroScope_4054_ = lean_ctor_get(v___y_3723_, 11);
lean_inc_n(v_currMacroScope_4054_, 2);
lean_dec_ref(v___y_3723_);
v___x_4055_ = 0;
v___x_4056_ = l_Lean_SourceInfo_fromRef(v_ref_4052_, v___x_4055_);
lean_dec(v_ref_4052_);
v___x_4057_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4058_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4059_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3713_);
v___x_4060_ = l_Lean_Name_mkStr2(v___x_3713_, v___x_4059_);
v___x_4061_ = l_Lean_addMacroScope(v_quotContext_4053_, v___x_4060_, v_currMacroScope_4054_);
v___x_4062_ = l_Lean_Name_mkStr4(v___x_3714_, v___x_3715_, v___x_3713_, v___x_4059_);
v___x_4063_ = lean_box(0);
lean_inc(v___x_4062_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set_tag(v___x_3772_, 1);
lean_ctor_set(v___x_3772_, 1, v___x_4063_);
lean_ctor_set(v___x_3772_, 0, v___x_4062_);
v___x_4065_ = v___x_3772_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4067_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set_tag(v___x_3743_, 0);
lean_ctor_set(v___x_3743_, 0, v___x_4062_);
v___x_4067_ = v___x_3743_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4062_);
v___x_4067_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4069_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set_tag(v___x_3767_, 1);
lean_ctor_set(v___x_3767_, 1, v___x_4063_);
lean_ctor_set(v___x_3767_, 0, v___x_4067_);
v___x_4069_ = v___x_3767_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v___x_4063_);
v___x_4069_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4071_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 1);
lean_ctor_set(v___x_3758_, 1, v___x_4069_);
lean_ctor_set(v___x_3758_, 0, v___x_4065_);
v___x_4071_ = v___x_3758_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4122_, 1, v___x_4069_);
v___x_4071_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4077_; 
lean_inc_n(v___x_4056_, 2);
v___x_4072_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4056_);
lean_ctor_set(v___x_4072_, 1, v___x_4058_);
lean_ctor_set(v___x_4072_, 2, v___x_4061_);
lean_ctor_set(v___x_4072_, 3, v___x_4071_);
v___x_4073_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4074_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4075_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3754_ == 0)
{
lean_ctor_set_tag(v___x_3753_, 2);
lean_ctor_set(v___x_3753_, 1, v___x_4075_);
lean_ctor_set(v___x_3753_, 0, v___x_4056_);
v___x_4077_ = v___x_3753_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4084_; 
v___x_4078_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4079_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_4054_);
lean_inc(v_quotContext_4053_);
v___x_4080_ = l_Lean_addMacroScope(v_quotContext_4053_, v___x_4079_, v_currMacroScope_4054_);
lean_inc_n(v___x_4056_, 2);
v___x_4081_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4056_);
lean_ctor_set(v___x_4081_, 1, v___x_4078_);
lean_ctor_set(v___x_4081_, 2, v___x_4080_);
lean_ctor_set(v___x_4081_, 3, v___x_4063_);
v___x_4082_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 2);
lean_ctor_set(v___x_3749_, 1, v___x_4082_);
lean_ctor_set(v___x_3749_, 0, v___x_4056_);
v___x_4084_ = v___x_3749_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4085_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4086_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_4056_, 17);
v___x_4087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4056_);
lean_ctor_set(v___x_4087_, 1, v___x_4085_);
v___x_4088_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4089_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4090_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_4054_, 3);
lean_inc_n(v_quotContext_4053_, 3);
v___x_4091_ = l_Lean_addMacroScope(v_quotContext_4053_, v___x_4090_, v_currMacroScope_4054_);
v___x_4092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4056_);
lean_ctor_set(v___x_4092_, 1, v___x_4089_);
lean_ctor_set(v___x_4092_, 2, v___x_4091_);
lean_ctor_set(v___x_4092_, 3, v___x_4063_);
v___x_4093_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4094_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4095_ = l_Lean_addMacroScope(v_quotContext_4053_, v___x_4094_, v_currMacroScope_4054_);
v___x_4096_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4056_);
lean_ctor_set(v___x_4096_, 1, v___x_4093_);
lean_ctor_set(v___x_4096_, 2, v___x_4095_);
lean_ctor_set(v___x_4096_, 3, v___x_4063_);
lean_inc_ref(v___x_4096_);
v___x_4097_ = l_Lean_Syntax_node2(v___x_4056_, v___x_4073_, v___x_4092_, v___x_4096_);
v___x_4098_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4056_);
lean_ctor_set(v___x_4099_, 1, v___x_4073_);
lean_ctor_set(v___x_4099_, 2, v___x_4098_);
v___x_4100_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4056_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
lean_inc_ref(v___x_4101_);
lean_inc_ref(v___x_4099_);
v___x_4102_ = l_Lean_Syntax_node4(v___x_4056_, v___x_4088_, v___x_4097_, v___x_4099_, v___x_4101_, v_snd_3765_);
lean_inc_ref(v___x_4087_);
v___x_4103_ = l_Lean_Syntax_node2(v___x_4056_, v___x_4086_, v___x_4087_, v___x_4102_);
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4056_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
lean_inc_ref(v___x_4105_);
lean_inc_ref(v___x_4084_);
lean_inc_ref(v___x_4077_);
v___x_4106_ = l_Lean_Syntax_node5(v___x_4056_, v___x_4074_, v___x_4077_, v___x_4081_, v___x_4084_, v___x_4103_, v___x_4105_);
v___x_4107_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4108_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4109_ = l_Lean_addMacroScope(v_quotContext_4053_, v___x_4108_, v_currMacroScope_4054_);
v___x_4110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4056_);
lean_ctor_set(v___x_4110_, 1, v___x_4107_);
lean_ctor_set(v___x_4110_, 2, v___x_4109_);
lean_ctor_set(v___x_4110_, 3, v___x_4063_);
v___x_4111_ = l_String_toRawSubstring_x27(v___x_3716_);
v___x_4112_ = l_Lean_addMacroScope(v_quotContext_4053_, v___x_3704_, v_currMacroScope_4054_);
v___x_4113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4056_);
lean_ctor_set(v___x_4113_, 1, v___x_4111_);
lean_ctor_set(v___x_4113_, 2, v___x_4112_);
lean_ctor_set(v___x_4113_, 3, v___x_4063_);
v___x_4114_ = l_Lean_Syntax_node2(v___x_4056_, v___x_4073_, v___x_4113_, v___x_4096_);
v___x_4115_ = l_Lean_Syntax_node4(v___x_4056_, v___x_4088_, v___x_4114_, v___x_4099_, v___x_4101_, v_fst_3764_);
v___x_4116_ = l_Lean_Syntax_node2(v___x_4056_, v___x_4086_, v___x_4087_, v___x_4115_);
v___x_4117_ = l_Lean_Syntax_node5(v___x_4056_, v___x_4074_, v___x_4077_, v___x_4110_, v___x_4084_, v___x_4116_, v___x_4105_);
v___x_4118_ = l_Lean_Syntax_node2(v___x_4056_, v___x_4073_, v___x_4106_, v___x_4117_);
v___x_4119_ = l_Lean_Syntax_node2(v___x_4056_, v___x_4057_, v___x_4072_, v___x_4118_);
v_a_3727_ = v___x_4119_;
goto v___jp_3726_;
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
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_del_object(v___x_3758_);
lean_dec(v_snd_3756_);
lean_del_object(v___x_3753_);
lean_del_object(v___x_3749_);
lean_del_object(v___x_3743_);
lean_dec_ref(v___y_3723_);
lean_dec_ref(v___x_3716_);
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
lean_dec_ref(v___x_3713_);
lean_dec(v___x_3712_);
lean_dec(v___x_3704_);
v_a_4128_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_3762_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_3762_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
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
lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v_a_3734_);
lean_dec(v___x_3712_);
lean_dec(v___x_3711_);
lean_dec_ref(v___x_3705_);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_val_3737_);
if (v_isSharedCheck_4214_ == 0)
{
lean_object* v_unused_4215_; lean_object* v_unused_4216_; 
v_unused_4215_ = lean_ctor_get(v_val_3737_, 1);
lean_dec(v_unused_4215_);
v_unused_4216_ = lean_ctor_get(v_val_3737_, 0);
lean_dec(v_unused_4216_);
v___x_4142_ = v_val_3737_;
v_isShared_4143_ = v_isSharedCheck_4214_;
goto v_resetjp_4141_;
}
else
{
lean_dec(v_val_3737_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4214_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v_ref_4144_; lean_object* v_quotContext_4145_; lean_object* v_currMacroScope_4146_; uint8_t v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4157_; 
v_ref_4144_ = lean_ctor_get(v___y_3723_, 5);
lean_inc(v_ref_4144_);
v_quotContext_4145_ = lean_ctor_get(v___y_3723_, 10);
lean_inc_n(v_quotContext_4145_, 2);
v_currMacroScope_4146_ = lean_ctor_get(v___y_3723_, 11);
lean_inc_n(v_currMacroScope_4146_, 2);
lean_dec_ref(v___y_3723_);
v___x_4147_ = 0;
v___x_4148_ = l_Lean_SourceInfo_fromRef(v_ref_4144_, v___x_4147_);
lean_dec(v_ref_4144_);
v___x_4149_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4150_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4151_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3713_);
v___x_4152_ = l_Lean_Name_mkStr2(v___x_3713_, v___x_4151_);
v___x_4153_ = l_Lean_addMacroScope(v_quotContext_4145_, v___x_4152_, v_currMacroScope_4146_);
v___x_4154_ = l_Lean_Name_mkStr4(v___x_3714_, v___x_3715_, v___x_3713_, v___x_4151_);
v___x_4155_ = lean_box(0);
lean_inc(v___x_4154_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set_tag(v___x_4142_, 1);
lean_ctor_set(v___x_4142_, 1, v___x_4155_);
lean_ctor_set(v___x_4142_, 0, v___x_4154_);
v___x_4157_ = v___x_4142_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4154_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4159_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set_tag(v___x_3739_, 0);
lean_ctor_set(v___x_3739_, 0, v___x_4154_);
v___x_4159_ = v___x_3739_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4154_);
v___x_4159_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
lean_ctor_set(v___x_4160_, 1, v___x_4155_);
v___x_4161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4157_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
lean_inc_n(v___x_4148_, 23);
v___x_4162_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4148_);
lean_ctor_set(v___x_4162_, 1, v___x_4150_);
lean_ctor_set(v___x_4162_, 2, v___x_4153_);
lean_ctor_set(v___x_4162_, 3, v___x_4161_);
v___x_4163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4165_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_4166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4148_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4168_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_4146_, 4);
lean_inc_n(v_quotContext_4145_, 4);
v___x_4169_ = l_Lean_addMacroScope(v_quotContext_4145_, v___x_4168_, v_currMacroScope_4146_);
v___x_4170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4148_);
lean_ctor_set(v___x_4170_, 1, v___x_4167_);
lean_ctor_set(v___x_4170_, 2, v___x_4169_);
lean_ctor_set(v___x_4170_, 3, v___x_4155_);
v___x_4171_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_4172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4148_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
v___x_4175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4148_);
lean_ctor_set(v___x_4175_, 1, v___x_4173_);
v___x_4176_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4177_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4178_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_4179_ = l_Lean_addMacroScope(v_quotContext_4145_, v___x_4178_, v_currMacroScope_4146_);
v___x_4180_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4148_);
lean_ctor_set(v___x_4180_, 1, v___x_4177_);
lean_ctor_set(v___x_4180_, 2, v___x_4179_);
lean_ctor_set(v___x_4180_, 3, v___x_4155_);
v___x_4181_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4182_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4183_ = l_Lean_addMacroScope(v_quotContext_4145_, v___x_4182_, v_currMacroScope_4146_);
v___x_4184_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4148_);
lean_ctor_set(v___x_4184_, 1, v___x_4181_);
lean_ctor_set(v___x_4184_, 2, v___x_4183_);
lean_ctor_set(v___x_4184_, 3, v___x_4155_);
lean_inc_ref(v___x_4184_);
v___x_4185_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4163_, v___x_4180_, v___x_4184_);
v___x_4186_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4148_);
lean_ctor_set(v___x_4187_, 1, v___x_4163_);
lean_ctor_set(v___x_4187_, 2, v___x_4186_);
v___x_4188_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4148_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4191_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4148_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = l_Lean_Syntax_node1(v___x_4148_, v___x_4190_, v___x_4192_);
lean_inc(v___x_4193_);
lean_inc_ref(v___x_4189_);
lean_inc_ref(v___x_4187_);
v___x_4194_ = l_Lean_Syntax_node4(v___x_4148_, v___x_4176_, v___x_4185_, v___x_4187_, v___x_4189_, v___x_4193_);
lean_inc_ref(v___x_4175_);
v___x_4195_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4174_, v___x_4175_, v___x_4194_);
v___x_4196_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4148_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
lean_inc_ref(v___x_4197_);
lean_inc_ref(v___x_4172_);
lean_inc_ref(v___x_4166_);
v___x_4198_ = l_Lean_Syntax_node5(v___x_4148_, v___x_4164_, v___x_4166_, v___x_4170_, v___x_4172_, v___x_4195_, v___x_4197_);
v___x_4199_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4200_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4201_ = l_Lean_addMacroScope(v_quotContext_4145_, v___x_4200_, v_currMacroScope_4146_);
v___x_4202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4148_);
lean_ctor_set(v___x_4202_, 1, v___x_4199_);
lean_ctor_set(v___x_4202_, 2, v___x_4201_);
lean_ctor_set(v___x_4202_, 3, v___x_4155_);
v___x_4203_ = l_String_toRawSubstring_x27(v___x_3716_);
v___x_4204_ = l_Lean_addMacroScope(v_quotContext_4145_, v___x_3704_, v_currMacroScope_4146_);
v___x_4205_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4148_);
lean_ctor_set(v___x_4205_, 1, v___x_4203_);
lean_ctor_set(v___x_4205_, 2, v___x_4204_);
lean_ctor_set(v___x_4205_, 3, v___x_4155_);
v___x_4206_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4163_, v___x_4205_, v___x_4184_);
v___x_4207_ = l_Lean_Syntax_node4(v___x_4148_, v___x_4176_, v___x_4206_, v___x_4187_, v___x_4189_, v___x_4193_);
v___x_4208_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4174_, v___x_4175_, v___x_4207_);
v___x_4209_ = l_Lean_Syntax_node5(v___x_4148_, v___x_4164_, v___x_4166_, v___x_4202_, v___x_4172_, v___x_4208_, v___x_4197_);
v___x_4210_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4163_, v___x_4198_, v___x_4209_);
v___x_4211_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4149_, v___x_4162_, v___x_4210_);
v_a_3727_ = v___x_4211_;
goto v___jp_3726_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3736_);
lean_dec_ref(v___x_3713_);
if (lean_obj_tag(v_a_3734_) == 1)
{
lean_object* v_val_4218_; lean_object* v_snd_4219_; lean_object* v_fst_4220_; lean_object* v_snd_4221_; lean_object* v___x_4222_; lean_object* v___f_4223_; lean_object* v___x_4224_; 
v_val_4218_ = lean_ctor_get(v_a_3734_, 0);
lean_inc(v_val_4218_);
lean_dec_ref_known(v_a_3734_, 1);
v_snd_4219_ = lean_ctor_get(v_val_4218_, 1);
lean_inc(v_snd_4219_);
v_fst_4220_ = lean_ctor_get(v_val_4218_, 0);
lean_inc(v_fst_4220_);
lean_dec(v_val_4218_);
v_snd_4221_ = lean_ctor_get(v_snd_4219_, 1);
lean_inc(v_snd_4221_);
lean_dec(v_snd_4219_);
v___x_4222_ = lean_box(v___x_3710_);
lean_inc(v___x_3704_);
v___f_4223_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4223_, 0, v_fst_4220_);
lean_closure_set(v___f_4223_, 1, v_snd_4221_);
lean_closure_set(v___f_4223_, 2, v___x_3714_);
lean_closure_set(v___f_4223_, 3, v___x_3715_);
lean_closure_set(v___f_4223_, 4, v___x_3716_);
lean_closure_set(v___f_4223_, 5, v___x_3704_);
lean_closure_set(v___f_4223_, 6, v___x_3711_);
lean_closure_set(v___f_4223_, 7, v___x_4222_);
lean_closure_set(v___f_4223_, 8, v___x_3712_);
lean_closure_set(v___f_4223_, 9, v_arg_3709_);
v___x_4224_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3704_, v___x_3705_, v___f_4223_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec_ref(v___y_3723_);
v___y_3731_ = v___x_4224_;
goto v___jp_3730_;
}
else
{
lean_object* v_ref_4225_; lean_object* v_quotContext_4226_; lean_object* v_currMacroScope_4227_; uint8_t v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_dec(v_a_3734_);
lean_dec(v___x_3712_);
lean_dec(v___x_3711_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v___x_3705_);
v_ref_4225_ = lean_ctor_get(v___y_3723_, 5);
lean_inc(v_ref_4225_);
v_quotContext_4226_ = lean_ctor_get(v___y_3723_, 10);
lean_inc_n(v_quotContext_4226_, 2);
v_currMacroScope_4227_ = lean_ctor_get(v___y_3723_, 11);
lean_inc_n(v_currMacroScope_4227_, 2);
lean_dec_ref(v___y_3723_);
v___x_4228_ = 0;
v___x_4229_ = l_Lean_SourceInfo_fromRef(v_ref_4225_, v___x_4228_);
lean_dec(v_ref_4225_);
v___x_4230_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4231_ = l_Lean_Name_mkStr3(v___x_3714_, v___x_3715_, v___x_4230_);
v___x_4232_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4233_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4229_, 13);
v___x_4234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4229_);
lean_ctor_set(v___x_4234_, 1, v___x_4232_);
lean_ctor_set(v___x_4234_, 2, v___x_4233_);
v___x_4235_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_4236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4229_);
lean_ctor_set(v___x_4236_, 1, v___x_4235_);
v___x_4237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4229_);
lean_ctor_set(v___x_4240_, 1, v___x_4239_);
v___x_4241_ = l_String_toRawSubstring_x27(v___x_3716_);
v___x_4242_ = l_Lean_addMacroScope(v_quotContext_4226_, v___x_3704_, v_currMacroScope_4227_);
v___x_4243_ = lean_box(0);
v___x_4244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4229_);
lean_ctor_set(v___x_4244_, 1, v___x_4241_);
lean_ctor_set(v___x_4244_, 2, v___x_4242_);
lean_ctor_set(v___x_4244_, 3, v___x_4243_);
v___x_4245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4229_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4248_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4249_ = l_Lean_addMacroScope(v_quotContext_4226_, v___x_4248_, v_currMacroScope_4227_);
v___x_4250_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4229_);
lean_ctor_set(v___x_4250_, 1, v___x_4247_);
lean_ctor_set(v___x_4250_, 2, v___x_4249_);
lean_ctor_set(v___x_4250_, 3, v___x_4243_);
v___x_4251_ = l_Lean_Syntax_node3(v___x_4229_, v___x_4237_, v___x_4244_, v___x_4246_, v___x_4250_);
v___x_4252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4229_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = l_Lean_Syntax_node3(v___x_4229_, v___x_4238_, v___x_4240_, v___x_4251_, v___x_4253_);
v___x_4255_ = l_Lean_Syntax_node1(v___x_4229_, v___x_4237_, v___x_4254_);
v___x_4256_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4229_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4259_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4229_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Lean_Syntax_node1(v___x_4229_, v___x_4258_, v___x_4260_);
v___x_4262_ = l_Lean_Syntax_node5(v___x_4229_, v___x_4231_, v___x_4234_, v___x_4236_, v___x_4255_, v___x_4257_, v___x_4261_);
v_a_3727_ = v___x_4262_;
goto v___jp_3726_;
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec(v_a_3734_);
lean_dec_ref(v___y_3723_);
lean_dec_ref(v___x_3716_);
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
lean_dec_ref(v___x_3713_);
lean_dec(v___x_3712_);
lean_dec(v___x_3711_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v___x_3705_);
lean_dec(v___x_3704_);
v_a_4263_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_3735_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_3735_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref(v___y_3723_);
lean_dec_ref(v___x_3716_);
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
lean_dec_ref(v___x_3713_);
lean_dec(v___x_3712_);
lean_dec(v___x_3711_);
lean_dec_ref(v_arg_3709_);
lean_dec(v_inv_3708_);
lean_dec_ref(v___x_3705_);
lean_dec(v___x_3704_);
v_a_4271_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_3733_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_3733_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
v___jp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3727_);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
return v___x_3729_;
}
v___jp_3730_:
{
if (lean_obj_tag(v___y_3731_) == 0)
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___y_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___y_3731_, 1);
v_a_3727_ = v_a_3732_;
goto v___jp_3726_;
}
else
{
return v___y_3731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4279_ = _args[0];
lean_object* v___x_4280_ = _args[1];
lean_object* v___f_4281_ = _args[2];
lean_object* v_a_4282_ = _args[3];
lean_object* v_inv_4283_ = _args[4];
lean_object* v_arg_4284_ = _args[5];
lean_object* v___x_4285_ = _args[6];
lean_object* v___x_4286_ = _args[7];
lean_object* v___x_4287_ = _args[8];
lean_object* v___x_4288_ = _args[9];
lean_object* v___x_4289_ = _args[10];
lean_object* v___x_4290_ = _args[11];
lean_object* v___x_4291_ = _args[12];
lean_object* v___y_4292_ = _args[13];
lean_object* v___y_4293_ = _args[14];
lean_object* v___y_4294_ = _args[15];
lean_object* v___y_4295_ = _args[16];
lean_object* v___y_4296_ = _args[17];
lean_object* v___y_4297_ = _args[18];
lean_object* v___y_4298_ = _args[19];
lean_object* v___y_4299_ = _args[20];
lean_object* v___y_4300_ = _args[21];
_start:
{
uint8_t v___x_93975__boxed_4301_; lean_object* v_res_4302_; 
v___x_93975__boxed_4301_ = lean_unbox(v___x_4285_);
v_res_4302_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4279_, v___x_4280_, v___f_4281_, v_a_4282_, v_inv_4283_, v_arg_4284_, v___x_93975__boxed_4301_, v___x_4286_, v___x_4287_, v___x_4288_, v___x_4289_, v___x_4290_, v___x_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
lean_dec(v___y_4299_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec_ref(v_a_4282_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v___x_4309_; lean_object* v_env_4310_; lean_object* v___x_4311_; lean_object* v_mctx_4312_; lean_object* v_lctx_4313_; lean_object* v_options_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4309_ = lean_st_ref_get(v___y_4307_);
v_env_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc_ref(v_env_4310_);
lean_dec(v___x_4309_);
v___x_4311_ = lean_st_ref_get(v___y_4305_);
v_mctx_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc_ref(v_mctx_4312_);
lean_dec(v___x_4311_);
v_lctx_4313_ = lean_ctor_get(v___y_4304_, 2);
v_options_4314_ = lean_ctor_get(v___y_4306_, 2);
lean_inc_ref(v_options_4314_);
lean_inc_ref(v_lctx_4313_);
v___x_4315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4315_, 0, v_env_4310_);
lean_ctor_set(v___x_4315_, 1, v_mctx_4312_);
lean_ctor_set(v___x_4315_, 2, v_lctx_4313_);
lean_ctor_set(v___x_4315_, 3, v_options_4314_);
v___x_4316_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
lean_ctor_set(v___x_4316_, 1, v_msgData_4303_);
v___x_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_ref_4331_; lean_object* v___x_4332_; lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4341_; 
v_ref_4331_ = lean_ctor_get(v___y_4328_, 5);
v___x_4332_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4341_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4341_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; lean_object* v___x_4339_; 
lean_inc(v_ref_4331_);
v___x_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4337_, 0, v_ref_4331_);
lean_ctor_set(v___x_4337_, 1, v_a_4333_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set_tag(v___x_4335_, 1);
lean_ctor_set(v___x_4335_, 0, v___x_4337_);
v___x_4339_ = v___x_4335_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4355_, size_t v_i_4356_, size_t v_stop_4357_, lean_object* v_b_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v_a_4369_; lean_object* v_a_4374_; uint8_t v___x_4376_; 
v___x_4376_ = lean_usize_dec_eq(v_i_4356_, v_stop_4357_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4360_, v___y_4362_, v___y_4364_, v___y_4366_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; lean_object* v___y_4381_; uint8_t v___y_4382_; lean_object* v___y_4397_; lean_object* v_a_4398_; lean_object* v___x_4401_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4379_ = lean_array_uget_borrowed(v_as_4355_, v_i_4356_);
lean_inc(v___x_4379_);
v___x_4401_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4379_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v_ref_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v_ref_4403_ = lean_ctor_get(v___y_4365_, 5);
v___x_4404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
v___x_4406_ = l_Lean_SourceInfo_fromRef(v_ref_4403_, v___x_4376_);
lean_inc(v___x_4406_);
v___x_4407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
lean_ctor_set(v___x_4407_, 1, v___x_4404_);
v___x_4408_ = l_Lean_Syntax_node1(v___x_4406_, v___x_4405_, v___x_4407_);
v___x_4409_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4408_, v_a_4402_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
lean_dec(v_a_4378_);
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = lean_array_mk(v_a_4410_);
v_a_4374_ = v___x_4411_;
goto v___jp_4373_;
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
v_a_4412_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4409_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4409_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
lean_inc(v_a_4412_);
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
v___y_4397_ = v___x_4417_;
v_a_4398_ = v_a_4412_;
goto v___jp_4396_;
}
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
v_a_4420_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4401_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4401_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
lean_inc(v_a_4420_);
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
v___y_4397_ = v___x_4425_;
v_a_4398_ = v_a_4420_;
goto v___jp_4396_;
}
}
}
v___jp_4380_:
{
if (v___y_4382_ == 0)
{
lean_object* v___x_4383_; 
lean_dec_ref(v___y_4381_);
v___x_4383_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4378_, v___y_4382_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_dec_ref_known(v___x_4383_, 1);
v___x_4384_ = lean_unsigned_to_nat(1u);
v___x_4385_ = lean_mk_empty_array_with_capacity(v___x_4384_);
lean_inc(v___x_4379_);
v___x_4386_ = lean_array_push(v___x_4385_, v___x_4379_);
v_a_4374_ = v___x_4386_;
goto v___jp_4373_;
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
lean_dec_ref(v_b_4358_);
v_a_4387_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4383_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4383_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
else
{
lean_dec(v_a_4378_);
lean_dec_ref(v_b_4358_);
if (lean_obj_tag(v___y_4381_) == 0)
{
lean_object* v_a_4395_; 
v_a_4395_ = lean_ctor_get(v___y_4381_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___y_4381_, 1);
v_a_4369_ = v_a_4395_;
goto v___jp_4368_;
}
else
{
return v___y_4381_;
}
}
}
v___jp_4396_:
{
uint8_t v___x_4399_; 
v___x_4399_ = l_Lean_Exception_isInterrupt(v_a_4398_);
if (v___x_4399_ == 0)
{
uint8_t v___x_4400_; 
v___x_4400_ = l_Lean_Exception_isRuntime(v_a_4398_);
v___y_4381_ = v___y_4397_;
v___y_4382_ = v___x_4400_;
goto v___jp_4380_;
}
else
{
lean_dec_ref(v_a_4398_);
v___y_4381_ = v___y_4397_;
v___y_4382_ = v___x_4399_;
goto v___jp_4380_;
}
}
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec_ref(v_b_4358_);
v_a_4428_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4377_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4377_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v___x_4436_; 
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v_b_4358_);
return v___x_4436_;
}
v___jp_4368_:
{
size_t v___x_4370_; size_t v___x_4371_; 
v___x_4370_ = ((size_t)1ULL);
v___x_4371_ = lean_usize_add(v_i_4356_, v___x_4370_);
v_i_4356_ = v___x_4371_;
v_b_4358_ = v_a_4369_;
goto _start;
}
v___jp_4373_:
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Array_append___redArg(v_b_4358_, v_a_4374_);
lean_dec_ref(v_a_4374_);
v_a_4369_ = v___x_4375_;
goto v___jp_4368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4437_, lean_object* v_i_4438_, lean_object* v_stop_4439_, lean_object* v_b_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
size_t v_i_boxed_4450_; size_t v_stop_boxed_4451_; lean_object* v_res_4452_; 
v_i_boxed_4450_ = lean_unbox_usize(v_i_4438_);
lean_dec(v_i_4438_);
v_stop_boxed_4451_ = lean_unbox_usize(v_stop_4439_);
lean_dec(v_stop_4439_);
v_res_4452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4437_, v_i_boxed_4450_, v_stop_boxed_4451_, v_b_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec_ref(v_as_4437_);
return v_res_4452_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4454_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4455_ = l_Lean_stringToMessageData(v___x_4454_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4471_, lean_object* v_inv_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v___x_4482_; 
lean_inc(v_inv_4472_);
v___x_4482_ = l_Lean_MVarId_getType(v_inv_4472_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4484_; lean_object* v_a_4485_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
lean_dec_ref_known(v___x_4482_, 1);
v___x_4484_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4483_, v_a_4478_);
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc_n(v_a_4485_, 2);
lean_dec_ref(v___x_4484_);
v___x_4499_ = l_Lean_Expr_cleanupAnnotations(v_a_4485_);
v___x_4500_ = l_Lean_Expr_isApp(v___x_4499_);
if (v___x_4500_ == 0)
{
lean_dec_ref(v___x_4499_);
lean_dec(v_inv_4472_);
v___y_4487_ = v_a_4473_;
v___y_4488_ = v_a_4474_;
v___y_4489_ = v_a_4475_;
v___y_4490_ = v_a_4476_;
v___y_4491_ = v_a_4477_;
v___y_4492_ = v_a_4478_;
v___y_4493_ = v_a_4479_;
v___y_4494_ = v_a_4480_;
goto v___jp_4486_;
}
else
{
lean_object* v___x_4501_; uint8_t v___x_4502_; 
v___x_4501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4499_);
v___x_4502_ = l_Lean_Expr_isApp(v___x_4501_);
if (v___x_4502_ == 0)
{
lean_dec_ref(v___x_4501_);
lean_dec(v_inv_4472_);
v___y_4487_ = v_a_4473_;
v___y_4488_ = v_a_4474_;
v___y_4489_ = v_a_4475_;
v___y_4490_ = v_a_4476_;
v___y_4491_ = v_a_4477_;
v___y_4492_ = v_a_4478_;
v___y_4493_ = v_a_4479_;
v___y_4494_ = v_a_4480_;
goto v___jp_4486_;
}
else
{
lean_object* v_arg_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; 
v_arg_4503_ = lean_ctor_get(v___x_4501_, 1);
lean_inc_ref(v_arg_4503_);
v___x_4504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4501_);
v___x_4505_ = l_Lean_Expr_isApp(v___x_4504_);
if (v___x_4505_ == 0)
{
lean_dec_ref(v___x_4504_);
lean_dec_ref(v_arg_4503_);
lean_dec(v_inv_4472_);
v___y_4487_ = v_a_4473_;
v___y_4488_ = v_a_4474_;
v___y_4489_ = v_a_4475_;
v___y_4490_ = v_a_4476_;
v___y_4491_ = v_a_4477_;
v___y_4492_ = v_a_4478_;
v___y_4493_ = v_a_4479_;
v___y_4494_ = v_a_4480_;
goto v___jp_4486_;
}
else
{
lean_object* v_arg_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v_arg_4506_ = lean_ctor_get(v___x_4504_, 1);
lean_inc_ref(v_arg_4506_);
v___x_4507_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4504_);
v___x_4508_ = l_Lean_Expr_isApp(v___x_4507_);
if (v___x_4508_ == 0)
{
lean_dec_ref(v___x_4507_);
lean_dec_ref(v_arg_4506_);
lean_dec_ref(v_arg_4503_);
lean_dec(v_inv_4472_);
v___y_4487_ = v_a_4473_;
v___y_4488_ = v_a_4474_;
v___y_4489_ = v_a_4475_;
v___y_4490_ = v_a_4476_;
v___y_4491_ = v_a_4477_;
v___y_4492_ = v_a_4478_;
v___y_4493_ = v_a_4479_;
v___y_4494_ = v_a_4480_;
goto v___jp_4486_;
}
else
{
lean_object* v_arg_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v_arg_4509_ = lean_ctor_get(v___x_4507_, 1);
lean_inc_ref(v_arg_4509_);
v___x_4510_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4507_);
v___x_4511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4513_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4514_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4515_ = l_Lean_Expr_isConstOf(v___x_4510_, v___x_4514_);
if (v___x_4515_ == 0)
{
lean_dec_ref(v___x_4510_);
lean_dec_ref(v_arg_4509_);
lean_dec_ref(v_arg_4506_);
lean_dec_ref(v_arg_4503_);
lean_dec(v_inv_4472_);
v___y_4487_ = v_a_4473_;
v___y_4488_ = v_a_4474_;
v___y_4489_ = v_a_4475_;
v___y_4490_ = v_a_4476_;
v___y_4491_ = v_a_4477_;
v___y_4492_ = v_a_4478_;
v___y_4493_ = v_a_4479_;
v___y_4494_ = v_a_4480_;
goto v___jp_4486_;
}
else
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v_a_4522_; lean_object* v___y_4534_; lean_object* v___x_4544_; lean_object* v___x_4545_; uint8_t v___x_4546_; 
lean_dec(v_a_4485_);
v___x_4516_ = lean_unsigned_to_nat(1u);
v___x_4517_ = l_Lean_Expr_constLevels_x21(v___x_4510_);
lean_dec_ref(v___x_4510_);
v___x_4518_ = lean_unsigned_to_nat(0u);
v___x_4519_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4517_);
v___x_4520_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4517_, v___x_4517_, v___x_4516_, v___x_4519_);
lean_dec(v___x_4517_);
v___x_4544_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4545_ = lean_array_get_size(v_vcs_4471_);
v___x_4546_ = lean_nat_dec_lt(v___x_4518_, v___x_4545_);
if (v___x_4546_ == 0)
{
v_a_4522_ = v___x_4544_;
goto v___jp_4521_;
}
else
{
uint8_t v___x_4547_; 
v___x_4547_ = lean_nat_dec_le(v___x_4545_, v___x_4545_);
if (v___x_4547_ == 0)
{
if (v___x_4546_ == 0)
{
v_a_4522_ = v___x_4544_;
goto v___jp_4521_;
}
else
{
size_t v___x_4548_; size_t v___x_4549_; lean_object* v___x_4550_; 
v___x_4548_ = ((size_t)0ULL);
v___x_4549_ = lean_usize_of_nat(v___x_4545_);
v___x_4550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4471_, v___x_4548_, v___x_4549_, v___x_4544_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
v___y_4534_ = v___x_4550_;
goto v___jp_4533_;
}
}
else
{
size_t v___x_4551_; size_t v___x_4552_; lean_object* v___x_4553_; 
v___x_4551_ = ((size_t)0ULL);
v___x_4552_ = lean_usize_of_nat(v___x_4545_);
v___x_4553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4471_, v___x_4551_, v___x_4552_, v___x_4544_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
v___y_4534_ = v___x_4553_;
goto v___jp_4533_;
}
}
v___jp_4521_:
{
lean_object* v___x_4523_; lean_object* v___f_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___f_4531_; lean_object* v___x_4532_; 
v___x_4523_ = lean_box(v___x_4515_);
lean_inc_ref(v_arg_4503_);
lean_inc_n(v_inv_4472_, 2);
lean_inc_ref(v_a_4522_);
v___f_4524_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4524_, 0, v_a_4522_);
lean_closure_set(v___f_4524_, 1, v_inv_4472_);
lean_closure_set(v___f_4524_, 2, v___x_4523_);
lean_closure_set(v___f_4524_, 3, v___x_4516_);
lean_closure_set(v___f_4524_, 4, v_arg_4503_);
v___x_4525_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4526_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4527_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4528_ = l_Lean_mkConst(v___x_4527_, v___x_4520_);
v___x_4529_ = l_Lean_mkAppB(v___x_4528_, v_arg_4509_, v_arg_4506_);
v___x_4530_ = lean_box(v___x_4515_);
v___f_4531_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4531_, 0, v___x_4526_);
lean_closure_set(v___f_4531_, 1, v___x_4529_);
lean_closure_set(v___f_4531_, 2, v___f_4524_);
lean_closure_set(v___f_4531_, 3, v_a_4522_);
lean_closure_set(v___f_4531_, 4, v_inv_4472_);
lean_closure_set(v___f_4531_, 5, v_arg_4503_);
lean_closure_set(v___f_4531_, 6, v___x_4530_);
lean_closure_set(v___f_4531_, 7, v___x_4516_);
lean_closure_set(v___f_4531_, 8, v___x_4518_);
lean_closure_set(v___f_4531_, 9, v___x_4513_);
lean_closure_set(v___f_4531_, 10, v___x_4511_);
lean_closure_set(v___f_4531_, 11, v___x_4512_);
lean_closure_set(v___f_4531_, 12, v___x_4525_);
v___x_4532_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4472_, v___f_4531_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
return v___x_4532_;
}
v___jp_4533_:
{
if (lean_obj_tag(v___y_4534_) == 0)
{
lean_object* v_a_4535_; 
v_a_4535_ = lean_ctor_get(v___y_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___y_4534_, 1);
v_a_4522_ = v_a_4535_;
goto v___jp_4521_;
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec(v___x_4520_);
lean_dec_ref(v_arg_4509_);
lean_dec_ref(v_arg_4506_);
lean_dec_ref(v_arg_4503_);
lean_dec(v_inv_4472_);
v_a_4536_ = lean_ctor_get(v___y_4534_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___y_4534_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___y_4534_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___y_4534_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
}
}
}
}
}
v___jp_4486_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4495_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4496_ = l_Lean_MessageData_ofExpr(v_a_4485_);
v___x_4497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4495_);
lean_ctor_set(v___x_4497_, 1, v___x_4496_);
v___x_4498_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4497_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v___x_4498_;
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec(v_inv_4472_);
v_a_4554_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4482_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4482_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4562_, lean_object* v_inv_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4562_, v_inv_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
lean_dec(v_a_4571_);
lean_dec_ref(v_a_4570_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec_ref(v_vcs_4562_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4574_, lean_object* v_msg_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v___x_4585_; 
v___x_4585_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4575_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4586_, lean_object* v_msg_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4586_, v_msg_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4598_, lean_object* v_name_4599_, uint8_t v_bi_4600_, lean_object* v_type_4601_, lean_object* v_k_4602_, uint8_t v_kind_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4599_, v_bi_4600_, v_type_4601_, v_k_4602_, v_kind_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4614_, lean_object* v_name_4615_, lean_object* v_bi_4616_, lean_object* v_type_4617_, lean_object* v_k_4618_, lean_object* v_kind_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
uint8_t v_bi_boxed_4629_; uint8_t v_kind_boxed_4630_; lean_object* v_res_4631_; 
v_bi_boxed_4629_ = lean_unbox(v_bi_4616_);
v_kind_boxed_4630_ = lean_unbox(v_kind_4619_);
v_res_4631_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4614_, v_name_4615_, v_bi_boxed_4629_, v_type_4617_, v_k_4618_, v_kind_boxed_4630_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4632_, lean_object* v_name_4633_, lean_object* v_type_4634_, lean_object* v_k_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4633_, v_type_4634_, v_k_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4646_, lean_object* v_name_4647_, lean_object* v_type_4648_, lean_object* v_k_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4646_, v_name_4647_, v_type_4648_, v_k_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4660_, size_t v_sz_4661_, size_t v_i_4662_, lean_object* v_b_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4660_, v_sz_4661_, v_i_4662_, v_b_4663_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4674_, lean_object* v_sz_4675_, lean_object* v_i_4676_, lean_object* v_b_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
size_t v_sz_boxed_4687_; size_t v_i_boxed_4688_; lean_object* v_res_4689_; 
v_sz_boxed_4687_ = lean_unbox_usize(v_sz_4675_);
lean_dec(v_sz_4675_);
v_i_boxed_4688_ = lean_unbox_usize(v_i_4676_);
lean_dec(v_i_4676_);
v_res_4689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4674_, v_sz_boxed_4687_, v_i_boxed_4688_, v_b_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec_ref(v_as_4674_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4690_, size_t v_sz_4691_, size_t v_i_4692_, lean_object* v_b_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4690_, v_sz_4691_, v_i_4692_, v_b_4693_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4704_, lean_object* v_sz_4705_, lean_object* v_i_4706_, lean_object* v_b_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
size_t v_sz_boxed_4717_; size_t v_i_boxed_4718_; lean_object* v_res_4719_; 
v_sz_boxed_4717_ = lean_unbox_usize(v_sz_4705_);
lean_dec(v_sz_4705_);
v_i_boxed_4718_ = lean_unbox_usize(v_i_4706_);
lean_dec(v_i_4706_);
v_res_4719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4704_, v_sz_boxed_4717_, v_i_boxed_4718_, v_b_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec_ref(v_as_4704_);
return v_res_4719_;
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
