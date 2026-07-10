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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__11;
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
lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_256_; 
v_snd_215_ = lean_ctor_get(v_a_214_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_a_214_, 0);
lean_dec(v_unused_257_);
v___x_217_ = v_a_214_;
v_isShared_218_ = v_isSharedCheck_256_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_dec(v_a_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_256_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_fst_219_; lean_object* v_snd_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_255_; 
v_fst_219_ = lean_ctor_get(v_snd_215_, 0);
v_snd_220_ = lean_ctor_get(v_snd_215_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_snd_215_);
if (v_isSharedCheck_255_ == 0)
{
v___x_222_ = v_snd_215_;
v_isShared_223_ = v_isSharedCheck_255_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_snd_220_);
lean_inc(v_fst_219_);
lean_dec(v_snd_215_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_255_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; uint8_t v___x_227_; 
v___x_224_ = lean_box(0);
lean_inc(v_inv_213_);
v___x_225_ = l_Lean_mkMVar(v_inv_213_);
v___x_226_ = lean_expr_eqv(v_fst_219_, v___x_225_);
lean_dec_ref(v___x_225_);
v___x_227_ = lean_bool_not(v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_229_; 
lean_dec(v_inv_213_);
if (v_isShared_223_ == 0)
{
v___x_229_ = v___x_222_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_fst_219_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_snd_220_);
v___x_229_ = v_reuseFailAlloc_233_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_229_);
lean_ctor_set(v___x_217_, 0, v___x_224_);
v___x_231_ = v___x_217_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; uint8_t v___x_237_; 
v___x_234_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_235_ = lean_unsigned_to_nat(4u);
v___x_236_ = l_Lean_Expr_isAppOfArity(v_fst_219_, v___x_234_, v___x_235_);
v___x_237_ = lean_bool_not(v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_snd_220_, v___x_238_);
lean_dec(v_snd_220_);
v___x_240_ = l_Lean_Expr_getRevArg_x21(v_fst_219_, v___x_238_);
lean_dec(v_fst_219_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_239_);
lean_ctor_set(v___x_222_, 0, v___x_240_);
v___x_242_ = v___x_222_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_239_);
v___x_242_ = v_reuseFailAlloc_247_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_242_);
lean_ctor_set(v___x_217_, 0, v___x_224_);
v___x_244_ = v___x_217_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
v_a_214_ = v___x_244_;
goto _start;
}
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_250_; 
lean_dec(v_inv_213_);
v___x_248_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__2));
if (v_isShared_223_ == 0)
{
v___x_250_ = v___x_222_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_fst_219_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_snd_220_);
v___x_250_ = v_reuseFailAlloc_254_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_250_);
lean_ctor_set(v___x_217_, 0, v___x_248_);
v___x_252_ = v___x_217_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(lean_object* v_assertion_270_, lean_object* v_inv_271_){
_start:
{
lean_object* v_assertion_272_; lean_object* v___x_273_; uint8_t v___x_274_; uint8_t v___x_275_; 
v_assertion_272_ = l_Lean_Expr_consumeMData(v_assertion_270_);
v___x_273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1));
v___x_274_ = l_Lean_Expr_isAppOf(v_assertion_272_, v___x_273_);
v___x_275_ = lean_bool_not(v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_head_281_; lean_object* v_conditionIdx_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_fst_287_; 
v___x_276_ = lean_unsigned_to_nat(2u);
v___x_277_ = l_Lean_Expr_getAppNumArgs(v_assertion_272_);
v___x_278_ = lean_nat_sub(v___x_277_, v___x_276_);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_sub(v___x_278_, v___x_279_);
lean_dec(v___x_278_);
v_head_281_ = l_Lean_Expr_getRevArg_x21(v_assertion_272_, v___x_280_);
v_conditionIdx_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_head_281_);
lean_ctor_set(v___x_284_, 1, v_conditionIdx_282_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(v_inv_271_, v___x_285_);
v_fst_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_fst_287_);
if (lean_obj_tag(v_fst_287_) == 0)
{
lean_object* v_snd_288_; lean_object* v_dummy_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_snd_288_ = lean_ctor_get(v___x_286_, 1);
lean_inc(v_snd_288_);
lean_dec_ref(v___x_286_);
v_dummy_289_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__0);
lean_inc(v___x_277_);
v___x_290_ = lean_mk_array(v___x_277_, v_dummy_289_);
v___x_291_ = lean_nat_sub(v___x_277_, v___x_279_);
lean_dec(v___x_277_);
v___x_292_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_assertion_272_, v___x_290_, v___x_291_);
v___x_293_ = lean_array_get_size(v___x_292_);
v___x_294_ = lean_unsigned_to_nat(4u);
v___x_295_ = lean_nat_dec_lt(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_296_ = l_Lean_instInhabitedExpr;
v___x_297_ = lean_unsigned_to_nat(3u);
v___x_298_ = lean_array_get(v___x_296_, v___x_292_, v___x_297_);
v___x_299_ = l_Lean_Expr_cleanupAnnotations(v___x_298_);
v___x_300_ = l_Lean_Expr_isApp(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_dec_ref(v___x_299_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_301_ = lean_box(2);
return v___x_301_;
}
else
{
lean_object* v_arg_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_arg_302_ = lean_ctor_get(v___x_299_, 1);
lean_inc_ref(v_arg_302_);
v___x_303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_299_);
v___x_304_ = l_Lean_Expr_isApp(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec_ref(v___x_303_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_305_ = lean_box(2);
return v___x_305_;
}
else
{
lean_object* v_arg_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_arg_306_ = lean_ctor_get(v___x_303_, 1);
lean_inc_ref(v_arg_306_);
v___x_307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_303_);
v___x_308_ = l_Lean_Expr_isApp(v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_309_ = lean_box(2);
return v___x_309_;
}
else
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_307_);
v___x_311_ = l_Lean_Expr_isApp(v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v___x_310_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_312_ = lean_box(2);
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = l_Lean_Expr_appFnCleanup___redArg(v___x_310_);
v___x_314_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_315_ = l_Lean_Expr_isConstOf(v___x_313_, v___x_314_);
lean_dec_ref(v___x_313_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_316_ = lean_box(2);
return v___x_316_;
}
else
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = l_Lean_Expr_cleanupAnnotations(v_arg_306_);
v___x_318_ = l_Lean_Expr_isApp(v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
lean_dec_ref(v___x_317_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_319_ = lean_box(2);
return v___x_319_;
}
else
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_317_);
v___x_321_ = l_Lean_Expr_isApp(v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_322_ = lean_box(2);
return v___x_322_;
}
else
{
lean_object* v_arg_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_arg_323_ = lean_ctor_get(v___x_320_, 1);
lean_inc_ref(v_arg_323_);
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_320_);
v___x_325_ = l_Lean_Expr_isApp(v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_326_ = lean_box(2);
return v___x_326_;
}
else
{
lean_object* v_arg_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_arg_327_ = lean_ctor_get(v___x_324_, 1);
lean_inc_ref(v_arg_327_);
v___x_328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_324_);
v___x_329_ = l_Lean_Expr_isApp(v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec_ref(v___x_328_);
lean_dec_ref(v_arg_327_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_330_ = lean_box(2);
return v___x_330_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_328_);
v___x_332_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v___x_331_);
lean_dec_ref(v_arg_327_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_333_ = lean_box(2);
return v___x_333_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4));
v___x_336_ = l_Lean_Expr_isConstOf(v___x_334_, v___x_335_);
lean_dec_ref(v___x_334_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v_arg_327_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_337_ = lean_box(2);
return v___x_337_;
}
else
{
lean_object* v_snd_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_354_; 
v_snd_338_ = lean_ctor_get(v_snd_288_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_snd_288_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v_snd_288_, 0);
lean_dec(v_unused_355_);
v___x_340_ = v_snd_288_;
v_isShared_341_ = v_isSharedCheck_354_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_snd_338_);
lean_dec(v_snd_288_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_354_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
lean_inc_ref(v_arg_302_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v___x_342_);
lean_ctor_set(v___x_340_, 0, v_arg_302_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_arg_302_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_353_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v_fst_346_; lean_object* v_snd_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_345_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(v___x_344_);
v_fst_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_fst_346_);
v_snd_347_ = lean_ctor_get(v___x_345_, 1);
lean_inc(v_snd_347_);
lean_dec_ref(v___x_345_);
v___x_348_ = l_Array_toSubarray___redArg(v___x_292_, v___x_294_, v___x_293_);
v___x_349_ = lean_array_push(v_snd_347_, v_fst_346_);
v___x_350_ = l_Subarray_copy___redArg(v___x_348_);
v___x_351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_351_, 0, v_snd_338_);
lean_ctor_set(v___x_351_, 1, v_arg_327_);
lean_ctor_set(v___x_351_, 2, v_arg_323_);
lean_ctor_set(v___x_351_, 3, v___x_349_);
lean_ctor_set(v___x_351_, 4, v_arg_302_);
lean_ctor_set(v___x_351_, 5, v___x_350_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
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
lean_object* v___x_356_; 
lean_dec_ref(v___x_292_);
lean_dec(v_snd_288_);
v___x_356_ = lean_box(1);
return v___x_356_;
}
}
else
{
lean_object* v_val_357_; 
lean_dec_ref(v___x_286_);
lean_dec(v___x_277_);
lean_dec_ref(v_assertion_272_);
v_val_357_ = lean_ctor_get(v_fst_287_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v_fst_287_, 1);
return v_val_357_;
}
}
else
{
lean_object* v___x_358_; 
lean_dec_ref(v_assertion_272_);
lean_dec(v_inv_271_);
v___x_358_ = lean_box(1);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___boxed(lean_object* v_assertion_359_, lean_object* v_inv_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_assertion_359_, v_inv_360_);
lean_dec_ref(v_assertion_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0(lean_object* v_inv_362_, lean_object* v_inst_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg(v_inv_362_, v_a_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1(lean_object* v_inst_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg(v_a_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(lean_object* v_mvarId_369_, lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_369_, v_x_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_376_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg___boxed(lean_object* v_mvarId_393_, lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_393_, v_x_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_object* v_00_u03b1_401_, lean_object* v_mvarId_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_402_, v_x_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___boxed(lean_object* v_00_u03b1_410_, lean_object* v_mvarId_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(v_00_u03b1_410_, v_mvarId_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(lean_object* v_e_419_, lean_object* v___y_420_){
_start:
{
uint8_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = l_Lean_Expr_hasMVar(v_e_419_);
v___x_423_ = lean_bool_not(v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v_mctx_425_; lean_object* v___x_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_429_; lean_object* v_cache_430_; lean_object* v_zetaDeltaFVarIds_431_; lean_object* v_postponed_432_; lean_object* v_diag_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_442_; 
v___x_424_ = lean_st_ref_get(v___y_420_);
v_mctx_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc_ref(v_mctx_425_);
lean_dec(v___x_424_);
v___x_426_ = l_Lean_instantiateMVarsCore(v_mctx_425_, v_e_419_);
v_fst_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v___x_426_);
v___x_429_ = lean_st_ref_take(v___y_420_);
v_cache_430_ = lean_ctor_get(v___x_429_, 1);
v_zetaDeltaFVarIds_431_ = lean_ctor_get(v___x_429_, 2);
v_postponed_432_ = lean_ctor_get(v___x_429_, 3);
v_diag_433_ = lean_ctor_get(v___x_429_, 4);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_429_, 0);
lean_dec(v_unused_443_);
v___x_435_ = v___x_429_;
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_diag_433_);
lean_inc(v_postponed_432_);
lean_inc(v_zetaDeltaFVarIds_431_);
lean_inc(v_cache_430_);
lean_dec(v___x_429_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_snd_428_);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_snd_428_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_cache_430_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_zetaDeltaFVarIds_431_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_postponed_432_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_diag_433_);
v___x_438_ = v_reuseFailAlloc_441_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_st_ref_set(v___y_420_, v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_fst_427_);
return v___x_440_;
}
}
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v_e_419_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg___boxed(lean_object* v_e_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_445_, v___y_446_);
lean_dec(v___y_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(lean_object* v_e_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_449_, v___y_451_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___boxed(lean_object* v_e_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(v_e_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object* v_inv_480_, lean_object* v_as_481_, size_t v_sz_482_, size_t v_i_483_, lean_object* v_b_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_a_491_; uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_lt(v_i_483_, v_sz_482_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec(v_inv_480_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v_b_484_);
return v___x_496_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_498_; 
lean_dec_ref(v_b_484_);
v_a_497_ = lean_array_uget_borrowed(v_as_481_, v_i_483_);
lean_inc(v_a_497_);
v___x_498_ = l_Lean_MVarId_getType(v_a_497_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_559_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_559_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_559_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_559_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; uint8_t v___y_505_; lean_object* v_a_511_; lean_object* v___x_547_; 
v___x_503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v___x_547_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_499_, v___y_486_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = l_Lean_Expr_consumeMData(v_a_548_);
lean_dec(v_a_548_);
v_a_511_ = v___x_549_;
goto v___jp_510_;
}
else
{
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_550_; 
v_a_550_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_547_, 1);
v_a_511_ = v_a_550_;
goto v___jp_510_;
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_del_object(v___x_501_);
lean_dec(v_inv_480_);
v_a_551_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_547_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_547_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
v___jp_504_:
{
if (v___y_505_ == 0)
{
lean_del_object(v___x_501_);
v_a_491_ = v___x_503_;
goto v___jp_490_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec(v_inv_480_);
v___x_506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_506_);
v___x_508_ = v___x_501_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_512_, 0, v_a_511_);
lean_inc(v_a_497_);
v___x_513_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_497_, v___x_512_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_538_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_538_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_538_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_538_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
if (lean_obj_tag(v_a_514_) == 1)
{
lean_object* v_val_518_; lean_object* v_snd_519_; lean_object* v_snd_520_; lean_object* v___x_521_; 
v_val_518_ = lean_ctor_get(v_a_514_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_a_514_, 1);
v_snd_519_ = lean_ctor_get(v_val_518_, 1);
lean_inc(v_snd_519_);
lean_dec(v_val_518_);
v_snd_520_ = lean_ctor_get(v_snd_519_, 1);
lean_inc(v_snd_520_);
lean_dec(v_snd_519_);
lean_inc(v_inv_480_);
v___x_521_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_520_, v_inv_480_);
lean_dec(v_snd_520_);
switch(lean_obj_tag(v___x_521_))
{
case 0:
{
lean_object* v_invariantUse_522_; lean_object* v_cursorSuffix_523_; lean_object* v_letMuts_524_; lean_object* v___x_525_; uint8_t v___x_526_; uint8_t v___x_527_; 
lean_del_object(v___x_516_);
v_invariantUse_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_invariantUse_522_);
lean_dec_ref_known(v___x_521_, 1);
v_cursorSuffix_523_ = lean_ctor_get(v_invariantUse_522_, 2);
lean_inc_ref(v_cursorSuffix_523_);
v_letMuts_524_ = lean_ctor_get(v_invariantUse_522_, 3);
lean_inc_ref(v_letMuts_524_);
lean_dec_ref(v_invariantUse_522_);
v___x_525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4));
v___x_526_ = l_Lean_Expr_isAppOf(v_cursorSuffix_523_, v___x_525_);
lean_dec_ref(v_cursorSuffix_523_);
v___x_527_ = lean_bool_not(v___x_526_);
if (v___x_527_ == 0)
{
lean_dec_ref(v_letMuts_524_);
v___y_505_ = v___x_527_;
goto v___jp_504_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; uint8_t v___x_533_; 
v___x_528_ = l_Lean_instInhabitedExpr;
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_array_get(v___x_528_, v_letMuts_524_, v___x_529_);
lean_dec_ref(v_letMuts_524_);
v___x_531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_532_ = l_Lean_Expr_isAppOf(v___x_530_, v___x_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_bool_not(v___x_532_);
v___y_505_ = v___x_533_;
goto v___jp_504_;
}
}
case 1:
{
lean_del_object(v___x_516_);
lean_del_object(v___x_501_);
v_a_491_ = v___x_503_;
goto v___jp_490_;
}
default: 
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_del_object(v___x_501_);
lean_dec(v_inv_480_);
v___x_534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_534_);
v___x_536_ = v___x_516_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_del_object(v___x_501_);
v_a_491_ = v___x_503_;
goto v___jp_490_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_501_);
lean_dec(v_inv_480_);
v_a_539_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_513_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_513_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_inv_480_);
v_a_560_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_498_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_498_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
v___jp_490_:
{
size_t v___x_492_; size_t v___x_493_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_483_, v___x_492_);
lean_inc_ref(v_a_491_);
v_i_483_ = v___x_493_;
v_b_484_ = v_a_491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object* v_inv_568_, lean_object* v_as_569_, lean_object* v_sz_570_, lean_object* v_i_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v_sz_boxed_578_ = lean_unbox_usize(v_sz_570_);
lean_dec(v_sz_570_);
v_i_boxed_579_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_568_, v_as_569_, v_sz_boxed_578_, v_i_boxed_579_, v_b_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_as_569_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object* v_vcs_585_, lean_object* v_inv_586_, lean_object* v_letMutsTy_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
uint8_t v___y_597_; lean_object* v___x_646_; uint8_t v___x_647_; uint8_t v___x_648_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1));
v___x_647_ = l_Lean_Expr_isAppOf(v_letMutsTy_587_, v___x_646_);
v___x_648_ = lean_bool_not(v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = l_Lean_Expr_getAppNumArgs(v_letMutsTy_587_);
v___x_650_ = lean_unsigned_to_nat(2u);
v___x_651_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
lean_dec(v___x_649_);
v___y_597_ = v___x_651_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___x_648_;
goto v___jp_596_;
}
v___jp_593_:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_598_ = l_Lean_Expr_getAppNumArgs(v_letMutsTy_587_);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_sub(v___x_598_, v___x_599_);
lean_dec(v___x_598_);
lean_inc(v___x_600_);
v___x_601_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_587_, v___x_600_);
v___x_602_ = l_Lean_Expr_cleanupAnnotations(v___x_601_);
v___x_603_ = l_Lean_Expr_isApp(v___x_602_);
if (v___x_603_ == 0)
{
lean_dec_ref(v___x_602_);
lean_dec(v___x_600_);
lean_dec(v_inv_586_);
goto v___jp_593_;
}
else
{
lean_object* v_arg_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_arg_604_ = lean_ctor_get(v___x_602_, 1);
lean_inc_ref(v_arg_604_);
v___x_605_ = l_Lean_Expr_appFnCleanup___redArg(v___x_602_);
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0));
v___x_607_ = l_Lean_Expr_isConstOf(v___x_605_, v___x_606_);
lean_dec_ref(v___x_605_);
if (v___x_607_ == 0)
{
lean_dec_ref(v_arg_604_);
lean_dec(v___x_600_);
lean_dec(v_inv_586_);
goto v___jp_593_;
}
else
{
lean_object* v___x_608_; size_t v_sz_609_; size_t v___x_610_; lean_object* v___x_611_; 
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v_sz_609_ = lean_array_size(v_vcs_585_);
v___x_610_ = ((size_t)0ULL);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_586_, v_vcs_585_, v_sz_609_, v___x_610_, v___x_608_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_635_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_635_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_635_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_635_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_fst_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_633_; 
v_fst_616_ = lean_ctor_get(v_a_612_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_612_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_a_612_, 1);
lean_dec(v_unused_634_);
v___x_618_ = v_a_612_;
v_isShared_619_ = v_isSharedCheck_633_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_fst_616_);
lean_dec(v_a_612_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_633_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
if (lean_obj_tag(v_fst_616_) == 0)
{
lean_object* v___x_620_; lean_object* v_00_u03c3_621_; lean_object* v___x_623_; 
v___x_620_ = lean_nat_sub(v___x_600_, v___x_599_);
lean_dec(v___x_600_);
v_00_u03c3_621_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_587_, v___x_620_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v_00_u03c3_621_);
lean_ctor_set(v___x_618_, 0, v_arg_604_);
v___x_623_ = v___x_618_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_arg_604_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_00_u03c3_621_);
v___x_623_ = v_reuseFailAlloc_628_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_624_);
v___x_626_ = v___x_614_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_val_629_; lean_object* v___x_631_; 
lean_del_object(v___x_618_);
lean_dec_ref(v_arg_604_);
lean_dec(v___x_600_);
v_val_629_ = lean_ctor_get(v_fst_616_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v_fst_616_, 1);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v_val_629_);
v___x_631_ = v___x_614_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_val_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_arg_604_);
lean_dec(v___x_600_);
v_a_636_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_611_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_611_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_inv_586_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object* v_vcs_652_, lean_object* v_inv_653_, lean_object* v_letMutsTy_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_vcs_652_, v_inv_653_, v_letMutsTy_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec_ref(v_letMutsTy_654_);
lean_dec_ref(v_vcs_652_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object* v_dontRevert_661_, lean_object* v_as_662_, size_t v_i_663_, size_t v_stop_664_, lean_object* v_b_665_){
_start:
{
lean_object* v___y_667_; uint8_t v___x_671_; 
v___x_671_ = lean_usize_dec_eq(v_i_663_, v_stop_664_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; uint8_t v___x_675_; 
v___x_672_ = lean_array_uget_borrowed(v_as_662_, v_i_663_);
lean_inc_ref(v_dontRevert_661_);
lean_inc(v___x_672_);
v___x_673_ = lean_apply_1(v_dontRevert_661_, v___x_672_);
v___x_674_ = lean_unbox(v___x_673_);
v___x_675_ = lean_bool_not(v___x_674_);
if (v___x_675_ == 0)
{
v___y_667_ = v_b_665_;
goto v___jp_666_;
}
else
{
lean_object* v___x_676_; 
lean_inc(v___x_672_);
v___x_676_ = lean_array_push(v_b_665_, v___x_672_);
v___y_667_ = v___x_676_;
goto v___jp_666_;
}
}
else
{
lean_dec_ref(v_dontRevert_661_);
return v_b_665_;
}
v___jp_666_:
{
size_t v___x_668_; size_t v___x_669_; 
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_add(v_i_663_, v___x_668_);
v_i_663_ = v___x_669_;
v_b_665_ = v___y_667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object* v_dontRevert_677_, lean_object* v_as_678_, lean_object* v_i_679_, lean_object* v_stop_680_, lean_object* v_b_681_){
_start:
{
size_t v_i_boxed_682_; size_t v_stop_boxed_683_; lean_object* v_res_684_; 
v_i_boxed_682_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_stop_boxed_683_ = lean_unbox_usize(v_stop_680_);
lean_dec(v_stop_680_);
v_res_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_677_, v_as_678_, v_i_boxed_682_, v_stop_boxed_683_, v_b_681_);
lean_dec_ref(v_as_678_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t v_sz_685_, size_t v_i_686_, lean_object* v_bs_687_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_lt(v_i_686_, v_sz_685_);
if (v___x_688_ == 0)
{
return v_bs_687_;
}
else
{
lean_object* v_v_689_; lean_object* v___x_690_; lean_object* v_bs_x27_691_; lean_object* v___x_692_; size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v_v_689_ = lean_array_uget(v_bs_687_, v_i_686_);
v___x_690_ = lean_unsigned_to_nat(0u);
v_bs_x27_691_ = lean_array_uset(v_bs_687_, v_i_686_, v___x_690_);
v___x_692_ = l_Lean_mkFVar(v_v_689_);
v___x_693_ = ((size_t)1ULL);
v___x_694_ = lean_usize_add(v_i_686_, v___x_693_);
v___x_695_ = lean_array_uset(v_bs_x27_691_, v_i_686_, v___x_692_);
v_i_686_ = v___x_694_;
v_bs_687_ = v___x_695_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object* v_sz_697_, lean_object* v_i_698_, lean_object* v_bs_699_){
_start:
{
size_t v_sz_boxed_700_; size_t v_i_boxed_701_; lean_object* v_res_702_; 
v_sz_boxed_700_ = lean_unbox_usize(v_sz_697_);
lean_dec(v_sz_697_);
v_i_boxed_701_ = lean_unbox_usize(v_i_698_);
lean_dec(v_i_698_);
v_res_702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_boxed_700_, v_i_boxed_701_, v_bs_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t v_sz_703_, size_t v_i_704_, lean_object* v_bs_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = lean_usize_dec_lt(v_i_704_, v_sz_703_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v_bs_705_);
return v___x_712_;
}
else
{
lean_object* v_v_713_; lean_object* v___x_714_; 
v_v_713_ = lean_array_uget_borrowed(v_bs_705_, v_i_704_);
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v_v_713_);
v___x_714_ = lean_infer_type(v_v_713_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v_bs_x27_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = lean_unsigned_to_nat(0u);
v_bs_x27_717_ = lean_array_uset(v_bs_705_, v_i_704_, v___x_716_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_add(v_i_704_, v___x_718_);
v___x_720_ = lean_array_uset(v_bs_x27_717_, v_i_704_, v_a_715_);
v_i_704_ = v___x_719_;
v_bs_705_ = v___x_720_;
goto _start;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v_bs_705_);
v_a_722_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_714_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_714_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object* v_sz_730_, lean_object* v_i_731_, lean_object* v_bs_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
size_t v_sz_boxed_738_; size_t v_i_boxed_739_; lean_object* v_res_740_; 
v_sz_boxed_738_ = lean_unbox_usize(v_sz_730_);
lean_dec(v_sz_730_);
v_i_boxed_739_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_boxed_738_, v_i_boxed_739_, v_bs_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_dontRevert_741_, lean_object* v_as_742_, size_t v_i_743_, size_t v_stop_744_, lean_object* v_b_745_){
_start:
{
lean_object* v___y_747_; uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_eq(v_i_743_, v_stop_744_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; uint8_t v___x_756_; 
v___x_752_ = lean_array_uget_borrowed(v_as_742_, v_i_743_);
v___x_753_ = l_Lean_Expr_fvarId_x21(v___x_752_);
lean_inc_ref(v_dontRevert_741_);
v___x_754_ = lean_apply_1(v_dontRevert_741_, v___x_753_);
v___x_755_ = lean_unbox(v___x_754_);
v___x_756_ = lean_bool_not(v___x_755_);
if (v___x_756_ == 0)
{
v___y_747_ = v_b_745_;
goto v___jp_746_;
}
else
{
lean_object* v___x_757_; 
lean_inc(v___x_752_);
v___x_757_ = lean_array_push(v_b_745_, v___x_752_);
v___y_747_ = v___x_757_;
goto v___jp_746_;
}
}
else
{
lean_dec_ref(v_dontRevert_741_);
return v_b_745_;
}
v___jp_746_:
{
size_t v___x_748_; size_t v___x_749_; 
v___x_748_ = ((size_t)1ULL);
v___x_749_ = lean_usize_add(v_i_743_, v___x_748_);
v_i_743_ = v___x_749_;
v_b_745_ = v___y_747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_dontRevert_758_, lean_object* v_as_759_, lean_object* v_i_760_, lean_object* v_stop_761_, lean_object* v_b_762_){
_start:
{
size_t v_i_boxed_763_; size_t v_stop_boxed_764_; lean_object* v_res_765_; 
v_i_boxed_763_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_stop_boxed_764_ = lean_unbox_usize(v_stop_761_);
lean_dec(v_stop_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_758_, v_as_759_, v_i_boxed_763_, v_stop_boxed_764_, v_b_762_);
lean_dec_ref(v_as_759_);
return v_res_765_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
uint8_t v___x_768_; 
v___x_768_ = 0;
return v___x_768_;
}
else
{
lean_object* v_key_769_; lean_object* v_tail_770_; uint8_t v___x_771_; 
v_key_769_ = lean_ctor_get(v_x_767_, 0);
v_tail_770_ = lean_ctor_get(v_x_767_, 2);
v___x_771_ = lean_expr_eqv(v_key_769_, v_a_766_);
if (v___x_771_ == 0)
{
v_x_767_ = v_tail_770_;
goto _start;
}
else
{
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_a_773_, lean_object* v_x_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_773_, v_x_774_);
lean_dec(v_x_774_);
lean_dec_ref(v_a_773_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
return v_x_777_;
}
else
{
lean_object* v_key_779_; lean_object* v_value_780_; lean_object* v_tail_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_804_; 
v_key_779_ = lean_ctor_get(v_x_778_, 0);
v_value_780_ = lean_ctor_get(v_x_778_, 1);
v_tail_781_ = lean_ctor_get(v_x_778_, 2);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_804_ == 0)
{
v___x_783_ = v_x_778_;
v_isShared_784_ = v_isSharedCheck_804_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_tail_781_);
lean_inc(v_value_780_);
lean_inc(v_key_779_);
lean_dec(v_x_778_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_804_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; uint64_t v_fold_789_; uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_785_ = lean_array_get_size(v_x_777_);
v___x_786_ = l_Lean_Expr_hash(v_key_779_);
v___x_787_ = 32ULL;
v___x_788_ = lean_uint64_shift_right(v___x_786_, v___x_787_);
v_fold_789_ = lean_uint64_xor(v___x_786_, v___x_788_);
v___x_790_ = 16ULL;
v___x_791_ = lean_uint64_shift_right(v_fold_789_, v___x_790_);
v___x_792_ = lean_uint64_xor(v_fold_789_, v___x_791_);
v___x_793_ = lean_uint64_to_usize(v___x_792_);
v___x_794_ = lean_usize_of_nat(v___x_785_);
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_sub(v___x_794_, v___x_795_);
v___x_797_ = lean_usize_land(v___x_793_, v___x_796_);
v___x_798_ = lean_array_uget_borrowed(v_x_777_, v___x_797_);
lean_inc(v___x_798_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 2, v___x_798_);
v___x_800_ = v___x_783_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_key_779_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_value_780_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v___x_798_);
v___x_800_ = v_reuseFailAlloc_803_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_array_uset(v_x_777_, v___x_797_, v___x_800_);
v_x_777_ = v___x_801_;
v_x_778_ = v_tail_781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_i_805_, lean_object* v_source_806_, lean_object* v_target_807_){
_start:
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = lean_array_get_size(v_source_806_);
v___x_809_ = lean_nat_dec_lt(v_i_805_, v___x_808_);
if (v___x_809_ == 0)
{
lean_dec_ref(v_source_806_);
lean_dec(v_i_805_);
return v_target_807_;
}
else
{
lean_object* v_es_810_; lean_object* v___x_811_; lean_object* v_source_812_; lean_object* v_target_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_es_810_ = lean_array_fget(v_source_806_, v_i_805_);
v___x_811_ = lean_box(0);
v_source_812_ = lean_array_fset(v_source_806_, v_i_805_, v___x_811_);
v_target_813_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_target_807_, v_es_810_);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v_i_805_, v___x_814_);
lean_dec(v_i_805_);
v_i_805_ = v___x_815_;
v_source_806_ = v_source_812_;
v_target_807_ = v_target_813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(lean_object* v_data_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_nbuckets_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_818_ = lean_array_get_size(v_data_817_);
v___x_819_ = lean_unsigned_to_nat(2u);
v_nbuckets_820_ = lean_nat_mul(v___x_818_, v___x_819_);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_box(0);
v___x_823_ = lean_mk_array(v_nbuckets_820_, v___x_822_);
v___x_824_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v___x_821_, v_data_817_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_825_, lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
lean_object* v_size_828_; lean_object* v_buckets_829_; lean_object* v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v___x_833_; uint64_t v_fold_834_; uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v_bkt_843_; uint8_t v___x_844_; 
v_size_828_ = lean_ctor_get(v_m_825_, 0);
v_buckets_829_ = lean_ctor_get(v_m_825_, 1);
v___x_830_ = lean_array_get_size(v_buckets_829_);
v___x_831_ = l_Lean_Expr_hash(v_a_826_);
v___x_832_ = 32ULL;
v___x_833_ = lean_uint64_shift_right(v___x_831_, v___x_832_);
v_fold_834_ = lean_uint64_xor(v___x_831_, v___x_833_);
v___x_835_ = 16ULL;
v___x_836_ = lean_uint64_shift_right(v_fold_834_, v___x_835_);
v___x_837_ = lean_uint64_xor(v_fold_834_, v___x_836_);
v___x_838_ = lean_uint64_to_usize(v___x_837_);
v___x_839_ = lean_usize_of_nat(v___x_830_);
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_sub(v___x_839_, v___x_840_);
v___x_842_ = lean_usize_land(v___x_838_, v___x_841_);
v_bkt_843_ = lean_array_uget_borrowed(v_buckets_829_, v___x_842_);
v___x_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_826_, v_bkt_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_865_; 
lean_inc_ref(v_buckets_829_);
lean_inc(v_size_828_);
v_isSharedCheck_865_ = !lean_is_exclusive(v_m_825_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_866_ = lean_ctor_get(v_m_825_, 1);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_m_825_, 0);
lean_dec(v_unused_867_);
v___x_846_ = v_m_825_;
v_isShared_847_ = v_isSharedCheck_865_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_m_825_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_865_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v_size_x27_849_; lean_object* v___x_850_; lean_object* v_buckets_x27_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_848_ = lean_unsigned_to_nat(1u);
v_size_x27_849_ = lean_nat_add(v_size_828_, v___x_848_);
lean_dec(v_size_828_);
lean_inc(v_bkt_843_);
v___x_850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_850_, 0, v_a_826_);
lean_ctor_set(v___x_850_, 1, v_b_827_);
lean_ctor_set(v___x_850_, 2, v_bkt_843_);
v_buckets_x27_851_ = lean_array_uset(v_buckets_829_, v___x_842_, v___x_850_);
v___x_852_ = lean_unsigned_to_nat(4u);
v___x_853_ = lean_nat_mul(v_size_x27_849_, v___x_852_);
v___x_854_ = lean_unsigned_to_nat(3u);
v___x_855_ = lean_nat_div(v___x_853_, v___x_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_array_get_size(v_buckets_x27_851_);
v___x_857_ = lean_nat_dec_le(v___x_855_, v___x_856_);
lean_dec(v___x_855_);
if (v___x_857_ == 0)
{
lean_object* v_val_858_; lean_object* v___x_860_; 
v_val_858_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_buckets_x27_851_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_val_858_);
lean_ctor_set(v___x_846_, 0, v_size_x27_849_);
v___x_860_ = v___x_846_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_size_x27_849_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_val_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
else
{
lean_object* v___x_863_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_buckets_x27_851_);
lean_ctor_set(v___x_846_, 0, v_size_x27_849_);
v___x_863_ = v___x_846_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_size_x27_849_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_buckets_x27_851_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_dec(v_b_827_);
lean_dec_ref(v_a_826_);
return v_m_825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_as_868_, size_t v_sz_869_, size_t v_i_870_, lean_object* v_b_871_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = lean_usize_dec_lt(v_i_870_, v_sz_869_);
if (v___x_872_ == 0)
{
return v_b_871_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v_r_875_; size_t v___x_876_; size_t v___x_877_; 
v_a_873_ = lean_array_uget_borrowed(v_as_868_, v_i_870_);
v___x_874_ = lean_box(0);
lean_inc(v_a_873_);
v_r_875_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_871_, v_a_873_, v___x_874_);
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_870_, v___x_876_);
v_i_870_ = v___x_877_;
v_b_871_ = v_r_875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_as_879_, lean_object* v_sz_880_, lean_object* v_i_881_, lean_object* v_b_882_){
_start:
{
size_t v_sz_boxed_883_; size_t v_i_boxed_884_; lean_object* v_res_885_; 
v_sz_boxed_883_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v_i_boxed_884_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_res_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_879_, v_sz_boxed_883_, v_i_boxed_884_, v_b_882_);
lean_dec_ref(v_as_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_886_, lean_object* v_l_887_){
_start:
{
size_t v_sz_888_; size_t v___x_889_; lean_object* v___x_890_; 
v_sz_888_ = lean_array_size(v_l_887_);
v___x_889_ = ((size_t)0ULL);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_l_887_, v_sz_888_, v___x_889_, v_m_886_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_891_, lean_object* v_l_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_891_, v_l_892_);
lean_dec_ref(v_l_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_894_, size_t v_i_895_, size_t v_stop_896_, lean_object* v_b_897_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = lean_usize_dec_eq(v_i_895_, v_stop_896_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; size_t v___x_901_; size_t v___x_902_; 
v___x_899_ = lean_array_uget_borrowed(v_as_894_, v_i_895_);
lean_inc(v___x_899_);
v___x_900_ = l_Lean_collectFVars(v_b_897_, v___x_899_);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_add(v_i_895_, v___x_901_);
v_i_895_ = v___x_902_;
v_b_897_ = v___x_900_;
goto _start;
}
else
{
return v_b_897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_904_, lean_object* v_i_905_, lean_object* v_stop_906_, lean_object* v_b_907_){
_start:
{
size_t v_i_boxed_908_; size_t v_stop_boxed_909_; lean_object* v_res_910_; 
v_i_boxed_908_ = lean_unbox_usize(v_i_905_);
lean_dec(v_i_905_);
v_stop_boxed_909_ = lean_unbox_usize(v_stop_906_);
lean_dec(v_stop_906_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_904_, v_i_boxed_908_, v_stop_boxed_909_, v_b_907_);
lean_dec_ref(v_as_904_);
return v_res_910_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(0);
v___x_914_ = lean_unsigned_to_nat(16u);
v___x_915_ = lean_mk_array(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object* v_dontRevert_919_, lean_object* v_a_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
uint8_t v___x_926_; uint8_t v___x_927_; lean_object* v___x_928_; 
v___x_926_ = 0;
v___x_927_ = 1;
lean_inc_ref(v_a_920_);
v___x_928_ = l_Lean_Meta_collectForwardDeps(v_a_920_, v___x_926_, v___x_927_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_1002_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_1002_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_1002_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___y_935_; size_t v___y_936_; lean_object* v___y_937_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___y_950_; size_t v___y_951_; lean_object* v_fvarIds_952_; lean_object* v___y_961_; size_t v___y_962_; lean_object* v___y_963_; lean_object* v___y_966_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_box(1);
v___x_948_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_993_ = lean_array_get_size(v_a_929_);
v___x_994_ = lean_nat_dec_lt(v___x_933_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v_a_929_);
v___y_966_ = v___x_948_;
goto v___jp_965_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = lean_nat_dec_le(v___x_993_, v___x_993_);
if (v___x_995_ == 0)
{
if (v___x_994_ == 0)
{
lean_dec(v_a_929_);
v___y_966_ = v___x_948_;
goto v___jp_965_;
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_993_);
lean_inc_ref(v_dontRevert_919_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_919_, v_a_929_, v___x_996_, v___x_997_, v___x_948_);
lean_dec(v_a_929_);
v___y_966_ = v___x_998_;
goto v___jp_965_;
}
}
else
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = lean_usize_of_nat(v___x_993_);
lean_inc_ref(v_dontRevert_919_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_919_, v_a_929_, v___x_999_, v___x_1000_, v___x_948_);
lean_dec(v_a_929_);
v___y_966_ = v___x_1001_;
goto v___jp_965_;
}
}
v___jp_934_:
{
size_t v_sz_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_sz_938_ = lean_array_size(v___y_937_);
lean_inc_ref(v___y_937_);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_938_, v___y_936_, v___y_937_);
v___x_940_ = l_Array_append___redArg(v___y_935_, v___x_939_);
lean_dec_ref(v___x_939_);
v___x_941_ = lean_array_get_size(v___y_937_);
lean_dec_ref(v___y_937_);
v___x_942_ = lean_nat_dec_eq(v___x_941_, v___x_933_);
if (v___x_942_ == 0)
{
lean_del_object(v___x_931_);
v_a_920_ = v___x_940_;
goto _start;
}
else
{
lean_object* v___x_945_; 
lean_dec_ref(v_dontRevert_919_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_940_);
v___x_945_ = v___x_931_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
v___jp_949_:
{
lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_953_ = lean_array_get_size(v_fvarIds_952_);
v___x_954_ = lean_nat_dec_lt(v___x_933_, v___x_953_);
if (v___x_954_ == 0)
{
lean_dec_ref(v_fvarIds_952_);
v___y_935_ = v___y_950_;
v___y_936_ = v___y_951_;
v___y_937_ = v___x_948_;
goto v___jp_934_;
}
else
{
uint8_t v___x_955_; 
v___x_955_ = lean_nat_dec_le(v___x_953_, v___x_953_);
if (v___x_955_ == 0)
{
if (v___x_954_ == 0)
{
lean_dec_ref(v_fvarIds_952_);
v___y_935_ = v___y_950_;
v___y_936_ = v___y_951_;
v___y_937_ = v___x_948_;
goto v___jp_934_;
}
else
{
size_t v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_usize_of_nat(v___x_953_);
lean_inc_ref(v_dontRevert_919_);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_919_, v_fvarIds_952_, v___y_951_, v___x_956_, v___x_948_);
lean_dec_ref(v_fvarIds_952_);
v___y_935_ = v___y_950_;
v___y_936_ = v___y_951_;
v___y_937_ = v___x_957_;
goto v___jp_934_;
}
}
else
{
size_t v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_usize_of_nat(v___x_953_);
lean_inc_ref(v_dontRevert_919_);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_919_, v_fvarIds_952_, v___y_951_, v___x_958_, v___x_948_);
lean_dec_ref(v_fvarIds_952_);
v___y_935_ = v___y_950_;
v___y_936_ = v___y_951_;
v___y_937_ = v___x_959_;
goto v___jp_934_;
}
}
}
v___jp_960_:
{
lean_object* v_fvarIds_964_; 
v_fvarIds_964_ = lean_ctor_get(v___y_963_, 2);
lean_inc_ref(v_fvarIds_964_);
lean_dec_ref(v___y_963_);
v___y_950_ = v___y_961_;
v___y_951_ = v___y_962_;
v_fvarIds_952_ = v_fvarIds_964_;
goto v___jp_949_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_array_get_size(v___y_966_);
v___x_968_ = lean_array_get_size(v_a_920_);
lean_dec_ref(v_a_920_);
v___x_969_ = lean_nat_dec_eq(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
size_t v_sz_970_; size_t v___x_971_; lean_object* v___x_972_; 
v_sz_970_ = lean_array_size(v___y_966_);
v___x_971_ = ((size_t)0ULL);
lean_inc_ref(v___y_966_);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_970_, v___x_971_, v___y_966_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v___x_974_ = lean_array_get_size(v_a_973_);
v___x_975_ = lean_nat_dec_lt(v___x_933_, v___x_974_);
if (v___x_975_ == 0)
{
lean_dec(v_a_973_);
v___y_950_ = v___y_966_;
v___y_951_ = v___x_971_;
v_fvarIds_952_ = v___x_948_;
goto v___jp_949_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_976_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_976_, v___y_966_);
v___x_978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_947_);
lean_ctor_set(v___x_978_, 2, v___x_948_);
v___x_979_ = lean_nat_dec_le(v___x_974_, v___x_974_);
if (v___x_979_ == 0)
{
if (v___x_975_ == 0)
{
lean_dec_ref_known(v___x_978_, 3);
lean_dec(v_a_973_);
v___y_950_ = v___y_966_;
v___y_951_ = v___x_971_;
v_fvarIds_952_ = v___x_948_;
goto v___jp_949_;
}
else
{
size_t v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_usize_of_nat(v___x_974_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_973_, v___x_971_, v___x_980_, v___x_978_);
lean_dec(v_a_973_);
v___y_961_ = v___y_966_;
v___y_962_ = v___x_971_;
v___y_963_ = v___x_981_;
goto v___jp_960_;
}
}
else
{
size_t v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_usize_of_nat(v___x_974_);
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_973_, v___x_971_, v___x_982_, v___x_978_);
lean_dec(v_a_973_);
v___y_961_ = v___y_966_;
v___y_962_ = v___x_971_;
v___y_963_ = v___x_983_;
goto v___jp_960_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v___y_966_);
lean_del_object(v___x_931_);
lean_dec_ref(v_dontRevert_919_);
v_a_984_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_972_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_972_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v___x_992_; 
lean_del_object(v___x_931_);
lean_dec_ref(v_dontRevert_919_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___y_966_);
return v___x_992_;
}
}
}
}
else
{
lean_dec_ref(v_a_920_);
lean_dec_ref(v_dontRevert_919_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object* v_dontRevert_1003_, lean_object* v_a_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1003_, v_a_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1010_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1011_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1012_ = lean_box(1);
v___x_1013_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_1014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1012_);
lean_ctor_set(v___x_1014_, 2, v___x_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_1015_, lean_object* v_dontRevert_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___y_1023_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_fvarIds_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1030_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_1031_ = l_Lean_collectFVars(v___x_1030_, v_e_1015_);
v_fvarIds_1032_ = lean_ctor_get(v___x_1031_, 2);
lean_inc_ref(v_fvarIds_1032_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = lean_array_get_size(v_fvarIds_1032_);
v___x_1034_ = lean_nat_dec_lt(v___x_1028_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v_fvarIds_1032_);
v___y_1023_ = v___x_1029_;
goto v___jp_1022_;
}
else
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_nat_dec_le(v___x_1033_, v___x_1033_);
if (v___x_1035_ == 0)
{
if (v___x_1034_ == 0)
{
lean_dec_ref(v_fvarIds_1032_);
v___y_1023_ = v___x_1029_;
goto v___jp_1022_;
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1033_);
lean_inc_ref(v_dontRevert_1016_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1016_, v_fvarIds_1032_, v___x_1036_, v___x_1037_, v___x_1029_);
lean_dec_ref(v_fvarIds_1032_);
v___y_1023_ = v___x_1038_;
goto v___jp_1022_;
}
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1033_);
lean_inc_ref(v_dontRevert_1016_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1016_, v_fvarIds_1032_, v___x_1039_, v___x_1040_, v___x_1029_);
lean_dec_ref(v_fvarIds_1032_);
v___y_1023_ = v___x_1041_;
goto v___jp_1022_;
}
}
v___jp_1022_:
{
size_t v_sz_1024_; size_t v___x_1025_; lean_object* v_xs_1026_; lean_object* v___x_1027_; 
v_sz_1024_ = lean_array_size(v___y_1023_);
v___x_1025_ = ((size_t)0ULL);
v_xs_1026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1024_, v___x_1025_, v___y_1023_);
v___x_1027_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1016_, v_xs_1026_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1042_, lean_object* v_dontRevert_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1042_, v_dontRevert_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_1050_, lean_object* v_inst_1051_, lean_object* v_a_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1050_, v_a_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_1059_, lean_object* v_inst_1060_, lean_object* v_a_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1059_, v_inst_1060_, v_a_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1068_, lean_object* v_m_1069_, lean_object* v_a_1070_, lean_object* v_b_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1069_, v_a_1070_, v_b_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1073_, lean_object* v_a_1074_, lean_object* v_x_1075_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_1074_, v_x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1077_, lean_object* v_a_1078_, lean_object* v_x_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1077_, v_a_1078_, v_x_1079_);
lean_dec(v_x_1079_);
lean_dec_ref(v_a_1078_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1082_, lean_object* v_data_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_data_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1085_, lean_object* v_i_1086_, lean_object* v_source_1087_, lean_object* v_target_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v_i_1086_, v_source_1087_, v_target_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1091_, v_x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v_i_1103_, lean_object* v_a_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_zero_1110_; uint8_t v_isZero_1111_; 
v_zero_1110_ = lean_unsigned_to_nat(0u);
v_isZero_1111_ = lean_nat_dec_eq(v_i_1103_, v_zero_1110_);
if (v_isZero_1111_ == 1)
{
lean_object* v___x_1112_; 
lean_dec(v_i_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v___x_1101_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_a_1104_);
return v___x_1112_;
}
else
{
lean_object* v_one_1113_; lean_object* v_n_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_one_1113_ = lean_unsigned_to_nat(1u);
v_n_1114_ = lean_nat_sub(v_i_1103_, v_one_1113_);
lean_dec(v_i_1103_);
v___x_1115_ = lean_array_fget_borrowed(v_a_1100_, v_n_1114_);
lean_inc_ref(v___x_1101_);
v___x_1116_ = l_Lean_LocalContext_getFVar_x21(v___x_1101_, v___x_1115_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_userName_1117_; lean_object* v_type_1118_; uint8_t v_bi_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_userName_1117_ = lean_ctor_get(v___x_1116_, 2);
lean_inc(v_userName_1117_);
v_type_1118_ = lean_ctor_get(v___x_1116_, 3);
lean_inc_ref(v_type_1118_);
v_bi_1119_ = lean_ctor_get_uint8(v___x_1116_, sizeof(void*)*4);
lean_dec_ref_known(v___x_1116_, 4);
v___x_1120_ = l_Lean_Expr_headBeta(v_type_1118_);
v___x_1121_ = lean_expr_abstract_range(v___x_1120_, v_n_1114_, v_a_1100_);
lean_dec_ref(v___x_1120_);
lean_inc_ref(v___x_1121_);
v___x_1122_ = l_Lean_Meta_getLevel(v___x_1121_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1125_ = lean_box(0);
lean_inc_n(v___x_1102_, 2);
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1102_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_a_1123_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_mkConst(v___x_1124_, v___x_1127_);
v___x_1129_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1102_);
lean_inc_ref(v___x_1121_);
v___x_1130_ = l_Lean_mkLambda(v_userName_1117_, v_bi_1119_, v___x_1121_, v_a_1104_);
v___x_1131_ = l_Lean_mkApp3(v___x_1128_, v___x_1121_, v___x_1129_, v___x_1130_);
v_i_1103_ = v_n_1114_;
v_a_1104_ = v___x_1131_;
goto _start;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v___x_1121_);
lean_dec(v_userName_1117_);
lean_dec(v_n_1114_);
lean_dec_ref(v_a_1104_);
lean_dec(v___x_1102_);
lean_dec_ref(v___x_1101_);
v_a_1133_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1122_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1122_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
uint8_t v_nondep_1141_; 
v_nondep_1141_ = lean_ctor_get_uint8(v___x_1116_, sizeof(void*)*5);
if (v_nondep_1141_ == 0)
{
lean_object* v_userName_1142_; lean_object* v_type_1143_; lean_object* v_value_1144_; uint8_t v___x_1145_; 
v_userName_1142_ = lean_ctor_get(v___x_1116_, 2);
lean_inc(v_userName_1142_);
v_type_1143_ = lean_ctor_get(v___x_1116_, 3);
lean_inc_ref(v_type_1143_);
v_value_1144_ = lean_ctor_get(v___x_1116_, 4);
lean_inc_ref(v_value_1144_);
lean_dec_ref_known(v___x_1116_, 5);
v___x_1145_ = lean_expr_has_loose_bvar(v_a_1104_, v_zero_1110_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec_ref(v_value_1144_);
lean_dec_ref(v_type_1143_);
lean_dec(v_userName_1142_);
v___x_1146_ = lean_expr_lower_loose_bvars(v_a_1104_, v_one_1113_, v_one_1113_);
lean_dec_ref(v_a_1104_);
v_i_1103_ = v_n_1114_;
v_a_1104_ = v___x_1146_;
goto _start;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = l_Lean_Expr_headBeta(v_type_1143_);
v___x_1149_ = lean_expr_abstract_range(v___x_1148_, v_n_1114_, v_a_1100_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = lean_expr_abstract_range(v_value_1144_, v_n_1114_, v_a_1100_);
lean_dec_ref(v_value_1144_);
v___x_1151_ = l_Lean_Expr_letE___override(v_userName_1142_, v___x_1149_, v___x_1150_, v_a_1104_, v_nondep_1141_);
v_i_1103_ = v_n_1114_;
v_a_1104_ = v___x_1151_;
goto _start;
}
}
else
{
lean_object* v_userName_1153_; lean_object* v_type_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_userName_1153_ = lean_ctor_get(v___x_1116_, 2);
lean_inc(v_userName_1153_);
v_type_1154_ = lean_ctor_get(v___x_1116_, 3);
lean_inc_ref(v_type_1154_);
lean_dec_ref_known(v___x_1116_, 5);
v___x_1155_ = l_Lean_Expr_headBeta(v_type_1154_);
v___x_1156_ = lean_expr_abstract_range(v___x_1155_, v_n_1114_, v_a_1100_);
lean_dec_ref(v___x_1155_);
lean_inc_ref(v___x_1156_);
v___x_1157_ = l_Lean_Meta_getLevel(v___x_1156_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1160_ = lean_box(0);
lean_inc_n(v___x_1102_, 2);
v___x_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1102_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_a_1158_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_mkConst(v___x_1159_, v___x_1162_);
v___x_1164_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1102_);
v___x_1165_ = 0;
lean_inc_ref(v___x_1156_);
v___x_1166_ = l_Lean_mkLambda(v_userName_1153_, v___x_1165_, v___x_1156_, v_a_1104_);
v___x_1167_ = l_Lean_mkApp3(v___x_1163_, v___x_1156_, v___x_1164_, v___x_1166_);
v_i_1103_ = v_n_1114_;
v_a_1104_ = v___x_1167_;
goto _start;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v___x_1156_);
lean_dec(v_userName_1153_);
lean_dec(v_n_1114_);
lean_dec_ref(v_a_1104_);
lean_dec(v___x_1102_);
lean_dec_ref(v___x_1101_);
v_a_1169_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1157_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1157_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1177_, lean_object* v___x_1178_, lean_object* v___x_1179_, lean_object* v_i_1180_, lean_object* v_a_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1177_, v___x_1178_, v___x_1179_, v_i_1180_, v_a_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec_ref(v_a_1177_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1192_, lean_object* v_dontRevert_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1199_; 
lean_inc_ref(v_e_1192_);
v___x_1199_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1192_, v_dontRevert_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v_lctx_1201_; lean_object* v___x_1202_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1199_, 1);
v_lctx_1201_ = lean_ctor_get(v_a_1194_, 2);
lean_inc(v_a_1197_);
lean_inc_ref(v_a_1196_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
lean_inc_ref(v_e_1192_);
v___x_1202_ = lean_infer_type(v_e_1192_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1225_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1225_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1225_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = l_Lean_Expr_cleanupAnnotations(v_a_1203_);
v___x_1208_ = l_Lean_Expr_isApp(v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v___x_1207_);
lean_dec(v_a_1200_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v_e_1192_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_e_1192_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1207_);
v___x_1213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1214_ = l_Lean_Expr_isConstOf(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v___x_1212_);
lean_dec(v_a_1200_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v_e_1192_);
v___x_1216_ = v___x_1205_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_e_1192_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_del_object(v___x_1205_);
v___x_1218_ = lean_box(0);
v___x_1219_ = l_Lean_Expr_constLevels_x21(v___x_1212_);
lean_dec_ref(v___x_1212_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = l_List_get_x21Internal___redArg(v___x_1218_, v___x_1219_, v___x_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_array_get_size(v_a_1200_);
v___x_1223_ = lean_expr_abstract(v_e_1192_, v_a_1200_);
lean_dec_ref(v_e_1192_);
lean_inc_ref(v_lctx_1201_);
v___x_1224_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1200_, v_lctx_1201_, v___x_1221_, v___x_1222_, v___x_1223_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1200_);
return v___x_1224_;
}
}
}
}
else
{
lean_dec(v_a_1200_);
lean_dec_ref(v_e_1192_);
return v___x_1202_;
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_e_1192_);
v_a_1226_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1199_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1199_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1234_, lean_object* v_dontRevert_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1234_, v_dontRevert_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1242_, lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v_n_1245_, lean_object* v_i_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1242_, v___x_1243_, v___x_1244_, v_i_1246_, v_a_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1255_, lean_object* v___x_1256_, lean_object* v___x_1257_, lean_object* v_n_1258_, lean_object* v_i_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1255_, v___x_1256_, v___x_1257_, v_n_1258_, v_i_1259_, v_a_1260_, v_a_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v_n_1258_);
lean_dec_ref(v_a_1255_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1274_, lean_object* v_lhs_1275_, lean_object* v_rhs_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1278_ = lean_box(0);
lean_inc(v_lvl_1274_);
v___x_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_lvl_1274_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_mkConst(v___x_1277_, v___x_1279_);
v___x_1281_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1274_);
v___x_1282_ = l_Lean_mkApp3(v___x_1280_, v___x_1281_, v_lhs_1275_, v_rhs_1276_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1289_, lean_object* v_lhs_1290_, lean_object* v_rhs_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1293_ = lean_box(0);
lean_inc(v_lvl_1289_);
v___x_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_lvl_1289_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_mkConst(v___x_1292_, v___x_1294_);
v___x_1296_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1289_);
v___x_1297_ = l_Lean_mkApp3(v___x_1295_, v___x_1296_, v_lhs_1290_, v_rhs_1291_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1298_){
_start:
{
lean_object* v_lvl_1299_; lean_object* v_cursorPred_1300_; lean_object* v_letMutsPred_1301_; lean_object* v___x_1302_; 
v_lvl_1299_ = lean_ctor_get(v_p_1298_, 0);
lean_inc(v_lvl_1299_);
v_cursorPred_1300_ = lean_ctor_get(v_p_1298_, 1);
lean_inc_ref(v_cursorPred_1300_);
v_letMutsPred_1301_ = lean_ctor_get(v_p_1298_, 2);
lean_inc_ref(v_letMutsPred_1301_);
lean_dec_ref(v_p_1298_);
v___x_1302_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1299_, v_cursorPred_1300_, v_letMutsPred_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(lean_object* v_x_1303_){
_start:
{
switch(lean_obj_tag(v_x_1303_))
{
case 0:
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
return v___x_1304_;
}
case 1:
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_unsigned_to_nat(1u);
return v___x_1305_;
}
case 2:
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_unsigned_to_nat(2u);
return v___x_1306_;
}
default: 
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_unsigned_to_nat(3u);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___boxed(lean_object* v_x_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(v_x_1308_);
lean_dec(v_x_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1310_, lean_object* v_k_1311_){
_start:
{
if (lean_obj_tag(v_t_1310_) == 3)
{
lean_object* v_e_1312_; lean_object* v___x_1313_; 
v_e_1312_ = lean_ctor_get(v_t_1310_, 0);
lean_inc_ref(v_e_1312_);
lean_dec_ref_known(v_t_1310_, 1);
v___x_1313_ = lean_apply_1(v_k_1311_, v_e_1312_);
return v___x_1313_;
}
else
{
lean_dec(v_t_1310_);
return v_k_1311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1314_, lean_object* v_ctorIdx_1315_, lean_object* v_t_1316_, lean_object* v_h_1317_, lean_object* v_k_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1316_, v_k_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1320_, lean_object* v_ctorIdx_1321_, lean_object* v_t_1322_, lean_object* v_h_1323_, lean_object* v_k_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1320_, v_ctorIdx_1321_, v_t_1322_, v_h_1323_, v_k_1324_);
lean_dec(v_ctorIdx_1321_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1326_, lean_object* v_punit_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1326_, v_punit_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1329_, lean_object* v_t_1330_, lean_object* v_h_1331_, lean_object* v_punit_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1330_, v_punit_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1334_, lean_object* v_false_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1334_, v_false_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1337_, lean_object* v_t_1338_, lean_object* v_h_1339_, lean_object* v_false_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1338_, v_false_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1342_, lean_object* v_true_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1342_, v_true_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1345_, lean_object* v_t_1346_, lean_object* v_h_1347_, lean_object* v_true_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1346_, v_true_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1350_, lean_object* v_other_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1350_, v_other_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1353_, lean_object* v_t_1354_, lean_object* v_h_1355_, lean_object* v_other_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1354_, v_other_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1358_){
_start:
{
lean_object* v_snd_1360_; lean_object* v_fst_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1400_; 
v_snd_1360_ = lean_ctor_get(v_a_1358_, 1);
v_fst_1361_ = lean_ctor_get(v_a_1358_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_a_1358_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1363_ = v_a_1358_;
v_isShared_1364_ = v_isSharedCheck_1400_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_snd_1360_);
lean_inc(v_fst_1361_);
lean_dec(v_a_1358_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1400_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1399_; 
v_fst_1365_ = lean_ctor_get(v_snd_1360_, 0);
v_snd_1366_ = lean_ctor_get(v_snd_1360_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_snd_1360_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1368_ = v_snd_1360_;
v_isShared_1369_ = v_isSharedCheck_1399_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_snd_1366_);
lean_inc(v_fst_1365_);
lean_dec(v_snd_1360_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1399_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1371_ = lean_unsigned_to_nat(4u);
v___x_1372_ = l_Lean_Expr_isAppOfArity(v_fst_1365_, v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1374_; 
if (v_isShared_1369_ == 0)
{
v___x_1374_ = v___x_1368_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_fst_1365_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_snd_1366_);
v___x_1374_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1376_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v___x_1374_);
v___x_1376_ = v___x_1363_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_fst_1361_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
}
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1380_ = lean_unsigned_to_nat(3u);
v___x_1381_ = lean_unsigned_to_nat(2u);
v___x_1382_ = l_Lean_Expr_getAppNumArgs(v_fst_1365_);
v___x_1383_ = lean_nat_sub(v___x_1382_, v___x_1381_);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_sub(v___x_1383_, v___x_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = l_Lean_Expr_getRevArg_x21(v_fst_1365_, v___x_1385_);
v___x_1387_ = lean_array_push(v_snd_1366_, v___x_1386_);
v___x_1388_ = lean_nat_add(v_fst_1361_, v___x_1384_);
lean_dec(v_fst_1361_);
v___x_1389_ = lean_nat_sub(v___x_1382_, v___x_1380_);
lean_dec(v___x_1382_);
v___x_1390_ = lean_nat_sub(v___x_1389_, v___x_1384_);
lean_dec(v___x_1389_);
v___x_1391_ = l_Lean_Expr_getRevArg_x21(v_fst_1365_, v___x_1390_);
lean_dec(v_fst_1365_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1387_);
lean_ctor_set(v___x_1368_, 0, v___x_1391_);
v___x_1393_ = v___x_1368_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1387_);
v___x_1393_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1395_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v___x_1393_);
lean_ctor_set(v___x_1363_, 0, v___x_1388_);
v___x_1395_ = v___x_1363_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
v_a_1358_ = v___x_1395_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_fst_1404_, lean_object* v_p_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_inc(v_fst_1404_);
v___x_1406_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1404_);
v___x_1407_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1404_, v___x_1406_, v_p_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_letMutsTuple_1408_, lean_object* v___x_1409_, uint8_t v___x_1410_, lean_object* v_fvarId_1411_){
_start:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1408_);
v___x_1413_ = l_Lean_instBEqFVarId_beq(v_fvarId_1411_, v___x_1412_);
lean_dec(v___x_1412_);
if (v___x_1413_ == 0)
{
uint8_t v___x_1414_; 
v___x_1414_ = l_Lean_LocalContext_contains(v___x_1409_, v_fvarId_1411_);
return v___x_1414_;
}
else
{
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1415_, lean_object* v___x_1416_, lean_object* v___x_1417_, lean_object* v_fvarId_1418_){
_start:
{
uint8_t v___x_11102__boxed_1419_; uint8_t v_res_1420_; lean_object* v_r_1421_; 
v___x_11102__boxed_1419_ = lean_unbox(v___x_1417_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1415_, v___x_1416_, v___x_11102__boxed_1419_, v_fvarId_1418_);
lean_dec(v_fvarId_1418_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_letMutsTuple_1415_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1441_, lean_object* v___x_1442_, lean_object* v_xs_1443_, lean_object* v_letMuts_1444_, lean_object* v_as_1445_, size_t v_sz_1446_, size_t v_i_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_a_1455_; uint8_t v___x_1459_; 
v___x_1459_ = lean_usize_dec_lt(v_i_1447_, v_sz_1446_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_b_1448_);
return v___x_1460_;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_array_uget_borrowed(v_as_1445_, v_i_1447_);
lean_inc(v_a_1461_);
v___x_1462_ = l_Lean_MVarId_getType(v_a_1461_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_snd_1463_; lean_object* v_a_1464_; lean_object* v_fst_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1809_; 
v_snd_1463_ = lean_ctor_get(v_b_1448_, 1);
lean_inc(v_snd_1463_);
v_a_1464_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1462_, 1);
v_fst_1465_ = lean_ctor_get(v_b_1448_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_b_1448_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v_b_1448_, 1);
lean_dec(v_unused_1810_);
v___x_1467_ = v_b_1448_;
v_isShared_1468_ = v_isSharedCheck_1809_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_fst_1465_);
lean_dec(v_b_1448_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1809_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_fst_1469_; lean_object* v_snd_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1808_; 
v_fst_1469_ = lean_ctor_get(v_snd_1463_, 0);
v_snd_1470_ = lean_ctor_get(v_snd_1463_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_snd_1463_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1472_ = v_snd_1463_;
v_isShared_1473_ = v_isSharedCheck_1808_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_snd_1470_);
lean_inc(v_fst_1469_);
lean_dec(v_snd_1463_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1808_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; uint8_t v___y_1488_; lean_object* v___y_1588_; lean_object* v_prefixPoint_x3f_1589_; lean_object* v_suffixPoint_x3f_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v_prefixPoint_x3f_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v_a_1717_; lean_object* v_a_1722_; lean_object* v___x_1796_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1476_ = lean_box(0);
v___x_1796_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1464_, v___y_1450_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = l_Lean_Expr_consumeMData(v_a_1797_);
lean_dec(v_a_1797_);
v_a_1722_ = v___x_1798_;
goto v___jp_1721_;
}
else
{
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1799_; 
v_a_1799_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1796_, 1);
v_a_1722_ = v_a_1799_;
goto v___jp_1721_;
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_del_object(v___x_1472_);
lean_dec(v_snd_1470_);
lean_dec(v_fst_1469_);
lean_del_object(v___x_1467_);
lean_dec(v_fst_1465_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1800_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1796_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1796_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
v___jp_1477_:
{
if (v___y_1488_ == 0)
{
lean_object* v___x_1490_; 
lean_dec_ref(v___y_1483_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___y_1482_);
v___x_1490_ = v___x_1472_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___y_1482_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_snd_1470_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v___x_1490_);
lean_ctor_set(v___x_1467_, 0, v___y_1486_);
v___x_1492_ = v___x_1467_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___y_1486_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
v_a_1455_ = v___x_1492_;
goto v___jp_1454_;
}
}
}
else
{
lean_object* v___x_1496_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1475_);
lean_ctor_set(v___x_1472_, 0, v___y_1483_);
v___x_1496_ = v___x_1472_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___y_1483_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___x_1475_);
v___x_1496_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v___x_1496_);
lean_ctor_set(v___x_1467_, 0, v___x_1474_);
v___x_1498_ = v___x_1467_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; 
v___x_1499_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v_snd_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1575_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v_snd_1501_ = lean_ctor_get(v_a_1500_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_a_1500_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_a_1500_, 0);
lean_dec(v_unused_1576_);
v___x_1503_ = v_a_1500_;
v_isShared_1504_ = v_isSharedCheck_1575_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snd_1501_);
lean_dec(v_a_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1575_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_fst_1505_; lean_object* v_snd_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1574_; 
v_fst_1505_ = lean_ctor_get(v_snd_1501_, 0);
v_snd_1506_ = lean_ctor_get(v_snd_1501_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_snd_1501_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1508_ = v_snd_1501_;
v_isShared_1509_ = v_isSharedCheck_1574_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_snd_1506_);
lean_inc(v_fst_1505_);
lean_dec(v_snd_1501_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1574_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_points_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v_points_1510_ = lean_ctor_get(v_snd_1470_, 0);
v___x_1511_ = lean_array_get_size(v_points_1510_);
v___x_1512_ = lean_array_get_size(v_snd_1506_);
v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1515_; 
lean_dec(v_snd_1506_);
lean_dec(v_fst_1505_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v_snd_1470_);
lean_ctor_set(v___x_1508_, 0, v___y_1482_);
v___x_1515_ = v___x_1508_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___y_1482_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_snd_1470_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1515_);
lean_ctor_set(v___x_1503_, 0, v___y_1486_);
v___x_1517_ = v___x_1503_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___y_1486_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v_a_1455_ = v___x_1517_;
goto v___jp_1454_;
}
}
}
else
{
lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1571_; 
v_isSharedCheck_1571_ = !lean_is_exclusive(v_snd_1470_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; lean_object* v_unused_1573_; 
v_unused_1572_ = lean_ctor_get(v_snd_1470_, 1);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_snd_1470_, 0);
lean_dec(v_unused_1573_);
v___x_1521_ = v_snd_1470_;
v_isShared_1522_ = v_isSharedCheck_1571_;
goto v_resetjp_1520_;
}
else
{
lean_dec(v_snd_1470_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1571_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2));
v___x_1524_ = l_Lean_Expr_isConstOf(v_fst_1505_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3));
lean_inc_ref(v___y_1484_);
lean_inc_ref(v___y_1478_);
lean_inc_ref(v___y_1480_);
v___x_1526_ = l_Lean_Name_mkStr4(v___y_1480_, v___y_1478_, v___y_1484_, v___x_1525_);
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = l_Lean_Expr_isAppOfArity(v_fst_1505_, v___x_1526_, v___x_1527_);
lean_dec(v___x_1526_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
lean_inc_ref(v___y_1484_);
lean_inc_ref(v___y_1478_);
lean_inc_ref(v___y_1480_);
v___x_1530_ = l_Lean_Name_mkStr4(v___y_1480_, v___y_1478_, v___y_1484_, v___x_1529_);
v___x_1531_ = l_Lean_Expr_isAppOfArity(v_fst_1505_, v___x_1530_, v___x_1527_);
lean_dec(v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_fst_1505_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1532_);
lean_ctor_set(v___x_1521_, 0, v_snd_1506_);
v___x_1534_ = v___x_1521_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_snd_1506_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1534_);
lean_ctor_set(v___x_1508_, 0, v___y_1482_);
v___x_1536_ = v___x_1508_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___y_1482_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1536_);
lean_ctor_set(v___x_1503_, 0, v___y_1486_);
v___x_1538_ = v___x_1503_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___y_1486_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
v_a_1455_ = v___x_1538_;
goto v___jp_1454_;
}
}
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec(v_fst_1505_);
v___x_1542_ = lean_box(2);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1542_);
lean_ctor_set(v___x_1521_, 0, v_snd_1506_);
v___x_1544_ = v___x_1521_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_snd_1506_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1544_);
lean_ctor_set(v___x_1508_, 0, v___y_1482_);
v___x_1546_ = v___x_1508_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___y_1482_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1546_);
lean_ctor_set(v___x_1503_, 0, v___y_1486_);
v___x_1548_ = v___x_1503_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___y_1486_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
v_a_1455_ = v___x_1548_;
goto v___jp_1454_;
}
}
}
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec(v_fst_1505_);
v___x_1552_ = lean_box(1);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1552_);
lean_ctor_set(v___x_1521_, 0, v_snd_1506_);
v___x_1554_ = v___x_1521_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_snd_1506_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1554_);
lean_ctor_set(v___x_1508_, 0, v___y_1482_);
v___x_1556_ = v___x_1508_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___y_1482_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1558_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1556_);
lean_ctor_set(v___x_1503_, 0, v___y_1486_);
v___x_1558_ = v___x_1503_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___y_1486_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
v_a_1455_ = v___x_1558_;
goto v___jp_1454_;
}
}
}
}
}
else
{
lean_object* v___x_1563_; 
lean_dec(v_fst_1505_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1476_);
lean_ctor_set(v___x_1521_, 0, v_snd_1506_);
v___x_1563_ = v___x_1521_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_snd_1506_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v___x_1476_);
v___x_1563_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1563_);
lean_ctor_set(v___x_1508_, 0, v___y_1482_);
v___x_1565_ = v___x_1508_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___y_1482_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1565_);
lean_ctor_set(v___x_1503_, 0, v___y_1486_);
v___x_1567_ = v___x_1503_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___y_1486_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
v_a_1455_ = v___x_1567_;
goto v___jp_1454_;
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
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v___y_1486_);
lean_dec(v___y_1482_);
lean_dec(v_snd_1470_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1577_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1499_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1499_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
}
v___jp_1587_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_1596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_1597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_1598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1599_ = lean_unsigned_to_nat(3u);
v___x_1600_ = l_Lean_Expr_isAppOfArity(v___y_1588_, v___x_1598_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v___y_1588_);
lean_del_object(v___x_1472_);
lean_del_object(v___x_1467_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_suffixPoint_x3f_1590_);
lean_ctor_set(v___x_1601_, 1, v_snd_1470_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_prefixPoint_x3f_1589_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v_a_1455_ = v___x_1602_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1603_ = l_Lean_Expr_appFn_x21(v___y_1588_);
v___x_1604_ = l_Lean_Expr_appArg_x21(v___x_1603_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = l_Lean_Expr_appArg_x21(v___y_1588_);
lean_dec_ref(v___y_1588_);
v___x_1606_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1607_ = l_Lean_Expr_isAppOfArity(v___x_1604_, v___x_1606_, v___x_1599_);
if (v___x_1607_ == 0)
{
lean_dec_ref(v___x_1604_);
v___y_1478_ = v___x_1596_;
v___y_1479_ = v___y_1593_;
v___y_1480_ = v___x_1595_;
v___y_1481_ = v___y_1592_;
v___y_1482_ = v_suffixPoint_x3f_1590_;
v___y_1483_ = v___x_1605_;
v___y_1484_ = v___x_1597_;
v___y_1485_ = v___y_1591_;
v___y_1486_ = v_prefixPoint_x3f_1589_;
v___y_1487_ = v___y_1594_;
v___y_1488_ = v___x_1607_;
goto v___jp_1477_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1608_ = lean_unsigned_to_nat(2u);
v___x_1609_ = l_Lean_Expr_getAppNumArgs(v___x_1604_);
v___x_1610_ = lean_nat_sub(v___x_1609_, v___x_1608_);
lean_dec(v___x_1609_);
v___x_1611_ = lean_unsigned_to_nat(1u);
v___x_1612_ = lean_nat_sub(v___x_1610_, v___x_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = l_Lean_Expr_getRevArg_x21(v___x_1604_, v___x_1612_);
lean_dec_ref(v___x_1604_);
lean_inc(v_inv_1441_);
v___x_1614_ = l_Lean_mkMVar(v_inv_1441_);
v___x_1615_ = lean_expr_eqv(v___x_1613_, v___x_1614_);
lean_dec_ref(v___x_1614_);
lean_dec_ref(v___x_1613_);
v___y_1478_ = v___x_1596_;
v___y_1479_ = v___y_1593_;
v___y_1480_ = v___x_1595_;
v___y_1481_ = v___y_1592_;
v___y_1482_ = v_suffixPoint_x3f_1590_;
v___y_1483_ = v___x_1605_;
v___y_1484_ = v___x_1597_;
v___y_1485_ = v___y_1591_;
v___y_1486_ = v_prefixPoint_x3f_1589_;
v___y_1487_ = v___y_1594_;
v___y_1488_ = v___x_1615_;
goto v___jp_1477_;
}
}
}
v___jp_1616_:
{
if (v___y_1629_ == 0)
{
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec_ref(v___y_1617_);
v___y_1588_ = v___y_1627_;
v_prefixPoint_x3f_1589_ = v___y_1625_;
v_suffixPoint_x3f_1590_ = v_fst_1469_;
v___y_1591_ = v___y_1620_;
v___y_1592_ = v___y_1623_;
v___y_1593_ = v___y_1621_;
v___y_1594_ = v___y_1628_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc_ref(v_xs_1443_);
v___x_1631_ = l_Lean_Meta_mkProjection(v_xs_1443_, v___x_1630_, v___y_1620_, v___y_1623_, v___y_1621_, v___y_1628_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = l_Lean_Meta_mkEq(v_a_1632_, v___y_1619_, v___y_1620_, v___y_1623_, v___y_1621_, v___y_1628_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1635_, 0, v___y_1617_);
lean_closure_set(v___x_1635_, 1, v___y_1626_);
lean_inc(v_a_1461_);
v___x_1636_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1461_, v___x_1635_, v___y_1620_, v___y_1623_, v___y_1621_, v___y_1628_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = l_Lean_Expr_replaceFVar(v_a_1637_, v___y_1618_, v_letMuts_1444_);
lean_dec(v_a_1637_);
if (lean_obj_tag(v_fst_1469_) == 1)
{
lean_object* v_val_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_a_1634_);
lean_dec_ref(v___y_1622_);
v_val_1639_ = lean_ctor_get(v_fst_1469_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_fst_1469_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1641_ = v_fst_1469_;
v_isShared_1642_ = v_isSharedCheck_1657_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_dec(v_fst_1469_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1657_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_lvl_1643_; lean_object* v_cursorPred_1644_; lean_object* v_letMutsPred_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1656_; 
v_lvl_1643_ = lean_ctor_get(v_val_1639_, 0);
v_cursorPred_1644_ = lean_ctor_get(v_val_1639_, 1);
v_letMutsPred_1645_ = lean_ctor_get(v_val_1639_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_val_1639_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1647_ = v_val_1639_;
v_isShared_1648_ = v_isSharedCheck_1656_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_letMutsPred_1645_);
lean_inc(v_cursorPred_1644_);
lean_inc(v_lvl_1643_);
lean_dec(v_val_1639_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1656_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1624_, v_letMutsPred_1645_, v___x_1638_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 2, v___x_1649_);
v___x_1651_ = v___x_1647_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_lvl_1643_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_cursorPred_1644_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1651_);
v___x_1653_ = v___x_1641_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v___y_1588_ = v___y_1627_;
v_prefixPoint_x3f_1589_ = v___y_1625_;
v_suffixPoint_x3f_1590_ = v___x_1653_;
v___y_1591_ = v___y_1620_;
v___y_1592_ = v___y_1623_;
v___y_1593_ = v___y_1621_;
v___y_1594_ = v___y_1628_;
goto v___jp_1587_;
}
}
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v_fst_1469_);
v___x_1658_ = lean_apply_1(v___y_1622_, v_a_1634_);
v___x_1659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___y_1624_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
lean_ctor_set(v___x_1659_, 2, v___x_1638_);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
v___y_1588_ = v___y_1627_;
v_prefixPoint_x3f_1589_ = v___y_1625_;
v_suffixPoint_x3f_1590_ = v___x_1660_;
v___y_1591_ = v___y_1620_;
v___y_1592_ = v___y_1623_;
v___y_1593_ = v___y_1621_;
v___y_1594_ = v___y_1628_;
goto v___jp_1587_;
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_a_1634_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___y_1618_);
lean_del_object(v___x_1472_);
lean_dec(v_snd_1470_);
lean_dec(v_fst_1469_);
lean_del_object(v___x_1467_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1661_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1636_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1636_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec_ref(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_del_object(v___x_1472_);
lean_dec(v_snd_1470_);
lean_dec(v_fst_1469_);
lean_del_object(v___x_1467_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1669_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1633_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1633_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec_ref(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_del_object(v___x_1472_);
lean_dec(v_snd_1470_);
lean_dec(v_fst_1469_);
lean_del_object(v___x_1467_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1677_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1631_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1631_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
v___jp_1685_:
{
lean_object* v___x_1696_; 
lean_inc(v_inv_1441_);
v___x_1696_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v___y_1688_, v_inv_1441_);
lean_dec_ref(v___y_1688_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_invariantUse_1697_; lean_object* v_conditionIdx_1698_; lean_object* v_cursorSuffix_1699_; lean_object* v_letMutsTuple_1700_; uint8_t v___x_1701_; uint8_t v___x_1702_; 
v_invariantUse_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc_ref(v_invariantUse_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v_conditionIdx_1698_ = lean_ctor_get(v_invariantUse_1697_, 0);
lean_inc(v_conditionIdx_1698_);
v_cursorSuffix_1699_ = lean_ctor_get(v_invariantUse_1697_, 2);
lean_inc_ref(v_cursorSuffix_1699_);
v_letMutsTuple_1700_ = lean_ctor_get(v_invariantUse_1697_, 4);
lean_inc_ref(v_letMutsTuple_1700_);
lean_dec_ref(v_invariantUse_1697_);
v___x_1701_ = lean_nat_dec_eq(v_conditionIdx_1698_, v___x_1474_);
lean_dec(v_conditionIdx_1698_);
v___x_1702_ = lean_bool_not(v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1703_ = lean_box(v___x_1459_);
lean_inc_ref(v___x_1442_);
lean_inc_ref(v_letMutsTuple_1700_);
v___f_1704_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1704_, 0, v_letMutsTuple_1700_);
lean_closure_set(v___f_1704_, 1, v___x_1442_);
lean_closure_set(v___f_1704_, 2, v___x_1703_);
v___x_1705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4));
v___x_1706_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1699_, v___x_1705_);
if (v___x_1706_ == 0)
{
v___y_1617_ = v___y_1687_;
v___y_1618_ = v_letMutsTuple_1700_;
v___y_1619_ = v_cursorSuffix_1699_;
v___y_1620_ = v___y_1692_;
v___y_1621_ = v___y_1694_;
v___y_1622_ = v___y_1690_;
v___y_1623_ = v___y_1693_;
v___y_1624_ = v___y_1686_;
v___y_1625_ = v_prefixPoint_x3f_1691_;
v___y_1626_ = v___f_1704_;
v___y_1627_ = v___y_1689_;
v___y_1628_ = v___y_1695_;
v___y_1629_ = v___x_1706_;
goto v___jp_1616_;
}
else
{
uint8_t v___x_1707_; 
v___x_1707_ = l_Lean_Expr_isFVar(v_letMutsTuple_1700_);
v___y_1617_ = v___y_1687_;
v___y_1618_ = v_letMutsTuple_1700_;
v___y_1619_ = v_cursorSuffix_1699_;
v___y_1620_ = v___y_1692_;
v___y_1621_ = v___y_1694_;
v___y_1622_ = v___y_1690_;
v___y_1623_ = v___y_1693_;
v___y_1624_ = v___y_1686_;
v___y_1625_ = v_prefixPoint_x3f_1691_;
v___y_1626_ = v___f_1704_;
v___y_1627_ = v___y_1689_;
v___y_1628_ = v___y_1695_;
v___y_1629_ = v___x_1707_;
goto v___jp_1616_;
}
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec_ref(v_letMutsTuple_1700_);
lean_dec_ref(v_cursorSuffix_1699_);
lean_dec_ref(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_del_object(v___x_1472_);
lean_del_object(v___x_1467_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_fst_1469_);
lean_ctor_set(v___x_1708_, 1, v_snd_1470_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v_prefixPoint_x3f_1691_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v_a_1455_ = v___x_1709_;
goto v___jp_1454_;
}
}
else
{
lean_dec(v___x_1696_);
lean_dec_ref(v___y_1690_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
v___y_1588_ = v___y_1689_;
v_prefixPoint_x3f_1589_ = v_prefixPoint_x3f_1691_;
v_suffixPoint_x3f_1590_ = v_fst_1469_;
v___y_1591_ = v___y_1692_;
v___y_1592_ = v___y_1693_;
v___y_1593_ = v___y_1694_;
v___y_1594_ = v___y_1695_;
goto v___jp_1587_;
}
}
v___jp_1710_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_inc_ref(v___y_1716_);
v___x_1718_ = lean_apply_1(v___y_1716_, v___y_1715_);
lean_inc(v___y_1711_);
v___x_1719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1719_, 0, v___y_1711_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
lean_ctor_set(v___x_1719_, 2, v_a_1717_);
v___x_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
v___y_1686_ = v___y_1711_;
v___y_1687_ = v___y_1712_;
v___y_1688_ = v___y_1713_;
v___y_1689_ = v___y_1714_;
v___y_1690_ = v___y_1716_;
v_prefixPoint_x3f_1691_ = v___x_1720_;
v___y_1692_ = v___y_1449_;
v___y_1693_ = v___y_1450_;
v___y_1694_ = v___y_1451_;
v___y_1695_ = v___y_1452_;
goto v___jp_1685_;
}
v___jp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_inc_ref(v_a_1722_);
v___x_1723_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1723_, 0, v_a_1722_);
lean_inc(v_a_1461_);
v___x_1724_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1461_, v___x_1723_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
if (lean_obj_tag(v_a_1725_) == 1)
{
lean_object* v_val_1726_; lean_object* v_snd_1727_; lean_object* v_fst_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1787_; 
v_val_1726_ = lean_ctor_get(v_a_1725_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v_a_1725_, 1);
v_snd_1727_ = lean_ctor_get(v_val_1726_, 1);
v_fst_1728_ = lean_ctor_get(v_val_1726_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_val_1726_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1730_ = v_val_1726_;
v_isShared_1731_ = v_isSharedCheck_1787_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_snd_1727_);
lean_inc(v_fst_1728_);
lean_dec(v_val_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1787_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_fst_1732_; lean_object* v_snd_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1786_; 
v_fst_1732_ = lean_ctor_get(v_snd_1727_, 0);
v_snd_1733_ = lean_ctor_get(v_snd_1727_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_snd_1727_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1735_ = v_snd_1727_;
v_isShared_1736_ = v_isSharedCheck_1786_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_snd_1733_);
lean_inc(v_fst_1732_);
lean_dec(v_snd_1727_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1786_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___f_1737_; lean_object* v___x_1738_; 
lean_inc(v_fst_1728_);
v___f_1737_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_1737_, 0, v_fst_1728_);
lean_inc(v_inv_1441_);
v___x_1738_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1733_, v_inv_1441_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_invariantUse_1739_; lean_object* v_conditionIdx_1740_; lean_object* v_cursorPrefix_1741_; lean_object* v_letMutsTuple_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; 
v_invariantUse_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_invariantUse_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v_conditionIdx_1740_ = lean_ctor_get(v_invariantUse_1739_, 0);
lean_inc(v_conditionIdx_1740_);
v_cursorPrefix_1741_ = lean_ctor_get(v_invariantUse_1739_, 1);
lean_inc_ref(v_cursorPrefix_1741_);
v_letMutsTuple_1742_ = lean_ctor_get(v_invariantUse_1739_, 4);
lean_inc_ref(v_letMutsTuple_1742_);
lean_dec_ref(v_invariantUse_1739_);
v___x_1743_ = lean_nat_dec_eq(v_conditionIdx_1740_, v___x_1474_);
lean_dec(v_conditionIdx_1740_);
v___x_1744_ = lean_bool_not(v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
lean_del_object(v___x_1735_);
lean_del_object(v___x_1730_);
v___x_1745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__4));
v___x_1746_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1741_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_dec_ref(v_letMutsTuple_1742_);
lean_dec_ref(v_cursorPrefix_1741_);
v___y_1686_ = v_fst_1728_;
v___y_1687_ = v_snd_1733_;
v___y_1688_ = v_fst_1732_;
v___y_1689_ = v_a_1722_;
v___y_1690_ = v___f_1737_;
v_prefixPoint_x3f_1691_ = v_fst_1465_;
v___y_1692_ = v___y_1449_;
v___y_1693_ = v___y_1450_;
v___y_1694_ = v___y_1451_;
v___y_1695_ = v___y_1452_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_fst_1465_);
v___x_1747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1443_);
v___x_1748_ = l_Lean_Meta_mkProjection(v_xs_1443_, v___x_1747_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = l_Lean_Meta_mkEq(v_a_1749_, v_cursorPrefix_1741_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
lean_inc_ref(v_letMuts_1444_);
v___x_1752_ = l_Lean_Meta_mkEq(v_letMuts_1444_, v_letMutsTuple_1742_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
lean_inc(v_fst_1728_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_fst_1728_, v_a_1753_);
v___y_1711_ = v_fst_1728_;
v___y_1712_ = v_snd_1733_;
v___y_1713_ = v_fst_1732_;
v___y_1714_ = v_a_1722_;
v___y_1715_ = v_a_1751_;
v___y_1716_ = v___f_1737_;
v_a_1717_ = v___x_1754_;
goto v___jp_1710_;
}
else
{
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1755_; 
v_a_1755_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1752_, 1);
v___y_1711_ = v_fst_1728_;
v___y_1712_ = v_snd_1733_;
v___y_1713_ = v_fst_1732_;
v___y_1714_ = v_a_1722_;
v___y_1715_ = v_a_1751_;
v___y_1716_ = v___f_1737_;
v_a_1717_ = v_a_1755_;
goto v___jp_1710_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1751_);
lean_dec_ref(v___f_1737_);
lean_dec(v_snd_1733_);
lean_dec(v_fst_1732_);
lean_dec(v_fst_1728_);
lean_dec_ref(v_a_1722_);
lean_del_object(v___x_1472_);
lean_dec(v_snd_1470_);
lean_dec(v_fst_1469_);
lean_del_object(v___x_1467_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1756_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1752_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1752_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_letMutsTuple_1742_);
lean_dec_ref(v___f_1737_);
lean_dec(v_snd_1733_);
lean_dec(v_fst_1732_);
lean_dec(v_fst_1728_);
lean_dec_ref(v_a_1722_);
lean_del_object(v___x_1472_);
lean_dec(v_snd_1470_);
lean_dec(v_fst_1469_);
lean_del_object(v___x_1467_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1764_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1750_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1750_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v_letMutsTuple_1742_);
lean_dec_ref(v_cursorPrefix_1741_);
lean_dec_ref(v___f_1737_);
lean_dec(v_snd_1733_);
lean_dec(v_fst_1732_);
lean_dec(v_fst_1728_);
lean_dec_ref(v_a_1722_);
lean_del_object(v___x_1472_);
lean_dec(v_snd_1470_);
lean_dec(v_fst_1469_);
lean_del_object(v___x_1467_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1772_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1748_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1748_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
else
{
lean_object* v___x_1781_; 
lean_dec_ref(v_letMutsTuple_1742_);
lean_dec_ref(v_cursorPrefix_1741_);
lean_dec_ref(v___f_1737_);
lean_dec(v_snd_1733_);
lean_dec(v_fst_1732_);
lean_dec(v_fst_1728_);
lean_dec_ref(v_a_1722_);
lean_del_object(v___x_1472_);
lean_del_object(v___x_1467_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v_snd_1470_);
lean_ctor_set(v___x_1735_, 0, v_fst_1469_);
v___x_1781_ = v___x_1735_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fst_1469_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_snd_1470_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v___x_1781_);
lean_ctor_set(v___x_1730_, 0, v_fst_1465_);
v___x_1783_ = v___x_1730_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_fst_1465_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
v_a_1455_ = v___x_1783_;
goto v___jp_1454_;
}
}
}
}
else
{
lean_dec(v___x_1738_);
lean_del_object(v___x_1735_);
lean_del_object(v___x_1730_);
v___y_1686_ = v_fst_1728_;
v___y_1687_ = v_snd_1733_;
v___y_1688_ = v_fst_1732_;
v___y_1689_ = v_a_1722_;
v___y_1690_ = v___f_1737_;
v_prefixPoint_x3f_1691_ = v_fst_1465_;
v___y_1692_ = v___y_1449_;
v___y_1693_ = v___y_1450_;
v___y_1694_ = v___y_1451_;
v___y_1695_ = v___y_1452_;
goto v___jp_1685_;
}
}
}
}
else
{
lean_dec(v_a_1725_);
v___y_1588_ = v_a_1722_;
v_prefixPoint_x3f_1589_ = v_fst_1465_;
v_suffixPoint_x3f_1590_ = v_fst_1469_;
v___y_1591_ = v___y_1449_;
v___y_1592_ = v___y_1450_;
v___y_1593_ = v___y_1451_;
v___y_1594_ = v___y_1452_;
goto v___jp_1587_;
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_a_1722_);
lean_del_object(v___x_1472_);
lean_dec(v_snd_1470_);
lean_dec(v_fst_1469_);
lean_del_object(v___x_1467_);
lean_dec(v_fst_1465_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1788_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1724_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1724_);
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
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_b_1448_);
lean_dec_ref(v_letMuts_1444_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec(v_inv_1441_);
v_a_1811_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1462_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1462_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
v___jp_1454_:
{
size_t v___x_1456_; size_t v___x_1457_; 
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1447_, v___x_1456_);
v_i_1447_ = v___x_1457_;
v_b_1448_ = v_a_1455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1819_, lean_object* v___x_1820_, lean_object* v_xs_1821_, lean_object* v_letMuts_1822_, lean_object* v_as_1823_, lean_object* v_sz_1824_, lean_object* v_i_1825_, lean_object* v_b_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
size_t v_sz_boxed_1832_; size_t v_i_boxed_1833_; lean_object* v_res_1834_; 
v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1824_);
lean_dec(v_sz_1824_);
v_i_boxed_1833_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1819_, v___x_1820_, v_xs_1821_, v_letMuts_1822_, v_as_1823_, v_sz_boxed_1832_, v_i_boxed_1833_, v_b_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_as_1823_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1844_, lean_object* v_inv_1845_, lean_object* v_xs_1846_, lean_object* v_letMuts_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_lctx_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; size_t v_sz_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v_lctx_1853_ = lean_ctor_get(v_a_1848_, 2);
v___x_1854_ = lean_box(0);
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1856_ = lean_array_size(v_vcs_1844_);
v___x_1857_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1853_);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1845_, v_lctx_1853_, v_xs_1846_, v_letMuts_1847_, v_vcs_1844_, v_sz_1856_, v___x_1857_, v___x_1855_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1902_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1902_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1902_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v_snd_1867_; lean_object* v_fst_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1901_; 
v_snd_1867_ = lean_ctor_get(v_a_1859_, 1);
v_fst_1868_ = lean_ctor_get(v_a_1859_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_a_1859_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1870_ = v_a_1859_;
v_isShared_1871_ = v_isSharedCheck_1901_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_snd_1867_);
lean_inc(v_fst_1868_);
lean_dec(v_a_1859_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1901_;
goto v_resetjp_1869_;
}
v___jp_1863_:
{
lean_object* v___x_1865_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1854_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1854_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
v_resetjp_1869_:
{
if (lean_obj_tag(v_fst_1868_) == 0)
{
lean_del_object(v___x_1870_);
lean_dec(v_snd_1867_);
goto v___jp_1863_;
}
else
{
lean_object* v_fst_1872_; 
v_fst_1872_ = lean_ctor_get(v_snd_1867_, 0);
lean_inc(v_fst_1872_);
if (lean_obj_tag(v_fst_1872_) == 0)
{
lean_dec_ref_known(v_fst_1868_, 1);
lean_del_object(v___x_1870_);
lean_dec(v_snd_1867_);
goto v___jp_1863_;
}
else
{
lean_object* v_snd_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1899_; 
lean_del_object(v___x_1861_);
v_snd_1873_ = lean_ctor_get(v_snd_1867_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_snd_1867_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_snd_1867_, 0);
lean_dec(v_unused_1900_);
v___x_1875_ = v_snd_1867_;
v_isShared_1876_ = v_isSharedCheck_1899_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snd_1873_);
lean_dec(v_snd_1867_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1899_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_val_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1898_; 
v_val_1877_ = lean_ctor_get(v_fst_1868_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_fst_1868_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1879_ = v_fst_1868_;
v_isShared_1880_ = v_isSharedCheck_1898_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_val_1877_);
lean_dec(v_fst_1868_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1898_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_val_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1897_; 
v_val_1881_ = lean_ctor_get(v_fst_1872_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_fst_1872_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1883_ = v_fst_1872_;
v_isShared_1884_ = v_isSharedCheck_1897_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_val_1881_);
lean_dec(v_fst_1872_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1897_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v_val_1881_);
v___x_1886_ = v___x_1875_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_val_1881_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_snd_1873_);
v___x_1886_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v___x_1886_);
lean_ctor_set(v___x_1870_, 0, v_val_1877_);
v___x_1888_ = v___x_1870_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_val_1877_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1888_);
v___x_1890_ = v___x_1883_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1890_);
v___x_1892_ = v___x_1879_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
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
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_a_1903_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1858_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1858_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1911_, lean_object* v_inv_1912_, lean_object* v_xs_1913_, lean_object* v_letMuts_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1911_, v_inv_1912_, v_xs_1913_, v_letMuts_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec_ref(v_vcs_1911_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_1921_, lean_object* v_a_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1922_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_1929_, lean_object* v_a_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_1929_, v_a_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_MVarId_getDecl(v_m_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v_userName_1945_; lean_object* v_lctx_1946_; lean_object* v_type_1947_; lean_object* v_localInstances_1948_; uint8_t v_kind_1949_; lean_object* v_numScopeArgs_1950_; lean_object* v___x_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v_userName_1945_ = lean_ctor_get(v_a_1944_, 0);
lean_inc(v_userName_1945_);
v_lctx_1946_ = lean_ctor_get(v_a_1944_, 1);
lean_inc_ref(v_lctx_1946_);
v_type_1947_ = lean_ctor_get(v_a_1944_, 2);
lean_inc_ref(v_type_1947_);
v_localInstances_1948_ = lean_ctor_get(v_a_1944_, 4);
lean_inc_ref(v_localInstances_1948_);
v_kind_1949_ = lean_ctor_get_uint8(v_a_1944_, sizeof(void*)*7);
v_numScopeArgs_1950_ = lean_ctor_get(v_a_1944_, 5);
lean_inc(v_numScopeArgs_1950_);
lean_dec(v_a_1944_);
v___x_1951_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1946_, v_localInstances_1948_, v_type_1947_, v_kind_1949_, v_userName_1945_, v_numScopeArgs_1950_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = l_Lean_Expr_mvarId_x21(v_a_1952_);
lean_dec(v_a_1952_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_a_1961_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1951_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1951_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
v_a_1969_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1943_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1943_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_1984_){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = l_String_instInhabitedSlice;
v___x_1986_ = lean_panic_fn_borrowed(v___x_1985_, v_msg_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_1987_, lean_object* v_a_1988_, uint8_t v_b_1989_){
_start:
{
lean_object* v_str_1990_; lean_object* v_startInclusive_1991_; lean_object* v_endExclusive_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_str_1990_ = lean_ctor_get(v_s_1987_, 0);
v_startInclusive_1991_ = lean_ctor_get(v_s_1987_, 1);
v_endExclusive_1992_ = lean_ctor_get(v_s_1987_, 2);
v___x_1993_ = lean_nat_sub(v_endExclusive_1992_, v_startInclusive_1991_);
v___x_1994_ = lean_nat_dec_eq(v_a_1988_, v___x_1993_);
lean_dec(v___x_1993_);
if (v___x_1994_ == 0)
{
uint32_t v___x_1995_; lean_object* v___x_1996_; uint32_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1995_ = 64;
v___x_1996_ = lean_nat_add(v_startInclusive_1991_, v_a_1988_);
lean_dec(v_a_1988_);
v___x_1997_ = lean_string_utf8_get_fast(v_str_1990_, v___x_1996_);
v___x_1998_ = lean_uint32_dec_eq(v___x_1997_, v___x_1995_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_string_utf8_next_fast(v_str_1990_, v___x_1996_);
lean_dec(v___x_1996_);
v___x_2000_ = lean_nat_sub(v___x_1999_, v_startInclusive_1991_);
v_a_1988_ = v___x_2000_;
v_b_1989_ = v___x_1998_;
goto _start;
}
else
{
lean_dec(v___x_1996_);
return v___x_1998_;
}
}
else
{
lean_dec(v_a_1988_);
return v_b_1989_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object* v_s_2002_, lean_object* v_a_2003_, lean_object* v_b_2004_){
_start:
{
uint8_t v_b_boxed_2005_; uint8_t v_res_2006_; lean_object* v_r_2007_; 
v_b_boxed_2005_ = lean_unbox(v_b_2004_);
v_res_2006_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2002_, v_a_2003_, v_b_boxed_2005_);
lean_dec_ref(v_s_2002_);
v_r_2007_ = lean_box(v_res_2006_);
return v_r_2007_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_2008_){
_start:
{
lean_object* v_searcher_2009_; uint8_t v___x_2010_; uint8_t v___x_2011_; 
v_searcher_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = 0;
v___x_2011_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2008_, v_searcher_2009_, v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_2012_){
_start:
{
uint8_t v_res_2013_; lean_object* v_r_2014_; 
v_res_2013_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_2012_);
lean_dec_ref(v_s_2012_);
v_r_2014_ = lean_box(v_res_2013_);
return v_r_2014_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_2019_ = lean_unsigned_to_nat(14u);
v___x_2020_ = lean_unsigned_to_nat(22u);
v___x_2021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_2022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_2023_ = l_mkPanicMessageWithDecl(v___x_2022_, v___x_2021_, v___x_2020_, v___x_2019_, v___x_2018_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_2024_){
_start:
{
switch(lean_obj_tag(v_x_2024_))
{
case 1:
{
lean_object* v_info_2025_; lean_object* v_kind_2026_; lean_object* v_args_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2037_; 
v_info_2025_ = lean_ctor_get(v_x_2024_, 0);
v_kind_2026_ = lean_ctor_get(v_x_2024_, 1);
v_args_2027_ = lean_ctor_get(v_x_2024_, 2);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_x_2024_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2029_ = v_x_2024_;
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_args_2027_);
lean_inc(v_kind_2026_);
lean_inc(v_info_2025_);
lean_dec(v_x_2024_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
size_t v_sz_2031_; size_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v_sz_2031_ = lean_array_size(v_args_2027_);
v___x_2032_ = ((size_t)0ULL);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_2031_, v___x_2032_, v_args_2027_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 2, v___x_2033_);
v___x_2035_ = v___x_2029_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_info_2025_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_kind_2026_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
case 3:
{
lean_object* v_info_2038_; lean_object* v_rawVal_2039_; lean_object* v_val_2040_; lean_object* v_preresolved_2041_; uint8_t v___y_2043_; lean_object* v_str_2060_; lean_object* v_startPos_2061_; lean_object* v_stopPos_2062_; uint8_t v___x_2063_; 
v_info_2038_ = lean_ctor_get(v_x_2024_, 0);
v_rawVal_2039_ = lean_ctor_get(v_x_2024_, 1);
v_val_2040_ = lean_ctor_get(v_x_2024_, 2);
v_preresolved_2041_ = lean_ctor_get(v_x_2024_, 3);
v_str_2060_ = lean_ctor_get(v_rawVal_2039_, 0);
v_startPos_2061_ = lean_ctor_get(v_rawVal_2039_, 1);
v_stopPos_2062_ = lean_ctor_get(v_rawVal_2039_, 2);
v___x_2063_ = lean_string_is_valid_pos(v_str_2060_, v_startPos_2061_);
if (v___x_2063_ == 0)
{
goto v___jp_2056_;
}
else
{
uint8_t v___x_2064_; 
v___x_2064_ = lean_string_is_valid_pos(v_str_2060_, v_stopPos_2062_);
if (v___x_2064_ == 0)
{
goto v___jp_2056_;
}
else
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_nat_dec_le(v_startPos_2061_, v_stopPos_2062_);
if (v___x_2065_ == 0)
{
goto v___jp_2056_;
}
else
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
lean_inc(v_stopPos_2062_);
lean_inc(v_startPos_2061_);
lean_inc_ref(v_str_2060_);
v___x_2066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2066_, 0, v_str_2060_);
lean_ctor_set(v___x_2066_, 1, v_startPos_2061_);
lean_ctor_set(v___x_2066_, 2, v_stopPos_2062_);
v___x_2067_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2066_);
lean_dec_ref_known(v___x_2066_, 3);
v___y_2043_ = v___x_2067_;
goto v___jp_2042_;
}
}
}
v___jp_2042_:
{
if (v___y_2043_ == 0)
{
lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
lean_inc(v_preresolved_2041_);
lean_inc(v_val_2040_);
lean_inc_ref(v_rawVal_2039_);
lean_inc(v_info_2038_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_2024_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; 
v_unused_2052_ = lean_ctor_get(v_x_2024_, 3);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_x_2024_, 2);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_x_2024_, 1);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_x_2024_, 0);
lean_dec(v_unused_2055_);
v___x_2045_ = v_x_2024_;
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v_x_2024_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = l_Lean_Name_eraseMacroScopes(v_val_2040_);
lean_dec(v_val_2040_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 2, v___x_2047_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_info_2038_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_rawVal_2039_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_preresolved_2041_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
return v_x_2024_;
}
}
v___jp_2056_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_2058_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_2057_);
v___x_2059_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2058_);
lean_dec_ref(v___x_2058_);
v___y_2043_ = v___x_2059_;
goto v___jp_2042_;
}
}
default: 
{
return v_x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_2068_, size_t v_i_2069_, lean_object* v_bs_2070_){
_start:
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_usize_dec_lt(v_i_2069_, v_sz_2068_);
if (v___x_2071_ == 0)
{
return v_bs_2070_;
}
else
{
lean_object* v_v_2072_; lean_object* v___x_2073_; lean_object* v_bs_x27_2074_; lean_object* v___x_2075_; size_t v___x_2076_; size_t v___x_2077_; lean_object* v___x_2078_; 
v_v_2072_ = lean_array_uget(v_bs_2070_, v_i_2069_);
v___x_2073_ = lean_unsigned_to_nat(0u);
v_bs_x27_2074_ = lean_array_uset(v_bs_2070_, v_i_2069_, v___x_2073_);
v___x_2075_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_2072_);
v___x_2076_ = ((size_t)1ULL);
v___x_2077_ = lean_usize_add(v_i_2069_, v___x_2076_);
v___x_2078_ = lean_array_uset(v_bs_x27_2074_, v_i_2069_, v___x_2075_);
v_i_2069_ = v___x_2077_;
v_bs_2070_ = v___x_2078_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2080_, lean_object* v_i_2081_, lean_object* v_bs_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2080_);
lean_dec(v_sz_2080_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2083_, v_i_boxed_2084_, v_bs_2082_);
return v_res_2085_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2086_, lean_object* v_inst_2087_, lean_object* v_R_2088_, lean_object* v_a_2089_, uint8_t v_b_2090_, lean_object* v_c_2091_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2086_, v_a_2089_, v_b_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2093_, lean_object* v_inst_2094_, lean_object* v_R_2095_, lean_object* v_a_2096_, lean_object* v_b_2097_, lean_object* v_c_2098_){
_start:
{
uint8_t v_b_boxed_2099_; uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_b_boxed_2099_ = lean_unbox(v_b_2097_);
v_res_2100_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2093_, v_inst_2094_, v_R_2095_, v_a_2096_, v_b_boxed_2099_, v_c_2098_);
lean_dec_ref(v_s_2093_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2102_, lean_object* v_h__1_2103_, lean_object* v_h__2_2104_, lean_object* v_h__3_2105_, lean_object* v_h__4_2106_){
_start:
{
switch(lean_obj_tag(v_x_2102_))
{
case 0:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v_h__3_2105_);
lean_dec(v_h__2_2104_);
lean_dec(v_h__1_2103_);
v___x_2107_ = lean_box(0);
v___x_2108_ = lean_apply_1(v_h__4_2106_, v___x_2107_);
return v___x_2108_;
}
case 1:
{
lean_object* v_info_2109_; lean_object* v_kind_2110_; lean_object* v_args_2111_; lean_object* v___x_2112_; 
lean_dec(v_h__4_2106_);
lean_dec(v_h__3_2105_);
lean_dec(v_h__1_2103_);
v_info_2109_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_info_2109_);
v_kind_2110_ = lean_ctor_get(v_x_2102_, 1);
lean_inc(v_kind_2110_);
v_args_2111_ = lean_ctor_get(v_x_2102_, 2);
lean_inc_ref(v_args_2111_);
lean_dec_ref_known(v_x_2102_, 3);
v___x_2112_ = lean_apply_3(v_h__2_2104_, v_info_2109_, v_kind_2110_, v_args_2111_);
return v___x_2112_;
}
case 2:
{
lean_object* v_info_2113_; lean_object* v_val_2114_; lean_object* v___x_2115_; 
lean_dec(v_h__4_2106_);
lean_dec(v_h__2_2104_);
lean_dec(v_h__1_2103_);
v_info_2113_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_info_2113_);
v_val_2114_ = lean_ctor_get(v_x_2102_, 1);
lean_inc_ref(v_val_2114_);
lean_dec_ref_known(v_x_2102_, 2);
v___x_2115_ = lean_apply_2(v_h__3_2105_, v_info_2113_, v_val_2114_);
return v___x_2115_;
}
default: 
{
lean_object* v_info_2116_; lean_object* v_rawVal_2117_; lean_object* v_val_2118_; lean_object* v_preresolved_2119_; lean_object* v___x_2120_; 
lean_dec(v_h__4_2106_);
lean_dec(v_h__3_2105_);
lean_dec(v_h__2_2104_);
v_info_2116_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_info_2116_);
v_rawVal_2117_ = lean_ctor_get(v_x_2102_, 1);
lean_inc_ref(v_rawVal_2117_);
v_val_2118_ = lean_ctor_get(v_x_2102_, 2);
lean_inc(v_val_2118_);
v_preresolved_2119_ = lean_ctor_get(v_x_2102_, 3);
lean_inc(v_preresolved_2119_);
lean_dec_ref_known(v_x_2102_, 4);
v___x_2120_ = lean_apply_4(v_h__1_2103_, v_info_2116_, v_rawVal_2117_, v_val_2118_, v_preresolved_2119_);
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2121_, lean_object* v_x_2122_, lean_object* v_h__1_2123_, lean_object* v_h__2_2124_, lean_object* v_h__3_2125_, lean_object* v_h__4_2126_){
_start:
{
switch(lean_obj_tag(v_x_2122_))
{
case 0:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v_h__3_2125_);
lean_dec(v_h__2_2124_);
lean_dec(v_h__1_2123_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_apply_1(v_h__4_2126_, v___x_2127_);
return v___x_2128_;
}
case 1:
{
lean_object* v_info_2129_; lean_object* v_kind_2130_; lean_object* v_args_2131_; lean_object* v___x_2132_; 
lean_dec(v_h__4_2126_);
lean_dec(v_h__3_2125_);
lean_dec(v_h__1_2123_);
v_info_2129_ = lean_ctor_get(v_x_2122_, 0);
lean_inc(v_info_2129_);
v_kind_2130_ = lean_ctor_get(v_x_2122_, 1);
lean_inc(v_kind_2130_);
v_args_2131_ = lean_ctor_get(v_x_2122_, 2);
lean_inc_ref(v_args_2131_);
lean_dec_ref_known(v_x_2122_, 3);
v___x_2132_ = lean_apply_3(v_h__2_2124_, v_info_2129_, v_kind_2130_, v_args_2131_);
return v___x_2132_;
}
case 2:
{
lean_object* v_info_2133_; lean_object* v_val_2134_; lean_object* v___x_2135_; 
lean_dec(v_h__4_2126_);
lean_dec(v_h__2_2124_);
lean_dec(v_h__1_2123_);
v_info_2133_ = lean_ctor_get(v_x_2122_, 0);
lean_inc(v_info_2133_);
v_val_2134_ = lean_ctor_get(v_x_2122_, 1);
lean_inc_ref(v_val_2134_);
lean_dec_ref_known(v_x_2122_, 2);
v___x_2135_ = lean_apply_2(v_h__3_2125_, v_info_2133_, v_val_2134_);
return v___x_2135_;
}
default: 
{
lean_object* v_info_2136_; lean_object* v_rawVal_2137_; lean_object* v_val_2138_; lean_object* v_preresolved_2139_; lean_object* v___x_2140_; 
lean_dec(v_h__4_2126_);
lean_dec(v_h__3_2125_);
lean_dec(v_h__2_2124_);
v_info_2136_ = lean_ctor_get(v_x_2122_, 0);
lean_inc(v_info_2136_);
v_rawVal_2137_ = lean_ctor_get(v_x_2122_, 1);
lean_inc_ref(v_rawVal_2137_);
v_val_2138_ = lean_ctor_get(v_x_2122_, 2);
lean_inc(v_val_2138_);
v_preresolved_2139_ = lean_ctor_get(v_x_2122_, 3);
lean_inc(v_preresolved_2139_);
lean_dec_ref_known(v_x_2122_, 4);
v___x_2140_ = lean_apply_4(v_h__1_2123_, v_info_2136_, v_rawVal_2137_, v_val_2138_, v_preresolved_2139_);
return v___x_2140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2141_, lean_object* v_h__1_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_apply_2(v_h__1_2142_, v_x_2141_, lean_box(0));
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2144_, lean_object* v_P_2145_, lean_object* v_motive_2146_, lean_object* v_x_2147_, lean_object* v_h__1_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_apply_2(v_h__1_2148_, v_x_2147_, lean_box(0));
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2152_, lean_object* v_syn_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2155_, lean_object* v_syn_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2155_, v_syn_2156_);
lean_dec(v_name_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2164_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2192_ = lean_unsigned_to_nat(2u);
v___x_2193_ = l_Lean_Expr_isAppOfArity(v_e_2164_, v___x_2191_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2195_ = lean_unsigned_to_nat(3u);
v___x_2196_ = l_Lean_Expr_isAppOfArity(v_e_2164_, v___x_2194_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2198_ = l_Lean_Expr_isAppOfArity(v_e_2164_, v___x_2197_, v___x_2195_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2200_ = l_Lean_Expr_isAppOfArity(v_e_2164_, v___x_2199_, v___x_2195_);
if (v___x_2200_ == 0)
{
goto v___jp_2165_;
}
else
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_Expr_appArg_x21(v_e_2164_);
if (lean_obj_tag(v___x_2201_) == 6)
{
lean_object* v_binderName_2202_; lean_object* v_binderType_2203_; lean_object* v_body_2204_; uint8_t v_binderInfo_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v_e_2164_);
v_binderName_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_binderName_2202_);
v_binderType_2203_ = lean_ctor_get(v___x_2201_, 1);
lean_inc_ref(v_binderType_2203_);
v_body_2204_ = lean_ctor_get(v___x_2201_, 2);
lean_inc_ref(v_body_2204_);
v_binderInfo_2205_ = lean_ctor_get_uint8(v___x_2201_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_2201_, 3);
v___x_2206_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2204_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_dec_ref(v_binderType_2203_);
lean_dec(v_binderName_2202_);
return v___x_2206_;
}
else
{
lean_object* v_val_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2224_; 
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2224_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_val_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2224_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_fst_2211_; lean_object* v_snd_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2223_; 
v_fst_2211_ = lean_ctor_get(v_val_2207_, 0);
v_snd_2212_ = lean_ctor_get(v_val_2207_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_val_2207_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2214_ = v_val_2207_;
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_snd_2212_);
lean_inc(v_fst_2211_);
lean_dec(v_val_2207_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = l_Lean_mkForall(v_binderName_2202_, v_binderInfo_2205_, v_binderType_2203_, v_snd_2212_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2216_);
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_fst_2211_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2218_);
v___x_2220_ = v___x_2209_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2201_);
goto v___jp_2165_;
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = l_Lean_Expr_appFn_x21(v_e_2164_);
v___x_2226_ = l_Lean_Expr_appArg_x21(v___x_2225_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2226_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_dec_ref(v_e_2164_);
return v___x_2227_;
}
else
{
lean_object* v_val_2228_; lean_object* v_snd_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_val_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_val_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v_snd_2229_ = lean_ctor_get(v_val_2228_, 1);
lean_inc(v_snd_2229_);
lean_dec(v_val_2228_);
v___x_2230_ = l_Lean_Expr_appArg_x21(v_e_2164_);
lean_dec_ref(v_e_2164_);
v___x_2231_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_dec(v_snd_2229_);
return v___x_2231_;
}
else
{
lean_object* v_val_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2249_; 
v_val_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2249_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_val_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2249_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v_fst_2236_; lean_object* v_snd_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2248_; 
v_fst_2236_ = lean_ctor_get(v_val_2232_, 0);
v_snd_2237_ = lean_ctor_get(v_val_2232_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_val_2232_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2239_ = v_val_2232_;
v_isShared_2240_ = v_isSharedCheck_2248_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_snd_2237_);
lean_inc(v_fst_2236_);
lean_dec(v_val_2232_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2248_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = l_Lean_mkOr(v_snd_2229_, v_snd_2237_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 1, v___x_2241_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_fst_2236_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2245_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2243_);
v___x_2245_ = v___x_2234_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
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
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = l_Lean_Expr_appFn_x21(v_e_2164_);
v___x_2251_ = l_Lean_Expr_appArg_x21(v___x_2250_);
lean_dec_ref(v___x_2250_);
v___x_2252_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2251_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_dec_ref(v_e_2164_);
return v___x_2252_;
}
else
{
lean_object* v_val_2253_; lean_object* v_snd_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v_val_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_val_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v_snd_2254_ = lean_ctor_get(v_val_2253_, 1);
lean_inc(v_snd_2254_);
lean_dec(v_val_2253_);
v___x_2255_ = l_Lean_Expr_appArg_x21(v_e_2164_);
lean_dec_ref(v_e_2164_);
v___x_2256_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2255_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_dec(v_snd_2254_);
return v___x_2256_;
}
else
{
lean_object* v_val_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2274_; 
v_val_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2274_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_val_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2274_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_fst_2261_; lean_object* v_snd_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2273_; 
v_fst_2261_ = lean_ctor_get(v_val_2257_, 0);
v_snd_2262_ = lean_ctor_get(v_val_2257_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_val_2257_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2264_ = v_val_2257_;
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_snd_2262_);
lean_inc(v_fst_2261_);
lean_dec(v_val_2257_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = l_Lean_mkAnd(v_snd_2254_, v_snd_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_fst_2261_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2268_);
v___x_2270_ = v___x_2259_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
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
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = l_Lean_Expr_getAppFn(v_e_2164_);
v___x_2277_ = l_Lean_Expr_constLevels_x21(v___x_2276_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = l_List_get_x21Internal___redArg(v___x_2275_, v___x_2277_, v___x_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = l_Lean_Expr_getAppNumArgs(v_e_2164_);
v___x_2282_ = lean_nat_sub(v___x_2281_, v___x_2280_);
lean_dec(v___x_2281_);
v___x_2283_ = lean_nat_sub(v___x_2282_, v___x_2280_);
lean_dec(v___x_2282_);
v___x_2284_ = l_Lean_Expr_getRevArg_x21(v_e_2164_, v___x_2283_);
lean_dec_ref(v_e_2164_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2279_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
v___jp_2165_:
{
if (lean_obj_tag(v_e_2164_) == 8)
{
lean_object* v_declName_2166_; lean_object* v_type_2167_; lean_object* v_value_2168_; lean_object* v_body_2169_; uint8_t v_nondep_2170_; lean_object* v___x_2171_; 
v_declName_2166_ = lean_ctor_get(v_e_2164_, 0);
lean_inc(v_declName_2166_);
v_type_2167_ = lean_ctor_get(v_e_2164_, 1);
lean_inc_ref(v_type_2167_);
v_value_2168_ = lean_ctor_get(v_e_2164_, 2);
lean_inc_ref(v_value_2168_);
v_body_2169_ = lean_ctor_get(v_e_2164_, 3);
lean_inc_ref(v_body_2169_);
v_nondep_2170_ = lean_ctor_get_uint8(v_e_2164_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2164_, 4);
v___x_2171_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2169_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_dec_ref(v_value_2168_);
lean_dec_ref(v_type_2167_);
lean_dec(v_declName_2166_);
return v___x_2171_;
}
else
{
lean_object* v_val_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2189_; 
v_val_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2189_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_val_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2189_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2188_; 
v_fst_2176_ = lean_ctor_get(v_val_2172_, 0);
v_snd_2177_ = lean_ctor_get(v_val_2172_, 1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_val_2172_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2179_ = v_val_2172_;
v_isShared_2180_ = v_isSharedCheck_2188_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_snd_2177_);
lean_inc(v_fst_2176_);
lean_dec(v_val_2172_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2188_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2181_ = l_Lean_Expr_letE___override(v_declName_2166_, v_type_2167_, v_value_2168_, v_snd_2177_, v_nondep_2170_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v___x_2181_);
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_fst_2176_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2185_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2183_);
v___x_2185_ = v___x_2174_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
else
{
lean_object* v___x_2190_; 
lean_dec_ref(v_e_2164_);
v___x_2190_ = lean_box(0);
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2287_){
_start:
{
lean_object* v___x_2288_; 
lean_inc_ref(v_e_2287_);
v___x_2288_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
return v_e_2287_;
}
else
{
lean_object* v_val_2289_; lean_object* v_fst_2290_; lean_object* v_snd_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v_e_2287_);
v_val_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_val_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v_fst_2290_ = lean_ctor_get(v_val_2289_, 0);
lean_inc_n(v_fst_2290_, 2);
v_snd_2291_ = lean_ctor_get(v_val_2289_, 1);
lean_inc(v_snd_2291_);
lean_dec(v_val_2289_);
v___x_2292_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2290_);
v___x_2293_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2290_, v___x_2292_, v_snd_2291_);
return v___x_2293_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Array_mkArray0(lean_box(0));
return v___x_2304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2343_ = l_String_toRawSubstring_x27(v___x_2342_);
return v___x_2343_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2360_ = l_String_toRawSubstring_x27(v___x_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2375_, lean_object* v_default_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2382_; lean_object* v_handlers_2383_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2383_ = l_Lean_Syntax_SepArray_ofElems(v___x_2382_, v_handlers_2375_);
switch(lean_obj_tag(v_default_2376_))
{
case 0:
{
lean_object* v_ref_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_ref_2384_ = lean_ctor_get(v_a_2379_, 5);
v___x_2385_ = 0;
v___x_2386_ = l_Lean_SourceInfo_fromRef(v_ref_2384_, v___x_2385_);
v___x_2387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2386_, 3);
v___x_2389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2391_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2392_ = l_Array_append___redArg(v___x_2391_, v_handlers_2383_);
lean_dec_ref(v_handlers_2383_);
v___x_2393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2386_);
lean_ctor_set(v___x_2393_, 1, v___x_2390_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
v___x_2394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2386_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Lean_Syntax_node3(v___x_2386_, v___x_2387_, v___x_2389_, v___x_2393_, v___x_2395_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
case 1:
{
lean_object* v_ref_2398_; lean_object* v_quotContext_2399_; lean_object* v_currMacroScope_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v_ref_2398_ = lean_ctor_get(v_a_2379_, 5);
v_quotContext_2399_ = lean_ctor_get(v_a_2379_, 10);
v_currMacroScope_2400_ = lean_ctor_get(v_a_2379_, 11);
v___x_2401_ = 0;
v___x_2402_ = l_Lean_SourceInfo_fromRef(v_ref_2398_, v___x_2401_);
v___x_2403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2402_, 12);
v___x_2405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2402_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2402_);
lean_ctor_set(v___x_2411_, 1, v___x_2409_);
v___x_2412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2402_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2416_ = l_Array_append___redArg(v___x_2415_, v_handlers_2383_);
lean_dec_ref(v_handlers_2383_);
v___x_2417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2402_);
lean_ctor_set(v___x_2417_, 1, v___x_2382_);
v___x_2418_ = lean_array_push(v___x_2416_, v___x_2417_);
v___x_2419_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2400_);
lean_inc(v_quotContext_2399_);
v___x_2421_ = l_Lean_addMacroScope(v_quotContext_2399_, v___x_2420_, v_currMacroScope_2400_);
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2423_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2402_);
lean_ctor_set(v___x_2423_, 1, v___x_2419_);
lean_ctor_set(v___x_2423_, 2, v___x_2421_);
lean_ctor_set(v___x_2423_, 3, v___x_2422_);
v___x_2424_ = lean_array_push(v___x_2418_, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2402_);
lean_ctor_set(v___x_2425_, 1, v___x_2408_);
lean_ctor_set(v___x_2425_, 2, v___x_2424_);
v___x_2426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2402_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = l_Lean_Syntax_node3(v___x_2402_, v___x_2412_, v___x_2414_, v___x_2425_, v___x_2427_);
v___x_2429_ = l_Lean_Syntax_node2(v___x_2402_, v___x_2410_, v___x_2411_, v___x_2428_);
v___x_2430_ = l_Lean_Syntax_node1(v___x_2402_, v___x_2408_, v___x_2429_);
v___x_2431_ = l_Lean_Syntax_node1(v___x_2402_, v___x_2407_, v___x_2430_);
v___x_2432_ = l_Lean_Syntax_node1(v___x_2402_, v___x_2406_, v___x_2431_);
v___x_2433_ = l_Lean_Syntax_node2(v___x_2402_, v___x_2403_, v___x_2405_, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
case 2:
{
lean_object* v_ref_2435_; lean_object* v_quotContext_2436_; lean_object* v_currMacroScope_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_ref_2435_ = lean_ctor_get(v_a_2379_, 5);
v_quotContext_2436_ = lean_ctor_get(v_a_2379_, 10);
v_currMacroScope_2437_ = lean_ctor_get(v_a_2379_, 11);
v___x_2438_ = 0;
v___x_2439_ = l_Lean_SourceInfo_fromRef(v_ref_2435_, v___x_2438_);
v___x_2440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2439_, 12);
v___x_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2439_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2439_);
lean_ctor_set(v___x_2448_, 1, v___x_2446_);
v___x_2449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2439_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2453_ = l_Array_append___redArg(v___x_2452_, v_handlers_2383_);
lean_dec_ref(v_handlers_2383_);
v___x_2454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2439_);
lean_ctor_set(v___x_2454_, 1, v___x_2382_);
v___x_2455_ = lean_array_push(v___x_2453_, v___x_2454_);
v___x_2456_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
lean_inc(v_currMacroScope_2437_);
lean_inc(v_quotContext_2436_);
v___x_2458_ = l_Lean_addMacroScope(v_quotContext_2436_, v___x_2457_, v_currMacroScope_2437_);
v___x_2459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
v___x_2460_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2439_);
lean_ctor_set(v___x_2460_, 1, v___x_2456_);
lean_ctor_set(v___x_2460_, 2, v___x_2458_);
lean_ctor_set(v___x_2460_, 3, v___x_2459_);
v___x_2461_ = lean_array_push(v___x_2455_, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2439_);
lean_ctor_set(v___x_2462_, 1, v___x_2445_);
lean_ctor_set(v___x_2462_, 2, v___x_2461_);
v___x_2463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2439_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l_Lean_Syntax_node3(v___x_2439_, v___x_2449_, v___x_2451_, v___x_2462_, v___x_2464_);
v___x_2466_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2447_, v___x_2448_, v___x_2465_);
v___x_2467_ = l_Lean_Syntax_node1(v___x_2439_, v___x_2445_, v___x_2466_);
v___x_2468_ = l_Lean_Syntax_node1(v___x_2439_, v___x_2444_, v___x_2467_);
v___x_2469_ = l_Lean_Syntax_node1(v___x_2439_, v___x_2443_, v___x_2468_);
v___x_2470_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2440_, v___x_2442_, v___x_2469_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
default: 
{
lean_object* v_e_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_e_2472_ = lean_ctor_get(v_default_2376_, 0);
lean_inc_ref(v_e_2472_);
lean_dec_ref_known(v_default_2376_, 1);
v___x_2473_ = lean_box(1);
v___x_2474_ = l_Lean_PrettyPrinter_delab(v_e_2472_, v___x_2473_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2511_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2511_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2511_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_ref_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v_ref_2479_ = lean_ctor_get(v_a_2379_, 5);
v___x_2480_ = 0;
v___x_2481_ = l_Lean_SourceInfo_fromRef(v_ref_2479_, v___x_2480_);
v___x_2482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2481_, 11);
v___x_2484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2481_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2481_);
lean_ctor_set(v___x_2490_, 1, v___x_2488_);
v___x_2491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2481_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2495_ = l_Array_append___redArg(v___x_2494_, v_handlers_2383_);
lean_dec_ref(v_handlers_2383_);
v___x_2496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2481_);
lean_ctor_set(v___x_2496_, 1, v___x_2382_);
v___x_2497_ = lean_array_push(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_array_push(v___x_2497_, v_a_2475_);
v___x_2499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2481_);
lean_ctor_set(v___x_2499_, 1, v___x_2487_);
lean_ctor_set(v___x_2499_, 2, v___x_2498_);
v___x_2500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2481_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_Syntax_node3(v___x_2481_, v___x_2491_, v___x_2493_, v___x_2499_, v___x_2501_);
v___x_2503_ = l_Lean_Syntax_node2(v___x_2481_, v___x_2489_, v___x_2490_, v___x_2502_);
v___x_2504_ = l_Lean_Syntax_node1(v___x_2481_, v___x_2487_, v___x_2503_);
v___x_2505_ = l_Lean_Syntax_node1(v___x_2481_, v___x_2486_, v___x_2504_);
v___x_2506_ = l_Lean_Syntax_node1(v___x_2481_, v___x_2485_, v___x_2505_);
v___x_2507_ = l_Lean_Syntax_node2(v___x_2481_, v___x_2482_, v___x_2484_, v___x_2506_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2507_);
v___x_2509_ = v___x_2477_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
else
{
lean_dec_ref(v_handlers_2383_);
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2512_, lean_object* v_default_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2512_, v_default_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec_ref(v_handlers_2512_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2520_, lean_object* v___y_2521_){
_start:
{
uint8_t v___x_2523_; uint8_t v___x_2524_; 
v___x_2523_ = l_Lean_Expr_hasMVar(v_e_2520_);
v___x_2524_ = lean_bool_not(v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; lean_object* v_mctx_2526_; lean_object* v___x_2527_; lean_object* v_fst_2528_; lean_object* v_snd_2529_; lean_object* v___x_2530_; lean_object* v_cache_2531_; lean_object* v_zetaDeltaFVarIds_2532_; lean_object* v_postponed_2533_; lean_object* v_diag_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2543_; 
v___x_2525_ = lean_st_ref_get(v___y_2521_);
v_mctx_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc_ref(v_mctx_2526_);
lean_dec(v___x_2525_);
v___x_2527_ = l_Lean_instantiateMVarsCore(v_mctx_2526_, v_e_2520_);
v_fst_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_fst_2528_);
v_snd_2529_ = lean_ctor_get(v___x_2527_, 1);
lean_inc(v_snd_2529_);
lean_dec_ref(v___x_2527_);
v___x_2530_ = lean_st_ref_take(v___y_2521_);
v_cache_2531_ = lean_ctor_get(v___x_2530_, 1);
v_zetaDeltaFVarIds_2532_ = lean_ctor_get(v___x_2530_, 2);
v_postponed_2533_ = lean_ctor_get(v___x_2530_, 3);
v_diag_2534_ = lean_ctor_get(v___x_2530_, 4);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2530_, 0);
lean_dec(v_unused_2544_);
v___x_2536_ = v___x_2530_;
v_isShared_2537_ = v_isSharedCheck_2543_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_diag_2534_);
lean_inc(v_postponed_2533_);
lean_inc(v_zetaDeltaFVarIds_2532_);
lean_inc(v_cache_2531_);
lean_dec(v___x_2530_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2543_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v_snd_2529_);
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_snd_2529_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_cache_2531_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_zetaDeltaFVarIds_2532_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_postponed_2533_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v_diag_2534_);
v___x_2539_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_st_ref_set(v___y_2521_, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_fst_2528_);
return v___x_2541_;
}
}
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_e_2520_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2546_, v___y_2547_);
lean_dec(v___y_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2550_, v___y_2556_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
v___x_2582_ = lean_apply_9(v_x_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, lean_box(0));
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2594_, lean_object* v_x_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___f_2605_; lean_object* v___x_2606_; 
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v___y_2597_);
lean_inc_ref(v___y_2596_);
v___f_2605_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2605_, 0, v_x_2595_);
lean_closure_set(v___f_2605_, 1, v___y_2596_);
lean_closure_set(v___f_2605_, 2, v___y_2597_);
lean_closure_set(v___f_2605_, 3, v___y_2598_);
lean_closure_set(v___f_2605_, 4, v___y_2599_);
v___x_2606_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2594_, v___f_2605_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
if (lean_obj_tag(v___x_2606_) == 0)
{
return v___x_2606_;
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2615_, lean_object* v_x_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2615_, v_x_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2627_, lean_object* v_mvarId_2628_, lean_object* v_x_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2628_, v_x_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_mvarId_2641_, lean_object* v_x_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2640_, v_mvarId_2641_, v_x_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2653_, lean_object* v_inv_2654_, lean_object* v_xs_2655_, uint8_t v___x_2656_, lean_object* v___x_2657_, lean_object* v_letMuts_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
lean_inc_ref(v_letMuts_2658_);
lean_inc_ref(v_xs_2655_);
v___x_2668_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2653_, v_inv_2654_, v_xs_2655_, v_letMuts_2658_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2745_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2745_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2745_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
if (lean_obj_tag(v_a_2669_) == 1)
{
lean_object* v_val_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2740_; 
lean_del_object(v___x_2671_);
v_val_2673_ = lean_ctor_get(v_a_2669_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_a_2669_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2675_ = v_a_2669_;
v_isShared_2676_ = v_isSharedCheck_2740_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_val_2673_);
lean_dec(v_a_2669_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2740_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_snd_2677_; lean_object* v_fst_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2739_; 
v_snd_2677_ = lean_ctor_get(v_val_2673_, 1);
v_fst_2678_ = lean_ctor_get(v_val_2673_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_val_2673_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2680_ = v_val_2673_;
v_isShared_2681_ = v_isSharedCheck_2739_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_snd_2677_);
lean_inc(v_fst_2678_);
lean_dec(v_val_2673_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2739_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_fst_2682_; lean_object* v_snd_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2738_; 
v_fst_2682_ = lean_ctor_get(v_snd_2677_, 0);
v_snd_2683_ = lean_ctor_get(v_snd_2677_, 1);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_snd_2677_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2685_ = v_snd_2677_;
v_isShared_2686_ = v_isSharedCheck_2738_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_snd_2683_);
lean_inc(v_fst_2682_);
lean_dec(v_snd_2677_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2738_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_lvl_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; 
v_lvl_2687_ = lean_ctor_get(v_fst_2678_, 0);
lean_inc(v_lvl_2687_);
v___x_2688_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2678_);
lean_inc(v_fst_2682_);
v___x_2689_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2682_);
v___x_2690_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2687_, v___x_2688_, v___x_2689_);
v___x_2691_ = lean_unsigned_to_nat(2u);
v___x_2692_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2693_ = lean_array_push(v___x_2692_, v_xs_2655_);
lean_inc_ref(v_letMuts_2658_);
v___x_2694_ = lean_array_push(v___x_2693_, v_letMuts_2658_);
v___x_2695_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2690_);
v___x_2696_ = 0;
v___x_2697_ = 1;
v___x_2698_ = l_Lean_Meta_mkLambdaFVars(v___x_2694_, v___x_2695_, v___x_2696_, v___x_2656_, v___x_2696_, v___x_2656_, v___x_2697_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec_ref(v___x_2694_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v_letMutsPred_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v_letMutsPred_2700_ = lean_ctor_get(v_fst_2682_, 2);
lean_inc_ref(v_letMutsPred_2700_);
lean_dec(v_fst_2682_);
v___x_2701_ = lean_mk_empty_array_with_capacity(v___x_2657_);
v___x_2702_ = lean_array_push(v___x_2701_, v_letMuts_2658_);
v___x_2703_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2700_);
v___x_2704_ = l_Lean_Meta_mkLambdaFVars(v___x_2702_, v___x_2703_, v___x_2696_, v___x_2656_, v___x_2696_, v___x_2656_, v___x_2697_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec_ref(v___x_2702_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2721_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2721_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2721_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v_a_2705_);
v___x_2710_ = v___x_2685_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2705_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_snd_2683_);
v___x_2710_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2712_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 1, v___x_2710_);
lean_ctor_set(v___x_2680_, 0, v_a_2699_);
v___x_2712_ = v___x_2680_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2699_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2714_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2712_);
v___x_2714_ = v___x_2675_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2716_; 
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2714_);
v___x_2716_ = v___x_2707_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v_a_2699_);
lean_del_object(v___x_2685_);
lean_dec(v_snd_2683_);
lean_del_object(v___x_2680_);
lean_del_object(v___x_2675_);
v_a_2722_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2704_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2704_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_del_object(v___x_2685_);
lean_dec(v_snd_2683_);
lean_dec(v_fst_2682_);
lean_del_object(v___x_2680_);
lean_del_object(v___x_2675_);
lean_dec_ref(v_letMuts_2658_);
v_a_2730_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2698_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2698_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_dec(v_a_2669_);
lean_dec_ref(v_letMuts_2658_);
lean_dec_ref(v_xs_2655_);
v___x_2741_ = lean_box(0);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2741_);
v___x_2743_ = v___x_2671_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref(v_letMuts_2658_);
lean_dec_ref(v_xs_2655_);
v_a_2746_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2668_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2668_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2754_, lean_object* v_inv_2755_, lean_object* v_xs_2756_, lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v_letMuts_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
uint8_t v___x_91938__boxed_2769_; lean_object* v_res_2770_; 
v___x_91938__boxed_2769_ = lean_unbox(v___x_2757_);
v_res_2770_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2754_, v_inv_2755_, v_xs_2756_, v___x_91938__boxed_2769_, v___x_2758_, v_letMuts_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___x_2758_);
lean_dec_ref(v_a_2754_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v_b_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v___x_2782_; 
lean_inc(v___y_2780_);
lean_inc_ref(v___y_2779_);
lean_inc(v___y_2778_);
lean_inc_ref(v___y_2777_);
lean_inc(v___y_2775_);
lean_inc_ref(v___y_2774_);
lean_inc(v___y_2773_);
lean_inc_ref(v___y_2772_);
v___x_2782_ = lean_apply_10(v_k_2771_, v_b_2776_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, lean_box(0));
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v_b_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2795_, uint8_t v_bi_2796_, lean_object* v_type_2797_, lean_object* v_k_2798_, uint8_t v_kind_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___f_2809_; lean_object* v___x_2810_; 
lean_inc(v___y_2803_);
lean_inc_ref(v___y_2802_);
lean_inc(v___y_2801_);
lean_inc_ref(v___y_2800_);
v___f_2809_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2809_, 0, v_k_2798_);
lean_closure_set(v___f_2809_, 1, v___y_2800_);
lean_closure_set(v___f_2809_, 2, v___y_2801_);
lean_closure_set(v___f_2809_, 3, v___y_2802_);
lean_closure_set(v___f_2809_, 4, v___y_2803_);
v___x_2810_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2795_, v_bi_2796_, v_type_2797_, v___f_2809_, v_kind_2799_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2810_) == 0)
{
return v___x_2810_;
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2819_, lean_object* v_bi_2820_, lean_object* v_type_2821_, lean_object* v_k_2822_, lean_object* v_kind_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
uint8_t v_bi_boxed_2833_; uint8_t v_kind_boxed_2834_; lean_object* v_res_2835_; 
v_bi_boxed_2833_ = lean_unbox(v_bi_2820_);
v_kind_boxed_2834_ = lean_unbox(v_kind_2823_);
v_res_2835_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2819_, v_bi_boxed_2833_, v_type_2821_, v_k_2822_, v_kind_boxed_2834_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2836_, lean_object* v_type_2837_, lean_object* v_k_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
uint8_t v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = 0;
v___x_2849_ = 0;
v___x_2850_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2836_, v___x_2848_, v_type_2837_, v_k_2838_, v___x_2849_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2851_, lean_object* v_type_2852_, lean_object* v_k_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2851_, v_type_2852_, v_k_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2867_, lean_object* v_inv_2868_, uint8_t v___x_2869_, lean_object* v___x_2870_, lean_object* v_arg_2871_, lean_object* v_xs_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; lean_object* v___f_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2882_ = lean_box(v___x_2869_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2883_, 0, v_a_2867_);
lean_closure_set(v___f_2883_, 1, v_inv_2868_);
lean_closure_set(v___f_2883_, 2, v_xs_2872_);
lean_closure_set(v___f_2883_, 3, v___x_2882_);
lean_closure_set(v___f_2883_, 4, v___x_2870_);
v___x_2884_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2885_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2884_, v_arg_2871_, v___f_2883_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2886_, lean_object* v_inv_2887_, lean_object* v___x_2888_, lean_object* v___x_2889_, lean_object* v_arg_2890_, lean_object* v_xs_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
uint8_t v___x_92258__boxed_2901_; lean_object* v_res_2902_; 
v___x_92258__boxed_2901_ = lean_unbox(v___x_2888_);
v_res_2902_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2886_, v_inv_2887_, v___x_92258__boxed_2901_, v___x_2889_, v_arg_2890_, v_xs_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
return v_res_2902_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2906_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
return v___x_2908_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_unsigned_to_nat(32u);
v___x_2910_ = lean_mk_empty_array_with_capacity(v___x_2909_);
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2912_, lean_object* v_r_2913_, uint8_t v___x_2914_, lean_object* v___x_2915_, lean_object* v___x_2916_, lean_object* v_xs_2917_, lean_object* v_fst_2918_, lean_object* v_fst_2919_, lean_object* v_letMuts_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
lean_inc_ref(v_fst_2912_);
v___x_2930_ = l_Lean_Meta_mkNone(v_fst_2912_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_2933_ = lean_unsigned_to_nat(2u);
v___x_2934_ = lean_mk_empty_array_with_capacity(v___x_2933_);
lean_inc_ref(v___x_2934_);
v___x_2935_ = lean_array_push(v___x_2934_, v_a_2931_);
lean_inc_ref(v_letMuts_2920_);
v___x_2936_ = lean_array_push(v___x_2935_, v_letMuts_2920_);
v___x_2937_ = l_Lean_Meta_mkAppM(v___x_2932_, v___x_2936_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2939_ = l_Lean_Meta_mkSome(v_fst_2912_, v_r_2913_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
lean_inc_ref(v___x_2934_);
v___x_2941_ = lean_array_push(v___x_2934_, v_a_2940_);
v___x_2942_ = lean_array_push(v___x_2941_, v_letMuts_2920_);
v___x_2943_ = l_Lean_Meta_mkAppM(v___x_2932_, v___x_2942_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2928_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2928_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2949_ = lean_unsigned_to_nat(100000u);
v___x_2950_ = 0;
v___x_2951_ = 0;
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2953_, 0, v___x_2949_);
lean_ctor_set(v___x_2953_, 1, v___x_2933_);
lean_ctor_set(v___x_2953_, 2, v___x_2952_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 1, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 2, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 3, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 4, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 5, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 6, v___x_2951_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 7, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 8, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 9, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 10, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 11, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 12, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 13, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 14, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 15, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 16, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 17, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 18, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 19, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 20, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 21, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 22, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 23, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 24, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 25, v___x_2914_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 26, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 27, v___x_2950_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*3 + 28, v___x_2950_);
v___x_2954_ = lean_mk_empty_array_with_capacity(v___x_2915_);
lean_inc_ref(v___x_2954_);
v___x_2955_ = lean_array_push(v___x_2954_, v_a_2946_);
v___x_2956_ = l_Lean_Options_empty;
v___x_2957_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2953_, v___x_2955_, v_a_2948_, v___x_2956_, v___y_2925_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2959_ = lean_mk_empty_array_with_capacity(v___x_2916_);
v___x_2960_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2961_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2959_, v___x_2960_, v___x_2950_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc_n(v_a_2962_, 2);
lean_dec_ref_known(v___x_2961_, 1);
v___x_2963_ = lean_array_push(v___x_2934_, v_xs_2917_);
v___x_2964_ = lean_array_push(v___x_2963_, v_a_2938_);
v___x_2965_ = l_Lean_Expr_beta(v_fst_2918_, v___x_2964_);
v___x_2966_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2916_, 2);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v___x_2916_);
v___x_2968_ = lean_unsigned_to_nat(32u);
v___x_2969_ = lean_mk_empty_array_with_capacity(v___x_2968_);
v___x_2970_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2971_ = ((size_t)5ULL);
v___x_2972_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2969_);
lean_ctor_set(v___x_2972_, 2, v___x_2916_);
lean_ctor_set(v___x_2972_, 3, v___x_2916_);
lean_ctor_set_usize(v___x_2972_, 4, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2966_);
lean_ctor_set(v___x_2973_, 1, v___x_2966_);
lean_ctor_set(v___x_2973_, 2, v___x_2966_);
lean_ctor_set(v___x_2973_, 3, v___x_2972_);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2967_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
lean_inc(v_a_2958_);
v___x_2975_ = l_Lean_Meta_simp(v___x_2965_, v_a_2958_, v_a_2962_, v___x_2952_, v___x_2974_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v_fst_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2975_, 1);
v_fst_2977_ = lean_ctor_get(v_a_2976_, 0);
lean_inc(v_fst_2977_);
lean_dec(v_a_2976_);
v___x_2978_ = lean_array_push(v___x_2954_, v_a_2944_);
v___x_2979_ = l_Lean_Expr_beta(v_fst_2919_, v___x_2978_);
v___x_2980_ = l_Lean_Meta_simp(v___x_2979_, v_a_2958_, v_a_2962_, v___x_2952_, v___x_2974_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec_ref_known(v___x_2974_, 2);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v_fst_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3019_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v_fst_2982_ = lean_ctor_get(v_a_2981_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_a_2981_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v_a_2981_, 1);
lean_dec(v_unused_3020_);
v___x_2984_ = v_a_2981_;
v_isShared_2985_ = v_isSharedCheck_3019_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_fst_2982_);
lean_dec(v_a_2981_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3019_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v_expr_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_expr_2986_ = lean_ctor_get(v_fst_2977_, 0);
lean_inc_ref(v_expr_2986_);
lean_dec(v_fst_2977_);
v___x_2987_ = lean_box(1);
v___x_2988_ = l_Lean_PrettyPrinter_delab(v_expr_2986_, v___x_2987_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v_expr_2990_; lean_object* v___x_2991_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v_expr_2990_ = lean_ctor_get(v_fst_2982_, 0);
lean_inc_ref(v_expr_2990_);
lean_dec(v_fst_2982_);
v___x_2991_ = l_Lean_PrettyPrinter_delab(v_expr_2990_, v___x_2987_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3002_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_3002_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3002_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v_a_2992_);
lean_ctor_set(v___x_2984_, 0, v_a_2989_);
v___x_2997_ = v___x_2984_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2989_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2999_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_2997_);
v___x_2999_ = v___x_2994_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2989_);
lean_del_object(v___x_2984_);
v_a_3003_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2991_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2991_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_del_object(v___x_2984_);
lean_dec(v_fst_2982_);
v_a_3011_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2988_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2988_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v_fst_2977_);
v_a_3021_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2980_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2980_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref_known(v___x_2974_, 2);
lean_dec(v_a_2962_);
lean_dec(v_a_2958_);
lean_dec_ref(v___x_2954_);
lean_dec(v_a_2944_);
lean_dec_ref(v_fst_2919_);
v_a_3029_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2975_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_2975_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_a_2958_);
lean_dec_ref(v___x_2954_);
lean_dec(v_a_2944_);
lean_dec(v_a_2938_);
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_fst_2919_);
lean_dec_ref(v_fst_2918_);
lean_dec_ref(v_xs_2917_);
lean_dec(v___x_2916_);
v_a_3037_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_2961_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_2961_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec_ref(v___x_2954_);
lean_dec(v_a_2944_);
lean_dec(v_a_2938_);
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_fst_2919_);
lean_dec_ref(v_fst_2918_);
lean_dec_ref(v_xs_2917_);
lean_dec(v___x_2916_);
v_a_3045_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2957_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2957_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v_a_2946_);
lean_dec(v_a_2944_);
lean_dec(v_a_2938_);
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_fst_2919_);
lean_dec_ref(v_fst_2918_);
lean_dec_ref(v_xs_2917_);
lean_dec(v___x_2916_);
v_a_3053_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2947_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2947_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_a_2944_);
lean_dec(v_a_2938_);
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_fst_2919_);
lean_dec_ref(v_fst_2918_);
lean_dec_ref(v_xs_2917_);
lean_dec(v___x_2916_);
v_a_3061_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_2945_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_2945_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_a_2938_);
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_fst_2919_);
lean_dec_ref(v_fst_2918_);
lean_dec_ref(v_xs_2917_);
lean_dec(v___x_2916_);
v_a_3069_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_2943_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_2943_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v_a_2938_);
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_letMuts_2920_);
lean_dec_ref(v_fst_2919_);
lean_dec_ref(v_fst_2918_);
lean_dec_ref(v_xs_2917_);
lean_dec(v___x_2916_);
v_a_3077_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_2939_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_2939_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_letMuts_2920_);
lean_dec_ref(v_fst_2919_);
lean_dec_ref(v_fst_2918_);
lean_dec_ref(v_xs_2917_);
lean_dec(v___x_2916_);
lean_dec_ref(v_r_2913_);
lean_dec_ref(v_fst_2912_);
v_a_3085_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_2937_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_2937_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec_ref(v_letMuts_2920_);
lean_dec_ref(v_fst_2919_);
lean_dec_ref(v_fst_2918_);
lean_dec_ref(v_xs_2917_);
lean_dec(v___x_2916_);
lean_dec_ref(v_r_2913_);
lean_dec_ref(v_fst_2912_);
v_a_3093_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_2930_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_2930_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3101_ = _args[0];
lean_object* v_r_3102_ = _args[1];
lean_object* v___x_3103_ = _args[2];
lean_object* v___x_3104_ = _args[3];
lean_object* v___x_3105_ = _args[4];
lean_object* v_xs_3106_ = _args[5];
lean_object* v_fst_3107_ = _args[6];
lean_object* v_fst_3108_ = _args[7];
lean_object* v_letMuts_3109_ = _args[8];
lean_object* v___y_3110_ = _args[9];
lean_object* v___y_3111_ = _args[10];
lean_object* v___y_3112_ = _args[11];
lean_object* v___y_3113_ = _args[12];
lean_object* v___y_3114_ = _args[13];
lean_object* v___y_3115_ = _args[14];
lean_object* v___y_3116_ = _args[15];
lean_object* v___y_3117_ = _args[16];
lean_object* v___y_3118_ = _args[17];
_start:
{
uint8_t v___x_92331__boxed_3119_; lean_object* v_res_3120_; 
v___x_92331__boxed_3119_ = lean_unbox(v___x_3103_);
v_res_3120_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3101_, v_r_3102_, v___x_92331__boxed_3119_, v___x_3104_, v___x_3105_, v_xs_3106_, v_fst_3107_, v_fst_3108_, v_letMuts_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___x_3104_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3121_, uint8_t v___x_3122_, lean_object* v___x_3123_, lean_object* v___x_3124_, lean_object* v_xs_3125_, lean_object* v_fst_3126_, lean_object* v_fst_3127_, lean_object* v_snd_3128_, lean_object* v_r_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; lean_object* v___f_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3139_ = lean_box(v___x_3122_);
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3140_, 0, v_fst_3121_);
lean_closure_set(v___f_3140_, 1, v_r_3129_);
lean_closure_set(v___f_3140_, 2, v___x_3139_);
lean_closure_set(v___f_3140_, 3, v___x_3123_);
lean_closure_set(v___f_3140_, 4, v___x_3124_);
lean_closure_set(v___f_3140_, 5, v_xs_3125_);
lean_closure_set(v___f_3140_, 6, v_fst_3126_);
lean_closure_set(v___f_3140_, 7, v_fst_3127_);
v___x_3141_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3142_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3141_, v_snd_3128_, v___f_3140_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3143_ = _args[0];
lean_object* v___x_3144_ = _args[1];
lean_object* v___x_3145_ = _args[2];
lean_object* v___x_3146_ = _args[3];
lean_object* v_xs_3147_ = _args[4];
lean_object* v_fst_3148_ = _args[5];
lean_object* v_fst_3149_ = _args[6];
lean_object* v_snd_3150_ = _args[7];
lean_object* v_r_3151_ = _args[8];
lean_object* v___y_3152_ = _args[9];
lean_object* v___y_3153_ = _args[10];
lean_object* v___y_3154_ = _args[11];
lean_object* v___y_3155_ = _args[12];
lean_object* v___y_3156_ = _args[13];
lean_object* v___y_3157_ = _args[14];
lean_object* v___y_3158_ = _args[15];
lean_object* v___y_3159_ = _args[16];
lean_object* v___y_3160_ = _args[17];
_start:
{
uint8_t v___x_92727__boxed_3161_; lean_object* v_res_3162_; 
v___x_92727__boxed_3161_ = lean_unbox(v___x_3144_);
v_res_3162_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3143_, v___x_92727__boxed_3161_, v___x_3145_, v___x_3146_, v_xs_3147_, v_fst_3148_, v_fst_3149_, v_snd_3150_, v_r_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3166_, uint8_t v___x_3167_, lean_object* v___x_3168_, lean_object* v___x_3169_, lean_object* v_fst_3170_, lean_object* v_fst_3171_, lean_object* v_snd_3172_, lean_object* v_xs_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3183_ = lean_box(v___x_3167_);
lean_inc_ref(v_fst_3166_);
v___f_3184_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3184_, 0, v_fst_3166_);
lean_closure_set(v___f_3184_, 1, v___x_3183_);
lean_closure_set(v___f_3184_, 2, v___x_3168_);
lean_closure_set(v___f_3184_, 3, v___x_3169_);
lean_closure_set(v___f_3184_, 4, v_xs_3173_);
lean_closure_set(v___f_3184_, 5, v_fst_3170_);
lean_closure_set(v___f_3184_, 6, v_fst_3171_);
lean_closure_set(v___f_3184_, 7, v_snd_3172_);
v___x_3185_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3186_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3185_, v_fst_3166_, v___f_3184_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3187_ = _args[0];
lean_object* v___x_3188_ = _args[1];
lean_object* v___x_3189_ = _args[2];
lean_object* v___x_3190_ = _args[3];
lean_object* v_fst_3191_ = _args[4];
lean_object* v_fst_3192_ = _args[5];
lean_object* v_snd_3193_ = _args[6];
lean_object* v_xs_3194_ = _args[7];
lean_object* v___y_3195_ = _args[8];
lean_object* v___y_3196_ = _args[9];
lean_object* v___y_3197_ = _args[10];
lean_object* v___y_3198_ = _args[11];
lean_object* v___y_3199_ = _args[12];
lean_object* v___y_3200_ = _args[13];
lean_object* v___y_3201_ = _args[14];
lean_object* v___y_3202_ = _args[15];
lean_object* v___y_3203_ = _args[16];
_start:
{
uint8_t v___x_92790__boxed_3204_; lean_object* v_res_3205_; 
v___x_92790__boxed_3204_ = lean_unbox(v___x_3188_);
v_res_3205_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3187_, v___x_92790__boxed_3204_, v___x_3189_, v___x_3190_, v_fst_3191_, v_fst_3192_, v_snd_3193_, v_xs_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3206_, size_t v_sz_3207_, size_t v_i_3208_, lean_object* v_b_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
uint8_t v___x_3215_; 
v___x_3215_ = lean_usize_dec_lt(v_i_3208_, v_sz_3207_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v_b_3209_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; lean_object* v_a_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_box(1);
v_a_3218_ = lean_array_uget_borrowed(v_as_3206_, v_i_3208_);
lean_inc(v_a_3218_);
v___x_3219_ = l_Lean_PrettyPrinter_delab(v_a_3218_, v___x_3217_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3221_; size_t v___x_3222_; size_t v___x_3223_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3221_ = lean_array_push(v_b_3209_, v_a_3220_);
v___x_3222_ = ((size_t)1ULL);
v___x_3223_ = lean_usize_add(v_i_3208_, v___x_3222_);
v_i_3208_ = v___x_3223_;
v_b_3209_ = v___x_3221_;
goto _start;
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref(v_b_3209_);
v_a_3225_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3219_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3219_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3233_, lean_object* v_sz_3234_, lean_object* v_i_3235_, lean_object* v_b_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
size_t v_sz_boxed_3242_; size_t v_i_boxed_3243_; lean_object* v_res_3244_; 
v_sz_boxed_3242_ = lean_unbox_usize(v_sz_3234_);
lean_dec(v_sz_3234_);
v_i_boxed_3243_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_res_3244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3233_, v_sz_boxed_3242_, v_i_boxed_3243_, v_b_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v_as_3233_);
return v_res_3244_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__11(void){
_start:
{
uint8_t v___x_3265_; uint8_t v___x_3266_; 
v___x_3265_ = 0;
v___x_3266_ = lean_bool_not(v___x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3267_, lean_object* v_fst_3268_, lean_object* v_snd_3269_, lean_object* v___x_3270_, lean_object* v___x_3271_, lean_object* v___x_3272_, lean_object* v___x_3273_, lean_object* v___x_3274_, lean_object* v___x_3275_, lean_object* v___x_3276_, uint8_t v___x_3277_, lean_object* v___x_3278_, lean_object* v_letMuts_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3289_ = lean_unsigned_to_nat(2u);
v___x_3290_ = lean_mk_empty_array_with_capacity(v___x_3289_);
v___x_3291_ = lean_array_push(v___x_3290_, v_xs_3267_);
v___x_3292_ = lean_array_push(v___x_3291_, v_letMuts_3279_);
v___x_3293_ = l_Lean_Expr_beta(v_fst_3268_, v___x_3292_);
v___x_3294_ = lean_box(1);
v___x_3295_ = l_Lean_PrettyPrinter_delab(v___x_3293_, v___x_3294_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3435_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3435_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3435_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
uint8_t v___y_3301_; lean_object* v_points_3337_; lean_object* v_default_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3434_; 
v_points_3337_ = lean_ctor_get(v_snd_3269_, 0);
v_default_3338_ = lean_ctor_get(v_snd_3269_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_snd_3269_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3340_ = v_snd_3269_;
v_isShared_3341_ = v_isSharedCheck_3434_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_default_3338_);
lean_inc(v_points_3337_);
lean_dec(v_snd_3269_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3434_;
goto v_resetjp_3339_;
}
v___jp_3300_:
{
lean_object* v_ref_3302_; lean_object* v_quotContext_3303_; lean_object* v_currMacroScope_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
v_ref_3302_ = lean_ctor_get(v___y_3286_, 5);
v_quotContext_3303_ = lean_ctor_get(v___y_3286_, 10);
v_currMacroScope_3304_ = lean_ctor_get(v___y_3286_, 11);
v___x_3305_ = l_Lean_SourceInfo_fromRef(v_ref_3302_, v___y_3301_);
v___x_3306_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3307_ = l_Lean_Name_mkStr3(v___x_3270_, v___x_3271_, v___x_3306_);
v___x_3308_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3309_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3305_, 11);
v___x_3310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3305_);
lean_ctor_set(v___x_3310_, 1, v___x_3308_);
lean_ctor_set(v___x_3310_, 2, v___x_3309_);
v___x_3311_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3305_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3305_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = l_String_toRawSubstring_x27(v___x_3272_);
lean_inc_n(v_currMacroScope_3304_, 2);
lean_inc_n(v_quotContext_3303_, 2);
v___x_3318_ = l_Lean_addMacroScope(v_quotContext_3303_, v___x_3273_, v_currMacroScope_3304_);
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3305_);
lean_ctor_set(v___x_3320_, 1, v___x_3317_);
lean_ctor_set(v___x_3320_, 2, v___x_3318_);
lean_ctor_set(v___x_3320_, 3, v___x_3319_);
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3305_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = l_String_toRawSubstring_x27(v___x_3274_);
v___x_3324_ = l_Lean_addMacroScope(v_quotContext_3303_, v___x_3275_, v_currMacroScope_3304_);
v___x_3325_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3305_);
lean_ctor_set(v___x_3325_, 1, v___x_3323_);
lean_ctor_set(v___x_3325_, 2, v___x_3324_);
lean_ctor_set(v___x_3325_, 3, v___x_3319_);
v___x_3326_ = l_Lean_Syntax_node3(v___x_3305_, v___x_3313_, v___x_3320_, v___x_3322_, v___x_3325_);
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3305_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = l_Lean_Syntax_node3(v___x_3305_, v___x_3314_, v___x_3316_, v___x_3326_, v___x_3328_);
v___x_3330_ = l_Lean_Syntax_node1(v___x_3305_, v___x_3313_, v___x_3329_);
v___x_3331_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3305_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_Syntax_node5(v___x_3305_, v___x_3307_, v___x_3310_, v___x_3312_, v___x_3330_, v___x_3332_, v_a_3296_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v___x_3333_);
v___x_3335_ = v___x_3298_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
v_resetjp_3339_:
{
uint8_t v___y_3343_; lean_object* v___x_3430_; uint8_t v___x_3431_; 
v___x_3430_ = lean_array_get_size(v_points_3337_);
v___x_3431_ = lean_nat_dec_eq(v___x_3430_, v___x_3278_);
if (v___x_3431_ == 0)
{
v___y_3343_ = v___x_3431_;
goto v___jp_3342_;
}
else
{
if (lean_obj_tag(v_default_3338_) == 3)
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_bool_not(v___x_3431_);
v___y_3343_ = v___x_3432_;
goto v___jp_3342_;
}
else
{
uint8_t v___x_3433_; 
v___x_3433_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__11, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__11_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__11);
v___y_3343_ = v___x_3433_;
goto v___jp_3342_;
}
}
v___jp_3342_:
{
if (v___y_3343_ == 0)
{
lean_object* v_ref_3344_; lean_object* v_quotContext_3345_; lean_object* v_currMacroScope_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
lean_del_object(v___x_3298_);
lean_dec_ref(v___x_3271_);
lean_dec_ref(v___x_3270_);
v_ref_3344_ = lean_ctor_get(v___y_3286_, 5);
v_quotContext_3345_ = lean_ctor_get(v___y_3286_, 10);
v_currMacroScope_3346_ = lean_ctor_get(v___y_3286_, 11);
v___x_3347_ = l_Lean_SourceInfo_fromRef(v_ref_3344_, v___y_3343_);
v___x_3348_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3349_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3347_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 2);
lean_ctor_set(v___x_3340_, 1, v___x_3348_);
lean_ctor_set(v___x_3340_, 0, v___x_3347_);
v___x_3351_ = v___x_3340_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v___x_3348_);
v___x_3351_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; size_t v_sz_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v___x_3352_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3347_, 11);
v___x_3356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3347_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = l_String_toRawSubstring_x27(v___x_3272_);
lean_inc_n(v_currMacroScope_3346_, 2);
lean_inc_n(v_quotContext_3345_, 2);
v___x_3358_ = l_Lean_addMacroScope(v_quotContext_3345_, v___x_3273_, v_currMacroScope_3346_);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3347_);
lean_ctor_set(v___x_3360_, 1, v___x_3357_);
lean_ctor_set(v___x_3360_, 2, v___x_3358_);
lean_ctor_set(v___x_3360_, 3, v___x_3359_);
v___x_3361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3347_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = l_String_toRawSubstring_x27(v___x_3274_);
v___x_3364_ = l_Lean_addMacroScope(v_quotContext_3345_, v___x_3275_, v_currMacroScope_3346_);
v___x_3365_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3347_);
lean_ctor_set(v___x_3365_, 1, v___x_3363_);
lean_ctor_set(v___x_3365_, 2, v___x_3364_);
lean_ctor_set(v___x_3365_, 3, v___x_3359_);
v___x_3366_ = l_Lean_Syntax_node3(v___x_3347_, v___x_3353_, v___x_3360_, v___x_3362_, v___x_3365_);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3347_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = l_Lean_Syntax_node3(v___x_3347_, v___x_3354_, v___x_3356_, v___x_3366_, v___x_3368_);
v___x_3370_ = l_Lean_Syntax_node1(v___x_3347_, v___x_3353_, v___x_3369_);
v___x_3371_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3347_);
lean_ctor_set(v___x_3372_, 1, v___x_3353_);
lean_ctor_set(v___x_3372_, 2, v___x_3371_);
v___x_3373_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3347_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Lean_Syntax_node4(v___x_3347_, v___x_3352_, v___x_3370_, v___x_3372_, v___x_3374_, v_a_3296_);
v___x_3376_ = l_Lean_Syntax_node2(v___x_3347_, v___x_3349_, v___x_3351_, v___x_3375_);
v___x_3377_ = lean_mk_empty_array_with_capacity(v___x_3276_);
v___x_3378_ = lean_array_push(v___x_3377_, v___x_3376_);
v_sz_3379_ = lean_array_size(v_points_3337_);
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3337_, v_sz_3379_, v___x_3380_, v___x_3378_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec_ref(v_points_3337_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
v___x_3383_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3382_, v_default_3338_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v_a_3382_);
return v___x_3383_;
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec(v_default_3338_);
v_a_3384_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3381_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3381_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
else
{
lean_dec_ref(v_points_3337_);
if (lean_obj_tag(v_default_3338_) == 2)
{
if (v___x_3277_ == 0)
{
lean_del_object(v___x_3340_);
v___y_3301_ = v___x_3277_;
goto v___jp_3300_;
}
else
{
lean_object* v_ref_3393_; lean_object* v_quotContext_3394_; lean_object* v_currMacroScope_3395_; uint8_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
lean_del_object(v___x_3298_);
v_ref_3393_ = lean_ctor_get(v___y_3286_, 5);
v_quotContext_3394_ = lean_ctor_get(v___y_3286_, 10);
v_currMacroScope_3395_ = lean_ctor_get(v___y_3286_, 11);
v___x_3396_ = 0;
v___x_3397_ = l_Lean_SourceInfo_fromRef(v_ref_3393_, v___x_3396_);
v___x_3398_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3399_ = l_Lean_Name_mkStr3(v___x_3270_, v___x_3271_, v___x_3398_);
v___x_3400_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3401_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3397_, 2);
v___x_3402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3397_);
lean_ctor_set(v___x_3402_, 1, v___x_3400_);
lean_ctor_set(v___x_3402_, 2, v___x_3401_);
v___x_3403_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 2);
lean_ctor_set(v___x_3340_, 1, v___x_3403_);
lean_ctor_set(v___x_3340_, 0, v___x_3397_);
v___x_3405_ = v___x_3340_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3397_, 9);
v___x_3409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3397_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = l_String_toRawSubstring_x27(v___x_3272_);
lean_inc_n(v_currMacroScope_3395_, 2);
lean_inc_n(v_quotContext_3394_, 2);
v___x_3411_ = l_Lean_addMacroScope(v_quotContext_3394_, v___x_3273_, v_currMacroScope_3395_);
v___x_3412_ = lean_box(0);
v___x_3413_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3397_);
lean_ctor_set(v___x_3413_, 1, v___x_3410_);
lean_ctor_set(v___x_3413_, 2, v___x_3411_);
lean_ctor_set(v___x_3413_, 3, v___x_3412_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3397_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = l_String_toRawSubstring_x27(v___x_3274_);
v___x_3417_ = l_Lean_addMacroScope(v_quotContext_3394_, v___x_3275_, v_currMacroScope_3395_);
v___x_3418_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3397_);
lean_ctor_set(v___x_3418_, 1, v___x_3416_);
lean_ctor_set(v___x_3418_, 2, v___x_3417_);
lean_ctor_set(v___x_3418_, 3, v___x_3412_);
v___x_3419_ = l_Lean_Syntax_node3(v___x_3397_, v___x_3406_, v___x_3413_, v___x_3415_, v___x_3418_);
v___x_3420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3397_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = l_Lean_Syntax_node3(v___x_3397_, v___x_3407_, v___x_3409_, v___x_3419_, v___x_3421_);
v___x_3423_ = l_Lean_Syntax_node1(v___x_3397_, v___x_3406_, v___x_3422_);
v___x_3424_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3397_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_Syntax_node5(v___x_3397_, v___x_3399_, v___x_3402_, v___x_3405_, v___x_3423_, v___x_3425_, v_a_3296_);
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
return v___x_3427_;
}
}
}
else
{
uint8_t v___x_3429_; 
lean_del_object(v___x_3340_);
lean_dec(v_default_3338_);
v___x_3429_ = 0;
v___y_3301_ = v___x_3429_;
goto v___jp_3300_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3275_);
lean_dec_ref(v___x_3274_);
lean_dec(v___x_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v___x_3271_);
lean_dec_ref(v___x_3270_);
lean_dec_ref(v_snd_3269_);
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3436_ = _args[0];
lean_object* v_fst_3437_ = _args[1];
lean_object* v_snd_3438_ = _args[2];
lean_object* v___x_3439_ = _args[3];
lean_object* v___x_3440_ = _args[4];
lean_object* v___x_3441_ = _args[5];
lean_object* v___x_3442_ = _args[6];
lean_object* v___x_3443_ = _args[7];
lean_object* v___x_3444_ = _args[8];
lean_object* v___x_3445_ = _args[9];
lean_object* v___x_3446_ = _args[10];
lean_object* v___x_3447_ = _args[11];
lean_object* v_letMuts_3448_ = _args[12];
lean_object* v___y_3449_ = _args[13];
lean_object* v___y_3450_ = _args[14];
lean_object* v___y_3451_ = _args[15];
lean_object* v___y_3452_ = _args[16];
lean_object* v___y_3453_ = _args[17];
lean_object* v___y_3454_ = _args[18];
lean_object* v___y_3455_ = _args[19];
lean_object* v___y_3456_ = _args[20];
lean_object* v___y_3457_ = _args[21];
_start:
{
uint8_t v___x_93003__boxed_3458_; lean_object* v_res_3459_; 
v___x_93003__boxed_3458_ = lean_unbox(v___x_3446_);
v_res_3459_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3436_, v_fst_3437_, v_snd_3438_, v___x_3439_, v___x_3440_, v___x_3441_, v___x_3442_, v___x_3443_, v___x_3444_, v___x_3445_, v___x_93003__boxed_3458_, v___x_3447_, v_letMuts_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___x_3447_);
lean_dec(v___x_3445_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3460_, lean_object* v_snd_3461_, lean_object* v___x_3462_, lean_object* v___x_3463_, lean_object* v___x_3464_, lean_object* v___x_3465_, lean_object* v___x_3466_, uint8_t v___x_3467_, lean_object* v___x_3468_, lean_object* v_arg_3469_, lean_object* v_xs_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; lean_object* v___x_3484_; 
v___x_3480_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3481_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3482_ = lean_box(v___x_3467_);
v___f_3483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3483_, 0, v_xs_3470_);
lean_closure_set(v___f_3483_, 1, v_fst_3460_);
lean_closure_set(v___f_3483_, 2, v_snd_3461_);
lean_closure_set(v___f_3483_, 3, v___x_3462_);
lean_closure_set(v___f_3483_, 4, v___x_3463_);
lean_closure_set(v___f_3483_, 5, v___x_3464_);
lean_closure_set(v___f_3483_, 6, v___x_3465_);
lean_closure_set(v___f_3483_, 7, v___x_3480_);
lean_closure_set(v___f_3483_, 8, v___x_3481_);
lean_closure_set(v___f_3483_, 9, v___x_3466_);
lean_closure_set(v___f_3483_, 10, v___x_3482_);
lean_closure_set(v___f_3483_, 11, v___x_3468_);
v___x_3484_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3481_, v_arg_3469_, v___f_3483_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3485_ = _args[0];
lean_object* v_snd_3486_ = _args[1];
lean_object* v___x_3487_ = _args[2];
lean_object* v___x_3488_ = _args[3];
lean_object* v___x_3489_ = _args[4];
lean_object* v___x_3490_ = _args[5];
lean_object* v___x_3491_ = _args[6];
lean_object* v___x_3492_ = _args[7];
lean_object* v___x_3493_ = _args[8];
lean_object* v_arg_3494_ = _args[9];
lean_object* v_xs_3495_ = _args[10];
lean_object* v___y_3496_ = _args[11];
lean_object* v___y_3497_ = _args[12];
lean_object* v___y_3498_ = _args[13];
lean_object* v___y_3499_ = _args[14];
lean_object* v___y_3500_ = _args[15];
lean_object* v___y_3501_ = _args[16];
lean_object* v___y_3502_ = _args[17];
lean_object* v___y_3503_ = _args[18];
lean_object* v___y_3504_ = _args[19];
_start:
{
uint8_t v___x_93358__boxed_3505_; lean_object* v_res_3506_; 
v___x_93358__boxed_3505_ = lean_unbox(v___x_3492_);
v_res_3506_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3485_, v_snd_3486_, v___x_3487_, v___x_3488_, v___x_3489_, v___x_3490_, v___x_3491_, v___x_93358__boxed_3505_, v___x_3493_, v_arg_3494_, v_xs_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3507_, size_t v_sz_3508_, size_t v_i_3509_, lean_object* v_b_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_lt(v_i_3509_, v_sz_3508_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_b_3510_);
return v___x_3517_;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3518_ = lean_array_uget_borrowed(v_as_3507_, v_i_3509_);
v___x_3519_ = lean_box(1);
lean_inc(v_a_3518_);
v___x_3520_ = l_Lean_PrettyPrinter_delab(v_a_3518_, v___x_3519_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; size_t v___x_3523_; size_t v___x_3524_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v___x_3522_ = lean_array_push(v_b_3510_, v_a_3521_);
v___x_3523_ = ((size_t)1ULL);
v___x_3524_ = lean_usize_add(v_i_3509_, v___x_3523_);
v_i_3509_ = v___x_3524_;
v_b_3510_ = v___x_3522_;
goto _start;
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v_b_3510_);
v_a_3526_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3520_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3520_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3534_, lean_object* v_sz_3535_, lean_object* v_i_3536_, lean_object* v_b_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
size_t v_sz_boxed_3543_; size_t v_i_boxed_3544_; lean_object* v_res_3545_; 
v_sz_boxed_3543_ = lean_unbox_usize(v_sz_3535_);
lean_dec(v_sz_3535_);
v_i_boxed_3544_ = lean_unbox_usize(v_i_3536_);
lean_dec(v_i_3536_);
v_res_3545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3534_, v_sz_boxed_3543_, v_i_boxed_3544_, v_b_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec_ref(v_as_3534_);
return v_res_3545_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3554_ = l_String_toRawSubstring_x27(v___x_3553_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3565_ = l_String_toRawSubstring_x27(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3570_ = l_String_toRawSubstring_x27(v___x_3569_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3572_ = l_String_toRawSubstring_x27(v___x_3571_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3576_ = l_String_toRawSubstring_x27(v___x_3575_);
return v___x_3576_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3581_ = l_String_toRawSubstring_x27(v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3591_, lean_object* v___x_3592_, lean_object* v___f_3593_, lean_object* v_a_3594_, lean_object* v_inv_3595_, lean_object* v_arg_3596_, uint8_t v___x_3597_, lean_object* v___x_3598_, lean_object* v___x_3599_, lean_object* v___x_3600_, lean_object* v___x_3601_, lean_object* v___x_3602_, lean_object* v___x_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_a_3614_; lean_object* v___y_3618_; lean_object* v___x_3620_; 
lean_inc_ref(v___x_3592_);
lean_inc(v___x_3591_);
v___x_3620_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3591_, v___x_3592_, v___f_3593_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3622_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3594_, v_inv_3595_, v_arg_3596_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
if (lean_obj_tag(v_a_3623_) == 1)
{
lean_object* v_val_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_4104_; 
lean_dec_ref(v_arg_3596_);
v_val_3624_ = lean_ctor_get(v_a_3623_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_a_3623_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_3626_ = v_a_3623_;
v_isShared_3627_ = v_isSharedCheck_4104_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_val_3624_);
lean_dec(v_a_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_4104_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
if (lean_obj_tag(v_a_3621_) == 1)
{
lean_object* v_val_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_4027_; 
lean_del_object(v___x_3626_);
v_val_3628_ = lean_ctor_get(v_a_3621_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_a_3621_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_3630_ = v_a_3621_;
v_isShared_3631_ = v_isSharedCheck_4027_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_val_3628_);
lean_dec(v_a_3621_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_4027_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_snd_3632_; lean_object* v_fst_3633_; lean_object* v_snd_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_4026_; 
v_snd_3632_ = lean_ctor_get(v_val_3628_, 1);
lean_inc(v_snd_3632_);
v_fst_3633_ = lean_ctor_get(v_val_3624_, 0);
v_snd_3634_ = lean_ctor_get(v_val_3624_, 1);
v_isSharedCheck_4026_ = !lean_is_exclusive(v_val_3624_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_3636_ = v_val_3624_;
v_isShared_3637_ = v_isSharedCheck_4026_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_snd_3634_);
lean_inc(v_fst_3633_);
lean_dec(v_val_3624_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_4026_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v_fst_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_4024_; 
v_fst_3638_ = lean_ctor_get(v_val_3628_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v_val_3628_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; 
v_unused_4025_ = lean_ctor_get(v_val_3628_, 1);
lean_dec(v_unused_4025_);
v___x_3640_ = v_val_3628_;
v_isShared_3641_ = v_isSharedCheck_4024_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_fst_3638_);
lean_dec(v_val_3628_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_4024_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_fst_3642_; lean_object* v_snd_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_4023_; 
v_fst_3642_ = lean_ctor_get(v_snd_3632_, 0);
v_snd_3643_ = lean_ctor_get(v_snd_3632_, 1);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_snd_3632_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_3645_ = v_snd_3632_;
v_isShared_3646_ = v_isSharedCheck_4023_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_snd_3643_);
lean_inc(v_fst_3642_);
lean_dec(v_snd_3632_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_4023_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___f_3648_; lean_object* v___x_3649_; 
v___x_3647_ = lean_box(v___x_3597_);
lean_inc(v___x_3599_);
v___f_3648_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3648_, 0, v_fst_3633_);
lean_closure_set(v___f_3648_, 1, v___x_3647_);
lean_closure_set(v___f_3648_, 2, v___x_3598_);
lean_closure_set(v___f_3648_, 3, v___x_3599_);
lean_closure_set(v___f_3648_, 4, v_fst_3638_);
lean_closure_set(v___f_3648_, 5, v_fst_3642_);
lean_closure_set(v___f_3648_, 6, v_snd_3634_);
lean_inc(v___x_3591_);
v___x_3649_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3591_, v___x_3592_, v___f_3648_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v_fst_3651_; lean_object* v_snd_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_4014_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v_fst_3651_ = lean_ctor_get(v_a_3650_, 0);
v_snd_3652_ = lean_ctor_get(v_a_3650_, 1);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3654_ = v_a_3650_;
v_isShared_3655_ = v_isSharedCheck_4014_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_snd_3652_);
lean_inc(v_fst_3651_);
lean_dec(v_a_3650_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_4014_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v_points_3656_; lean_object* v_default_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_4013_; 
v_points_3656_ = lean_ctor_get(v_snd_3643_, 0);
v_default_3657_ = lean_ctor_get(v_snd_3643_, 1);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_snd_3643_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3659_ = v_snd_3643_;
v_isShared_3660_ = v_isSharedCheck_4013_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_default_3657_);
lean_inc(v_points_3656_);
lean_dec(v_snd_3643_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_4013_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = lean_array_get_size(v_points_3656_);
v___x_3662_ = lean_nat_dec_eq(v___x_3661_, v___x_3599_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; size_t v_sz_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
lean_del_object(v___x_3630_);
v___x_3663_ = lean_mk_empty_array_with_capacity(v___x_3599_);
lean_dec(v___x_3599_);
v_sz_3664_ = lean_array_size(v_points_3656_);
v___x_3665_ = ((size_t)0ULL);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3656_, v_sz_3664_, v___x_3665_, v___x_3663_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec_ref(v_points_3656_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3668_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3667_, v_default_3657_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec(v_a_3667_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3751_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3751_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3751_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v_ref_3673_; lean_object* v_quotContext_3674_; lean_object* v_currMacroScope_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v_ref_3673_ = lean_ctor_get(v___y_3610_, 5);
lean_inc(v_ref_3673_);
v_quotContext_3674_ = lean_ctor_get(v___y_3610_, 10);
lean_inc_n(v_quotContext_3674_, 2);
v_currMacroScope_3675_ = lean_ctor_get(v___y_3610_, 11);
lean_inc_n(v_currMacroScope_3675_, 2);
lean_dec_ref(v___y_3610_);
v___x_3676_ = l_Lean_SourceInfo_fromRef(v_ref_3673_, v___x_3662_);
lean_dec(v_ref_3673_);
v___x_3677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3678_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3679_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3600_);
v___x_3680_ = l_Lean_Name_mkStr2(v___x_3600_, v___x_3679_);
v___x_3681_ = l_Lean_addMacroScope(v_quotContext_3674_, v___x_3680_, v_currMacroScope_3675_);
v___x_3682_ = l_Lean_Name_mkStr4(v___x_3601_, v___x_3602_, v___x_3600_, v___x_3679_);
v___x_3683_ = lean_box(0);
lean_inc(v___x_3682_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 1);
lean_ctor_set(v___x_3659_, 1, v___x_3683_);
lean_ctor_set(v___x_3659_, 0, v___x_3682_);
v___x_3685_ = v___x_3659_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3687_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3682_);
v___x_3687_ = v___x_3671_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3682_);
v___x_3687_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3689_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 1);
lean_ctor_set(v___x_3654_, 1, v___x_3683_);
lean_ctor_set(v___x_3654_, 0, v___x_3687_);
v___x_3689_ = v___x_3654_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3683_);
v___x_3689_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3691_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3689_);
lean_ctor_set(v___x_3645_, 0, v___x_3685_);
v___x_3691_ = v___x_3645_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3697_; 
lean_inc_n(v___x_3676_, 2);
v___x_3692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3676_);
lean_ctor_set(v___x_3692_, 1, v___x_3678_);
lean_ctor_set(v___x_3692_, 2, v___x_3681_);
lean_ctor_set(v___x_3692_, 3, v___x_3691_);
v___x_3693_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3694_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3695_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 2);
lean_ctor_set(v___x_3640_, 1, v___x_3695_);
lean_ctor_set(v___x_3640_, 0, v___x_3676_);
v___x_3697_ = v___x_3640_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v___x_3695_);
v___x_3697_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3698_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3675_);
lean_inc(v_quotContext_3674_);
v___x_3700_ = l_Lean_addMacroScope(v_quotContext_3674_, v___x_3699_, v_currMacroScope_3675_);
lean_inc_n(v___x_3676_, 2);
v___x_3701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3676_);
lean_ctor_set(v___x_3701_, 1, v___x_3698_);
lean_ctor_set(v___x_3701_, 2, v___x_3700_);
lean_ctor_set(v___x_3701_, 3, v___x_3683_);
v___x_3702_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 2);
lean_ctor_set(v___x_3636_, 1, v___x_3702_);
lean_ctor_set(v___x_3636_, 0, v___x_3676_);
v___x_3704_ = v___x_3636_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3705_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3706_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3676_, 19);
v___x_3707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3676_);
lean_ctor_set(v___x_3707_, 1, v___x_3705_);
v___x_3708_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3709_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3710_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3675_, 4);
lean_inc_n(v_quotContext_3674_, 4);
v___x_3711_ = l_Lean_addMacroScope(v_quotContext_3674_, v___x_3710_, v_currMacroScope_3675_);
v___x_3712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3676_);
lean_ctor_set(v___x_3712_, 1, v___x_3709_);
lean_ctor_set(v___x_3712_, 2, v___x_3711_);
lean_ctor_set(v___x_3712_, 3, v___x_3683_);
v___x_3713_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3714_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3715_ = l_Lean_addMacroScope(v_quotContext_3674_, v___x_3714_, v_currMacroScope_3675_);
v___x_3716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3676_);
lean_ctor_set(v___x_3716_, 1, v___x_3713_);
lean_ctor_set(v___x_3716_, 2, v___x_3715_);
lean_ctor_set(v___x_3716_, 3, v___x_3683_);
lean_inc_ref(v___x_3716_);
v___x_3717_ = l_Lean_Syntax_node2(v___x_3676_, v___x_3693_, v___x_3712_, v___x_3716_);
v___x_3718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3676_);
lean_ctor_set(v___x_3719_, 1, v___x_3693_);
lean_ctor_set(v___x_3719_, 2, v___x_3718_);
v___x_3720_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3676_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
lean_inc_ref(v___x_3721_);
lean_inc_ref(v___x_3719_);
v___x_3722_ = l_Lean_Syntax_node4(v___x_3676_, v___x_3708_, v___x_3717_, v___x_3719_, v___x_3721_, v_snd_3652_);
lean_inc_ref(v___x_3707_);
v___x_3723_ = l_Lean_Syntax_node2(v___x_3676_, v___x_3706_, v___x_3707_, v___x_3722_);
v___x_3724_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3676_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
lean_inc_ref_n(v___x_3725_, 2);
lean_inc_ref_n(v___x_3704_, 2);
lean_inc_ref_n(v___x_3697_, 2);
v___x_3726_ = l_Lean_Syntax_node5(v___x_3676_, v___x_3694_, v___x_3697_, v___x_3701_, v___x_3704_, v___x_3723_, v___x_3725_);
v___x_3727_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3728_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3729_ = l_Lean_addMacroScope(v_quotContext_3674_, v___x_3728_, v_currMacroScope_3675_);
v___x_3730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3676_);
lean_ctor_set(v___x_3730_, 1, v___x_3727_);
lean_ctor_set(v___x_3730_, 2, v___x_3729_);
lean_ctor_set(v___x_3730_, 3, v___x_3683_);
v___x_3731_ = l_String_toRawSubstring_x27(v___x_3603_);
v___x_3732_ = l_Lean_addMacroScope(v_quotContext_3674_, v___x_3591_, v_currMacroScope_3675_);
v___x_3733_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3676_);
lean_ctor_set(v___x_3733_, 1, v___x_3731_);
lean_ctor_set(v___x_3733_, 2, v___x_3732_);
lean_ctor_set(v___x_3733_, 3, v___x_3683_);
v___x_3734_ = l_Lean_Syntax_node2(v___x_3676_, v___x_3693_, v___x_3733_, v___x_3716_);
v___x_3735_ = l_Lean_Syntax_node4(v___x_3676_, v___x_3708_, v___x_3734_, v___x_3719_, v___x_3721_, v_fst_3651_);
v___x_3736_ = l_Lean_Syntax_node2(v___x_3676_, v___x_3706_, v___x_3707_, v___x_3735_);
v___x_3737_ = l_Lean_Syntax_node5(v___x_3676_, v___x_3694_, v___x_3697_, v___x_3730_, v___x_3704_, v___x_3736_, v___x_3725_);
v___x_3738_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3739_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3740_ = l_Lean_addMacroScope(v_quotContext_3674_, v___x_3739_, v_currMacroScope_3675_);
v___x_3741_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3676_);
lean_ctor_set(v___x_3741_, 1, v___x_3738_);
lean_ctor_set(v___x_3741_, 2, v___x_3740_);
lean_ctor_set(v___x_3741_, 3, v___x_3683_);
v___x_3742_ = l_Lean_Syntax_node5(v___x_3676_, v___x_3694_, v___x_3697_, v___x_3741_, v___x_3704_, v_a_3669_, v___x_3725_);
v___x_3743_ = l_Lean_Syntax_node3(v___x_3676_, v___x_3693_, v___x_3726_, v___x_3737_, v___x_3742_);
v___x_3744_ = l_Lean_Syntax_node2(v___x_3676_, v___x_3677_, v___x_3692_, v___x_3743_);
v_a_3614_ = v___x_3744_;
goto v___jp_3613_;
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
lean_del_object(v___x_3659_);
lean_del_object(v___x_3654_);
lean_dec(v_snd_3652_);
lean_dec(v_fst_3651_);
lean_del_object(v___x_3645_);
lean_del_object(v___x_3640_);
lean_del_object(v___x_3636_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___x_3603_);
lean_dec_ref(v___x_3602_);
lean_dec_ref(v___x_3601_);
lean_dec_ref(v___x_3600_);
lean_dec(v___x_3591_);
v___y_3618_ = v___x_3668_;
goto v___jp_3617_;
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_del_object(v___x_3659_);
lean_dec(v_default_3657_);
lean_del_object(v___x_3654_);
lean_dec(v_snd_3652_);
lean_dec(v_fst_3651_);
lean_del_object(v___x_3645_);
lean_del_object(v___x_3640_);
lean_del_object(v___x_3636_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___x_3603_);
lean_dec_ref(v___x_3602_);
lean_dec_ref(v___x_3601_);
lean_dec_ref(v___x_3600_);
lean_dec(v___x_3591_);
v_a_3752_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3666_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3666_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
else
{
lean_dec_ref(v_points_3656_);
lean_dec(v___x_3599_);
switch(lean_obj_tag(v_default_3657_))
{
case 2:
{
lean_object* v_ref_3760_; lean_object* v_quotContext_3761_; lean_object* v_currMacroScope_3762_; uint8_t v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
v_ref_3760_ = lean_ctor_get(v___y_3610_, 5);
lean_inc(v_ref_3760_);
v_quotContext_3761_ = lean_ctor_get(v___y_3610_, 10);
lean_inc_n(v_quotContext_3761_, 2);
v_currMacroScope_3762_ = lean_ctor_get(v___y_3610_, 11);
lean_inc_n(v_currMacroScope_3762_, 2);
lean_dec_ref(v___y_3610_);
v___x_3763_ = 0;
v___x_3764_ = l_Lean_SourceInfo_fromRef(v_ref_3760_, v___x_3763_);
lean_dec(v_ref_3760_);
v___x_3765_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3766_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3600_);
v___x_3768_ = l_Lean_Name_mkStr2(v___x_3600_, v___x_3767_);
v___x_3769_ = l_Lean_addMacroScope(v_quotContext_3761_, v___x_3768_, v_currMacroScope_3762_);
lean_inc_ref(v___x_3602_);
lean_inc_ref(v___x_3601_);
v___x_3770_ = l_Lean_Name_mkStr4(v___x_3601_, v___x_3602_, v___x_3600_, v___x_3767_);
v___x_3771_ = lean_box(0);
lean_inc(v___x_3770_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 1);
lean_ctor_set(v___x_3659_, 1, v___x_3771_);
lean_ctor_set(v___x_3659_, 0, v___x_3770_);
v___x_3773_ = v___x_3659_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3770_);
v___x_3775_ = v___x_3630_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3770_);
v___x_3775_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 1);
lean_ctor_set(v___x_3654_, 1, v___x_3771_);
lean_ctor_set(v___x_3654_, 0, v___x_3775_);
v___x_3777_ = v___x_3654_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3771_);
v___x_3777_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3777_);
lean_ctor_set(v___x_3645_, 0, v___x_3773_);
v___x_3779_ = v___x_3645_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
lean_inc_n(v___x_3764_, 2);
v___x_3780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3764_);
lean_ctor_set(v___x_3780_, 1, v___x_3766_);
lean_ctor_set(v___x_3780_, 2, v___x_3769_);
lean_ctor_set(v___x_3780_, 3, v___x_3779_);
v___x_3781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3782_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3783_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 2);
lean_ctor_set(v___x_3640_, 1, v___x_3783_);
lean_ctor_set(v___x_3640_, 0, v___x_3764_);
v___x_3785_ = v___x_3640_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3786_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3787_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3762_);
lean_inc(v_quotContext_3761_);
v___x_3788_ = l_Lean_addMacroScope(v_quotContext_3761_, v___x_3787_, v_currMacroScope_3762_);
lean_inc_n(v___x_3764_, 2);
v___x_3789_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3764_);
lean_ctor_set(v___x_3789_, 1, v___x_3786_);
lean_ctor_set(v___x_3789_, 2, v___x_3788_);
lean_ctor_set(v___x_3789_, 3, v___x_3771_);
v___x_3790_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 2);
lean_ctor_set(v___x_3636_, 1, v___x_3790_);
lean_ctor_set(v___x_3636_, 0, v___x_3764_);
v___x_3792_ = v___x_3636_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3793_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3794_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3764_, 22);
v___x_3795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3764_);
lean_ctor_set(v___x_3795_, 1, v___x_3793_);
v___x_3796_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3797_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3798_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3762_, 5);
lean_inc_n(v_quotContext_3761_, 5);
v___x_3799_ = l_Lean_addMacroScope(v_quotContext_3761_, v___x_3798_, v_currMacroScope_3762_);
v___x_3800_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3764_);
lean_ctor_set(v___x_3800_, 1, v___x_3797_);
lean_ctor_set(v___x_3800_, 2, v___x_3799_);
lean_ctor_set(v___x_3800_, 3, v___x_3771_);
v___x_3801_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3802_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3803_ = l_Lean_addMacroScope(v_quotContext_3761_, v___x_3802_, v_currMacroScope_3762_);
v___x_3804_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3764_);
lean_ctor_set(v___x_3804_, 1, v___x_3801_);
lean_ctor_set(v___x_3804_, 2, v___x_3803_);
lean_ctor_set(v___x_3804_, 3, v___x_3771_);
lean_inc_ref(v___x_3804_);
v___x_3805_ = l_Lean_Syntax_node2(v___x_3764_, v___x_3781_, v___x_3800_, v___x_3804_);
v___x_3806_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3764_);
lean_ctor_set(v___x_3807_, 1, v___x_3781_);
lean_ctor_set(v___x_3807_, 2, v___x_3806_);
v___x_3808_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3764_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
lean_inc_ref(v___x_3809_);
lean_inc_ref(v___x_3807_);
v___x_3810_ = l_Lean_Syntax_node4(v___x_3764_, v___x_3796_, v___x_3805_, v___x_3807_, v___x_3809_, v_snd_3652_);
lean_inc_ref(v___x_3795_);
v___x_3811_ = l_Lean_Syntax_node2(v___x_3764_, v___x_3794_, v___x_3795_, v___x_3810_);
v___x_3812_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3764_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
lean_inc_ref_n(v___x_3813_, 2);
lean_inc_ref_n(v___x_3792_, 2);
lean_inc_ref_n(v___x_3785_, 2);
v___x_3814_ = l_Lean_Syntax_node5(v___x_3764_, v___x_3782_, v___x_3785_, v___x_3789_, v___x_3792_, v___x_3811_, v___x_3813_);
v___x_3815_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3816_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3817_ = l_Lean_addMacroScope(v_quotContext_3761_, v___x_3816_, v_currMacroScope_3762_);
v___x_3818_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3764_);
lean_ctor_set(v___x_3818_, 1, v___x_3815_);
lean_ctor_set(v___x_3818_, 2, v___x_3817_);
lean_ctor_set(v___x_3818_, 3, v___x_3771_);
v___x_3819_ = l_String_toRawSubstring_x27(v___x_3603_);
v___x_3820_ = l_Lean_addMacroScope(v_quotContext_3761_, v___x_3591_, v_currMacroScope_3762_);
v___x_3821_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3764_);
lean_ctor_set(v___x_3821_, 1, v___x_3819_);
lean_ctor_set(v___x_3821_, 2, v___x_3820_);
lean_ctor_set(v___x_3821_, 3, v___x_3771_);
v___x_3822_ = l_Lean_Syntax_node2(v___x_3764_, v___x_3781_, v___x_3821_, v___x_3804_);
v___x_3823_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3824_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3825_ = l_Lean_addMacroScope(v_quotContext_3761_, v___x_3824_, v_currMacroScope_3762_);
v___x_3826_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3764_);
lean_ctor_set(v___x_3826_, 1, v___x_3823_);
lean_ctor_set(v___x_3826_, 2, v___x_3825_);
lean_ctor_set(v___x_3826_, 3, v___x_3771_);
v___x_3827_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3831_ = l_Lean_addMacroScope(v_quotContext_3761_, v___x_3830_, v_currMacroScope_3762_);
v___x_3832_ = l_Lean_Name_mkStr4(v___x_3601_, v___x_3602_, v___x_3828_, v___x_3829_);
v___x_3833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
lean_ctor_set(v___x_3833_, 1, v___x_3771_);
v___x_3834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
lean_ctor_set(v___x_3834_, 1, v___x_3771_);
v___x_3835_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3764_);
lean_ctor_set(v___x_3835_, 1, v___x_3827_);
lean_ctor_set(v___x_3835_, 2, v___x_3831_);
lean_ctor_set(v___x_3835_, 3, v___x_3834_);
v___x_3836_ = l_Lean_Syntax_node5(v___x_3764_, v___x_3782_, v___x_3785_, v___x_3826_, v___x_3792_, v___x_3835_, v___x_3813_);
v___x_3837_ = l_Lean_Syntax_node1(v___x_3764_, v___x_3781_, v___x_3836_);
v___x_3838_ = l_Lean_Syntax_node2(v___x_3764_, v___x_3765_, v_fst_3651_, v___x_3837_);
v___x_3839_ = l_Lean_Syntax_node4(v___x_3764_, v___x_3796_, v___x_3822_, v___x_3807_, v___x_3809_, v___x_3838_);
v___x_3840_ = l_Lean_Syntax_node2(v___x_3764_, v___x_3794_, v___x_3795_, v___x_3839_);
v___x_3841_ = l_Lean_Syntax_node5(v___x_3764_, v___x_3782_, v___x_3785_, v___x_3818_, v___x_3792_, v___x_3840_, v___x_3813_);
v___x_3842_ = l_Lean_Syntax_node2(v___x_3764_, v___x_3781_, v___x_3814_, v___x_3841_);
v___x_3843_ = l_Lean_Syntax_node2(v___x_3764_, v___x_3765_, v___x_3780_, v___x_3842_);
v_a_3614_ = v___x_3843_;
goto v___jp_3613_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
lean_del_object(v___x_3630_);
v_e_3850_ = lean_ctor_get(v_default_3657_, 0);
lean_inc_ref(v_e_3850_);
lean_dec_ref_known(v_default_3657_, 1);
v___x_3851_ = lean_box(1);
v___x_3852_ = l_Lean_PrettyPrinter_delab(v_e_3850_, v___x_3851_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3938_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3938_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3938_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v_ref_3857_; lean_object* v_quotContext_3858_; lean_object* v_currMacroScope_3859_; uint8_t v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
v_ref_3857_ = lean_ctor_get(v___y_3610_, 5);
lean_inc(v_ref_3857_);
v_quotContext_3858_ = lean_ctor_get(v___y_3610_, 10);
lean_inc_n(v_quotContext_3858_, 2);
v_currMacroScope_3859_ = lean_ctor_get(v___y_3610_, 11);
lean_inc_n(v_currMacroScope_3859_, 2);
lean_dec_ref(v___y_3610_);
v___x_3860_ = 0;
v___x_3861_ = l_Lean_SourceInfo_fromRef(v_ref_3857_, v___x_3860_);
lean_dec(v_ref_3857_);
v___x_3862_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3863_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3864_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3600_);
v___x_3865_ = l_Lean_Name_mkStr2(v___x_3600_, v___x_3864_);
v___x_3866_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3865_, v_currMacroScope_3859_);
v___x_3867_ = l_Lean_Name_mkStr4(v___x_3601_, v___x_3602_, v___x_3600_, v___x_3864_);
v___x_3868_ = lean_box(0);
lean_inc(v___x_3867_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 1);
lean_ctor_set(v___x_3659_, 1, v___x_3868_);
lean_ctor_set(v___x_3659_, 0, v___x_3867_);
v___x_3870_ = v___x_3659_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3872_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3867_);
v___x_3872_ = v___x_3855_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3867_);
v___x_3872_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3874_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 1);
lean_ctor_set(v___x_3654_, 1, v___x_3868_);
lean_ctor_set(v___x_3654_, 0, v___x_3872_);
v___x_3874_ = v___x_3654_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3872_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v___x_3868_);
v___x_3874_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3876_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3874_);
lean_ctor_set(v___x_3645_, 0, v___x_3870_);
v___x_3876_ = v___x_3645_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
lean_inc_n(v___x_3861_, 2);
v___x_3877_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3861_);
lean_ctor_set(v___x_3877_, 1, v___x_3863_);
lean_ctor_set(v___x_3877_, 2, v___x_3866_);
lean_ctor_set(v___x_3877_, 3, v___x_3876_);
v___x_3878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3879_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3880_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 2);
lean_ctor_set(v___x_3640_, 1, v___x_3880_);
lean_ctor_set(v___x_3640_, 0, v___x_3861_);
v___x_3882_ = v___x_3640_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3883_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3884_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3859_);
lean_inc(v_quotContext_3858_);
v___x_3885_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3884_, v_currMacroScope_3859_);
lean_inc_n(v___x_3861_, 2);
v___x_3886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3861_);
lean_ctor_set(v___x_3886_, 1, v___x_3883_);
lean_ctor_set(v___x_3886_, 2, v___x_3885_);
lean_ctor_set(v___x_3886_, 3, v___x_3868_);
v___x_3887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 2);
lean_ctor_set(v___x_3636_, 1, v___x_3887_);
lean_ctor_set(v___x_3636_, 0, v___x_3861_);
v___x_3889_ = v___x_3636_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3890_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3891_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3861_, 21);
v___x_3892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3861_);
lean_ctor_set(v___x_3892_, 1, v___x_3890_);
v___x_3893_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3894_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3895_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3859_, 4);
lean_inc_n(v_quotContext_3858_, 4);
v___x_3896_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3895_, v_currMacroScope_3859_);
v___x_3897_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3861_);
lean_ctor_set(v___x_3897_, 1, v___x_3894_);
lean_ctor_set(v___x_3897_, 2, v___x_3896_);
lean_ctor_set(v___x_3897_, 3, v___x_3868_);
v___x_3898_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3900_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3899_, v_currMacroScope_3859_);
v___x_3901_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3861_);
lean_ctor_set(v___x_3901_, 1, v___x_3898_);
lean_ctor_set(v___x_3901_, 2, v___x_3900_);
lean_ctor_set(v___x_3901_, 3, v___x_3868_);
lean_inc_ref(v___x_3901_);
v___x_3902_ = l_Lean_Syntax_node2(v___x_3861_, v___x_3878_, v___x_3897_, v___x_3901_);
v___x_3903_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3861_);
lean_ctor_set(v___x_3904_, 1, v___x_3878_);
lean_ctor_set(v___x_3904_, 2, v___x_3903_);
v___x_3905_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3861_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
lean_inc_ref(v___x_3906_);
lean_inc_ref(v___x_3904_);
v___x_3907_ = l_Lean_Syntax_node4(v___x_3861_, v___x_3893_, v___x_3902_, v___x_3904_, v___x_3906_, v_snd_3652_);
lean_inc_ref(v___x_3892_);
v___x_3908_ = l_Lean_Syntax_node2(v___x_3861_, v___x_3891_, v___x_3892_, v___x_3907_);
v___x_3909_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3861_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
lean_inc_ref_n(v___x_3910_, 2);
lean_inc_ref_n(v___x_3889_, 2);
lean_inc_ref_n(v___x_3882_, 2);
v___x_3911_ = l_Lean_Syntax_node5(v___x_3861_, v___x_3879_, v___x_3882_, v___x_3886_, v___x_3889_, v___x_3908_, v___x_3910_);
v___x_3912_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3913_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3914_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3913_, v_currMacroScope_3859_);
v___x_3915_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3861_);
lean_ctor_set(v___x_3915_, 1, v___x_3912_);
lean_ctor_set(v___x_3915_, 2, v___x_3914_);
lean_ctor_set(v___x_3915_, 3, v___x_3868_);
v___x_3916_ = l_String_toRawSubstring_x27(v___x_3603_);
v___x_3917_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3591_, v_currMacroScope_3859_);
v___x_3918_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3861_);
lean_ctor_set(v___x_3918_, 1, v___x_3916_);
lean_ctor_set(v___x_3918_, 2, v___x_3917_);
lean_ctor_set(v___x_3918_, 3, v___x_3868_);
v___x_3919_ = l_Lean_Syntax_node2(v___x_3861_, v___x_3878_, v___x_3918_, v___x_3901_);
v___x_3920_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3922_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3921_, v_currMacroScope_3859_);
v___x_3923_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3861_);
lean_ctor_set(v___x_3923_, 1, v___x_3920_);
lean_ctor_set(v___x_3923_, 2, v___x_3922_);
lean_ctor_set(v___x_3923_, 3, v___x_3868_);
v___x_3924_ = l_Lean_Syntax_node5(v___x_3861_, v___x_3879_, v___x_3882_, v___x_3923_, v___x_3889_, v_a_3853_, v___x_3910_);
v___x_3925_ = l_Lean_Syntax_node1(v___x_3861_, v___x_3878_, v___x_3924_);
v___x_3926_ = l_Lean_Syntax_node2(v___x_3861_, v___x_3862_, v_fst_3651_, v___x_3925_);
v___x_3927_ = l_Lean_Syntax_node4(v___x_3861_, v___x_3893_, v___x_3919_, v___x_3904_, v___x_3906_, v___x_3926_);
v___x_3928_ = l_Lean_Syntax_node2(v___x_3861_, v___x_3891_, v___x_3892_, v___x_3927_);
v___x_3929_ = l_Lean_Syntax_node5(v___x_3861_, v___x_3879_, v___x_3882_, v___x_3915_, v___x_3889_, v___x_3928_, v___x_3910_);
v___x_3930_ = l_Lean_Syntax_node2(v___x_3861_, v___x_3878_, v___x_3911_, v___x_3929_);
v___x_3931_ = l_Lean_Syntax_node2(v___x_3861_, v___x_3862_, v___x_3877_, v___x_3930_);
v_a_3614_ = v___x_3931_;
goto v___jp_3613_;
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
lean_del_object(v___x_3659_);
lean_del_object(v___x_3654_);
lean_dec(v_snd_3652_);
lean_dec(v_fst_3651_);
lean_del_object(v___x_3645_);
lean_del_object(v___x_3640_);
lean_del_object(v___x_3636_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___x_3603_);
lean_dec_ref(v___x_3602_);
lean_dec_ref(v___x_3601_);
lean_dec_ref(v___x_3600_);
lean_dec(v___x_3591_);
v___y_3618_ = v___x_3852_;
goto v___jp_3617_;
}
}
default: 
{
lean_object* v_ref_3939_; lean_object* v_quotContext_3940_; lean_object* v_currMacroScope_3941_; uint8_t v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
lean_dec(v_default_3657_);
v_ref_3939_ = lean_ctor_get(v___y_3610_, 5);
lean_inc(v_ref_3939_);
v_quotContext_3940_ = lean_ctor_get(v___y_3610_, 10);
lean_inc_n(v_quotContext_3940_, 2);
v_currMacroScope_3941_ = lean_ctor_get(v___y_3610_, 11);
lean_inc_n(v_currMacroScope_3941_, 2);
lean_dec_ref(v___y_3610_);
v___x_3942_ = 0;
v___x_3943_ = l_Lean_SourceInfo_fromRef(v_ref_3939_, v___x_3942_);
lean_dec(v_ref_3939_);
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3945_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3946_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3600_);
v___x_3947_ = l_Lean_Name_mkStr2(v___x_3600_, v___x_3946_);
v___x_3948_ = l_Lean_addMacroScope(v_quotContext_3940_, v___x_3947_, v_currMacroScope_3941_);
v___x_3949_ = l_Lean_Name_mkStr4(v___x_3601_, v___x_3602_, v___x_3600_, v___x_3946_);
v___x_3950_ = lean_box(0);
lean_inc(v___x_3949_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 1);
lean_ctor_set(v___x_3659_, 1, v___x_3950_);
lean_ctor_set(v___x_3659_, 0, v___x_3949_);
v___x_3952_ = v___x_3659_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_3949_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_4012_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3954_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3949_);
v___x_3954_ = v___x_3630_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_3949_);
v___x_3954_ = v_reuseFailAlloc_4011_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3956_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 1);
lean_ctor_set(v___x_3654_, 1, v___x_3950_);
lean_ctor_set(v___x_3654_, 0, v___x_3954_);
v___x_3956_ = v___x_3654_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v___x_3950_);
v___x_3956_ = v_reuseFailAlloc_4010_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3958_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3956_);
lean_ctor_set(v___x_3645_, 0, v___x_3952_);
v___x_3958_ = v___x_3645_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_4009_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3964_; 
lean_inc_n(v___x_3943_, 2);
v___x_3959_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3943_);
lean_ctor_set(v___x_3959_, 1, v___x_3945_);
lean_ctor_set(v___x_3959_, 2, v___x_3948_);
lean_ctor_set(v___x_3959_, 3, v___x_3958_);
v___x_3960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3962_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 2);
lean_ctor_set(v___x_3640_, 1, v___x_3962_);
lean_ctor_set(v___x_3640_, 0, v___x_3943_);
v___x_3964_ = v___x_3640_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_4008_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3971_; 
v___x_3965_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3941_);
lean_inc(v_quotContext_3940_);
v___x_3967_ = l_Lean_addMacroScope(v_quotContext_3940_, v___x_3966_, v_currMacroScope_3941_);
lean_inc_n(v___x_3943_, 2);
v___x_3968_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3943_);
lean_ctor_set(v___x_3968_, 1, v___x_3965_);
lean_ctor_set(v___x_3968_, 2, v___x_3967_);
lean_ctor_set(v___x_3968_, 3, v___x_3950_);
v___x_3969_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 2);
lean_ctor_set(v___x_3636_, 1, v___x_3969_);
lean_ctor_set(v___x_3636_, 0, v___x_3943_);
v___x_3971_ = v___x_3636_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v___x_3969_);
v___x_3971_ = v_reuseFailAlloc_4007_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_3972_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3973_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3943_, 17);
v___x_3974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3943_);
lean_ctor_set(v___x_3974_, 1, v___x_3972_);
v___x_3975_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3976_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3977_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3941_, 3);
lean_inc_n(v_quotContext_3940_, 3);
v___x_3978_ = l_Lean_addMacroScope(v_quotContext_3940_, v___x_3977_, v_currMacroScope_3941_);
v___x_3979_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3943_);
lean_ctor_set(v___x_3979_, 1, v___x_3976_);
lean_ctor_set(v___x_3979_, 2, v___x_3978_);
lean_ctor_set(v___x_3979_, 3, v___x_3950_);
v___x_3980_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3981_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3982_ = l_Lean_addMacroScope(v_quotContext_3940_, v___x_3981_, v_currMacroScope_3941_);
v___x_3983_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3943_);
lean_ctor_set(v___x_3983_, 1, v___x_3980_);
lean_ctor_set(v___x_3983_, 2, v___x_3982_);
lean_ctor_set(v___x_3983_, 3, v___x_3950_);
lean_inc_ref(v___x_3983_);
v___x_3984_ = l_Lean_Syntax_node2(v___x_3943_, v___x_3960_, v___x_3979_, v___x_3983_);
v___x_3985_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3943_);
lean_ctor_set(v___x_3986_, 1, v___x_3960_);
lean_ctor_set(v___x_3986_, 2, v___x_3985_);
v___x_3987_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3943_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
lean_inc_ref(v___x_3988_);
lean_inc_ref(v___x_3986_);
v___x_3989_ = l_Lean_Syntax_node4(v___x_3943_, v___x_3975_, v___x_3984_, v___x_3986_, v___x_3988_, v_snd_3652_);
lean_inc_ref(v___x_3974_);
v___x_3990_ = l_Lean_Syntax_node2(v___x_3943_, v___x_3973_, v___x_3974_, v___x_3989_);
v___x_3991_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3943_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
lean_inc_ref(v___x_3992_);
lean_inc_ref(v___x_3971_);
lean_inc_ref(v___x_3964_);
v___x_3993_ = l_Lean_Syntax_node5(v___x_3943_, v___x_3961_, v___x_3964_, v___x_3968_, v___x_3971_, v___x_3990_, v___x_3992_);
v___x_3994_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3995_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3996_ = l_Lean_addMacroScope(v_quotContext_3940_, v___x_3995_, v_currMacroScope_3941_);
v___x_3997_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3943_);
lean_ctor_set(v___x_3997_, 1, v___x_3994_);
lean_ctor_set(v___x_3997_, 2, v___x_3996_);
lean_ctor_set(v___x_3997_, 3, v___x_3950_);
v___x_3998_ = l_String_toRawSubstring_x27(v___x_3603_);
v___x_3999_ = l_Lean_addMacroScope(v_quotContext_3940_, v___x_3591_, v_currMacroScope_3941_);
v___x_4000_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3943_);
lean_ctor_set(v___x_4000_, 1, v___x_3998_);
lean_ctor_set(v___x_4000_, 2, v___x_3999_);
lean_ctor_set(v___x_4000_, 3, v___x_3950_);
v___x_4001_ = l_Lean_Syntax_node2(v___x_3943_, v___x_3960_, v___x_4000_, v___x_3983_);
v___x_4002_ = l_Lean_Syntax_node4(v___x_3943_, v___x_3975_, v___x_4001_, v___x_3986_, v___x_3988_, v_fst_3651_);
v___x_4003_ = l_Lean_Syntax_node2(v___x_3943_, v___x_3973_, v___x_3974_, v___x_4002_);
v___x_4004_ = l_Lean_Syntax_node5(v___x_3943_, v___x_3961_, v___x_3964_, v___x_3997_, v___x_3971_, v___x_4003_, v___x_3992_);
v___x_4005_ = l_Lean_Syntax_node2(v___x_3943_, v___x_3960_, v___x_3993_, v___x_4004_);
v___x_4006_ = l_Lean_Syntax_node2(v___x_3943_, v___x_3944_, v___x_3959_, v___x_4005_);
v_a_3614_ = v___x_4006_;
goto v___jp_3613_;
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
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_del_object(v___x_3645_);
lean_dec(v_snd_3643_);
lean_del_object(v___x_3640_);
lean_del_object(v___x_3636_);
lean_del_object(v___x_3630_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___x_3603_);
lean_dec_ref(v___x_3602_);
lean_dec_ref(v___x_3601_);
lean_dec_ref(v___x_3600_);
lean_dec(v___x_3599_);
lean_dec(v___x_3591_);
v_a_4015_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3649_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3649_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
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
lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v_a_3621_);
lean_dec(v___x_3599_);
lean_dec(v___x_3598_);
lean_dec_ref(v___x_3592_);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_val_3624_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; lean_object* v_unused_4103_; 
v_unused_4102_ = lean_ctor_get(v_val_3624_, 1);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_val_3624_, 0);
lean_dec(v_unused_4103_);
v___x_4029_ = v_val_3624_;
v_isShared_4030_ = v_isSharedCheck_4101_;
goto v_resetjp_4028_;
}
else
{
lean_dec(v_val_3624_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4101_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v_ref_4031_; lean_object* v_quotContext_4032_; lean_object* v_currMacroScope_4033_; uint8_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
v_ref_4031_ = lean_ctor_get(v___y_3610_, 5);
lean_inc(v_ref_4031_);
v_quotContext_4032_ = lean_ctor_get(v___y_3610_, 10);
lean_inc_n(v_quotContext_4032_, 2);
v_currMacroScope_4033_ = lean_ctor_get(v___y_3610_, 11);
lean_inc_n(v_currMacroScope_4033_, 2);
lean_dec_ref(v___y_3610_);
v___x_4034_ = 0;
v___x_4035_ = l_Lean_SourceInfo_fromRef(v_ref_4031_, v___x_4034_);
lean_dec(v_ref_4031_);
v___x_4036_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4037_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4038_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3600_);
v___x_4039_ = l_Lean_Name_mkStr2(v___x_3600_, v___x_4038_);
v___x_4040_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4039_, v_currMacroScope_4033_);
v___x_4041_ = l_Lean_Name_mkStr4(v___x_3601_, v___x_3602_, v___x_3600_, v___x_4038_);
v___x_4042_ = lean_box(0);
lean_inc(v___x_4041_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set_tag(v___x_4029_, 1);
lean_ctor_set(v___x_4029_, 1, v___x_4042_);
lean_ctor_set(v___x_4029_, 0, v___x_4041_);
v___x_4044_ = v___x_4029_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4041_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4046_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 0);
lean_ctor_set(v___x_3626_, 0, v___x_4041_);
v___x_4046_ = v___x_3626_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4041_);
v___x_4046_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
lean_ctor_set(v___x_4047_, 1, v___x_4042_);
v___x_4048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4044_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
lean_inc_n(v___x_4035_, 23);
v___x_4049_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4035_);
lean_ctor_set(v___x_4049_, 1, v___x_4037_);
lean_ctor_set(v___x_4049_, 2, v___x_4040_);
lean_ctor_set(v___x_4049_, 3, v___x_4048_);
v___x_4050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4051_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4052_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_4053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4035_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4055_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_4033_, 4);
lean_inc_n(v_quotContext_4032_, 4);
v___x_4056_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4055_, v_currMacroScope_4033_);
v___x_4057_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4035_);
lean_ctor_set(v___x_4057_, 1, v___x_4054_);
lean_ctor_set(v___x_4057_, 2, v___x_4056_);
lean_ctor_set(v___x_4057_, 3, v___x_4042_);
v___x_4058_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_4059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4035_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4061_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
v___x_4062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4035_);
lean_ctor_set(v___x_4062_, 1, v___x_4060_);
v___x_4063_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4064_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4065_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_4066_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4065_, v_currMacroScope_4033_);
v___x_4067_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4035_);
lean_ctor_set(v___x_4067_, 1, v___x_4064_);
lean_ctor_set(v___x_4067_, 2, v___x_4066_);
lean_ctor_set(v___x_4067_, 3, v___x_4042_);
v___x_4068_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4069_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4070_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4069_, v_currMacroScope_4033_);
v___x_4071_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4035_);
lean_ctor_set(v___x_4071_, 1, v___x_4068_);
lean_ctor_set(v___x_4071_, 2, v___x_4070_);
lean_ctor_set(v___x_4071_, 3, v___x_4042_);
lean_inc_ref(v___x_4071_);
v___x_4072_ = l_Lean_Syntax_node2(v___x_4035_, v___x_4050_, v___x_4067_, v___x_4071_);
v___x_4073_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4035_);
lean_ctor_set(v___x_4074_, 1, v___x_4050_);
lean_ctor_set(v___x_4074_, 2, v___x_4073_);
v___x_4075_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4076_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4035_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4035_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = l_Lean_Syntax_node1(v___x_4035_, v___x_4077_, v___x_4079_);
lean_inc(v___x_4080_);
lean_inc_ref(v___x_4076_);
lean_inc_ref(v___x_4074_);
v___x_4081_ = l_Lean_Syntax_node4(v___x_4035_, v___x_4063_, v___x_4072_, v___x_4074_, v___x_4076_, v___x_4080_);
lean_inc_ref(v___x_4062_);
v___x_4082_ = l_Lean_Syntax_node2(v___x_4035_, v___x_4061_, v___x_4062_, v___x_4081_);
v___x_4083_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4035_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
lean_inc_ref(v___x_4084_);
lean_inc_ref(v___x_4059_);
lean_inc_ref(v___x_4053_);
v___x_4085_ = l_Lean_Syntax_node5(v___x_4035_, v___x_4051_, v___x_4053_, v___x_4057_, v___x_4059_, v___x_4082_, v___x_4084_);
v___x_4086_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4087_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4088_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4087_, v_currMacroScope_4033_);
v___x_4089_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4035_);
lean_ctor_set(v___x_4089_, 1, v___x_4086_);
lean_ctor_set(v___x_4089_, 2, v___x_4088_);
lean_ctor_set(v___x_4089_, 3, v___x_4042_);
v___x_4090_ = l_String_toRawSubstring_x27(v___x_3603_);
v___x_4091_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_3591_, v_currMacroScope_4033_);
v___x_4092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4035_);
lean_ctor_set(v___x_4092_, 1, v___x_4090_);
lean_ctor_set(v___x_4092_, 2, v___x_4091_);
lean_ctor_set(v___x_4092_, 3, v___x_4042_);
v___x_4093_ = l_Lean_Syntax_node2(v___x_4035_, v___x_4050_, v___x_4092_, v___x_4071_);
v___x_4094_ = l_Lean_Syntax_node4(v___x_4035_, v___x_4063_, v___x_4093_, v___x_4074_, v___x_4076_, v___x_4080_);
v___x_4095_ = l_Lean_Syntax_node2(v___x_4035_, v___x_4061_, v___x_4062_, v___x_4094_);
v___x_4096_ = l_Lean_Syntax_node5(v___x_4035_, v___x_4051_, v___x_4053_, v___x_4089_, v___x_4059_, v___x_4095_, v___x_4084_);
v___x_4097_ = l_Lean_Syntax_node2(v___x_4035_, v___x_4050_, v___x_4085_, v___x_4096_);
v___x_4098_ = l_Lean_Syntax_node2(v___x_4035_, v___x_4036_, v___x_4049_, v___x_4097_);
v_a_3614_ = v___x_4098_;
goto v___jp_3613_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3623_);
lean_dec_ref(v___x_3600_);
if (lean_obj_tag(v_a_3621_) == 1)
{
lean_object* v_val_4105_; lean_object* v_snd_4106_; lean_object* v_fst_4107_; lean_object* v_snd_4108_; lean_object* v___x_4109_; lean_object* v___f_4110_; lean_object* v___x_4111_; 
v_val_4105_ = lean_ctor_get(v_a_3621_, 0);
lean_inc(v_val_4105_);
lean_dec_ref_known(v_a_3621_, 1);
v_snd_4106_ = lean_ctor_get(v_val_4105_, 1);
lean_inc(v_snd_4106_);
v_fst_4107_ = lean_ctor_get(v_val_4105_, 0);
lean_inc(v_fst_4107_);
lean_dec(v_val_4105_);
v_snd_4108_ = lean_ctor_get(v_snd_4106_, 1);
lean_inc(v_snd_4108_);
lean_dec(v_snd_4106_);
v___x_4109_ = lean_box(v___x_3597_);
lean_inc(v___x_3591_);
v___f_4110_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4110_, 0, v_fst_4107_);
lean_closure_set(v___f_4110_, 1, v_snd_4108_);
lean_closure_set(v___f_4110_, 2, v___x_3601_);
lean_closure_set(v___f_4110_, 3, v___x_3602_);
lean_closure_set(v___f_4110_, 4, v___x_3603_);
lean_closure_set(v___f_4110_, 5, v___x_3591_);
lean_closure_set(v___f_4110_, 6, v___x_3598_);
lean_closure_set(v___f_4110_, 7, v___x_4109_);
lean_closure_set(v___f_4110_, 8, v___x_3599_);
lean_closure_set(v___f_4110_, 9, v_arg_3596_);
v___x_4111_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3591_, v___x_3592_, v___f_4110_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec_ref(v___y_3610_);
v___y_3618_ = v___x_4111_;
goto v___jp_3617_;
}
else
{
lean_object* v_ref_4112_; lean_object* v_quotContext_4113_; lean_object* v_currMacroScope_4114_; uint8_t v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_dec(v_a_3621_);
lean_dec(v___x_3599_);
lean_dec(v___x_3598_);
lean_dec_ref(v_arg_3596_);
lean_dec_ref(v___x_3592_);
v_ref_4112_ = lean_ctor_get(v___y_3610_, 5);
lean_inc(v_ref_4112_);
v_quotContext_4113_ = lean_ctor_get(v___y_3610_, 10);
lean_inc_n(v_quotContext_4113_, 2);
v_currMacroScope_4114_ = lean_ctor_get(v___y_3610_, 11);
lean_inc_n(v_currMacroScope_4114_, 2);
lean_dec_ref(v___y_3610_);
v___x_4115_ = 0;
v___x_4116_ = l_Lean_SourceInfo_fromRef(v_ref_4112_, v___x_4115_);
lean_dec(v_ref_4112_);
v___x_4117_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4118_ = l_Lean_Name_mkStr3(v___x_3601_, v___x_3602_, v___x_4117_);
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4120_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4116_, 13);
v___x_4121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4116_);
lean_ctor_set(v___x_4121_, 1, v___x_4119_);
lean_ctor_set(v___x_4121_, 2, v___x_4120_);
v___x_4122_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_4123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4116_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4116_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = l_String_toRawSubstring_x27(v___x_3603_);
v___x_4129_ = l_Lean_addMacroScope(v_quotContext_4113_, v___x_3591_, v_currMacroScope_4114_);
v___x_4130_ = lean_box(0);
v___x_4131_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4116_);
lean_ctor_set(v___x_4131_, 1, v___x_4128_);
lean_ctor_set(v___x_4131_, 2, v___x_4129_);
lean_ctor_set(v___x_4131_, 3, v___x_4130_);
v___x_4132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4116_);
lean_ctor_set(v___x_4133_, 1, v___x_4132_);
v___x_4134_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4135_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4136_ = l_Lean_addMacroScope(v_quotContext_4113_, v___x_4135_, v_currMacroScope_4114_);
v___x_4137_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4116_);
lean_ctor_set(v___x_4137_, 1, v___x_4134_);
lean_ctor_set(v___x_4137_, 2, v___x_4136_);
lean_ctor_set(v___x_4137_, 3, v___x_4130_);
v___x_4138_ = l_Lean_Syntax_node3(v___x_4116_, v___x_4124_, v___x_4131_, v___x_4133_, v___x_4137_);
v___x_4139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4116_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_Syntax_node3(v___x_4116_, v___x_4125_, v___x_4127_, v___x_4138_, v___x_4140_);
v___x_4142_ = l_Lean_Syntax_node1(v___x_4116_, v___x_4124_, v___x_4141_);
v___x_4143_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4116_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4146_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4116_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = l_Lean_Syntax_node1(v___x_4116_, v___x_4145_, v___x_4147_);
v___x_4149_ = l_Lean_Syntax_node5(v___x_4116_, v___x_4118_, v___x_4121_, v___x_4123_, v___x_4142_, v___x_4144_, v___x_4148_);
v_a_3614_ = v___x_4149_;
goto v___jp_3613_;
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec(v_a_3621_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___x_3603_);
lean_dec_ref(v___x_3602_);
lean_dec_ref(v___x_3601_);
lean_dec_ref(v___x_3600_);
lean_dec(v___x_3599_);
lean_dec(v___x_3598_);
lean_dec_ref(v_arg_3596_);
lean_dec_ref(v___x_3592_);
lean_dec(v___x_3591_);
v_a_4150_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_3622_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_3622_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___x_3603_);
lean_dec_ref(v___x_3602_);
lean_dec_ref(v___x_3601_);
lean_dec_ref(v___x_3600_);
lean_dec(v___x_3599_);
lean_dec(v___x_3598_);
lean_dec_ref(v_arg_3596_);
lean_dec(v_inv_3595_);
lean_dec_ref(v___x_3592_);
lean_dec(v___x_3591_);
v_a_4158_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_3620_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_3620_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
v___jp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3614_);
v___x_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
return v___x_3616_;
}
v___jp_3617_:
{
if (lean_obj_tag(v___y_3618_) == 0)
{
lean_object* v_a_3619_; 
v_a_3619_ = lean_ctor_get(v___y_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___y_3618_, 1);
v_a_3614_ = v_a_3619_;
goto v___jp_3613_;
}
else
{
return v___y_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4166_ = _args[0];
lean_object* v___x_4167_ = _args[1];
lean_object* v___f_4168_ = _args[2];
lean_object* v_a_4169_ = _args[3];
lean_object* v_inv_4170_ = _args[4];
lean_object* v_arg_4171_ = _args[5];
lean_object* v___x_4172_ = _args[6];
lean_object* v___x_4173_ = _args[7];
lean_object* v___x_4174_ = _args[8];
lean_object* v___x_4175_ = _args[9];
lean_object* v___x_4176_ = _args[10];
lean_object* v___x_4177_ = _args[11];
lean_object* v___x_4178_ = _args[12];
lean_object* v___y_4179_ = _args[13];
lean_object* v___y_4180_ = _args[14];
lean_object* v___y_4181_ = _args[15];
lean_object* v___y_4182_ = _args[16];
lean_object* v___y_4183_ = _args[17];
lean_object* v___y_4184_ = _args[18];
lean_object* v___y_4185_ = _args[19];
lean_object* v___y_4186_ = _args[20];
lean_object* v___y_4187_ = _args[21];
_start:
{
uint8_t v___x_93876__boxed_4188_; lean_object* v_res_4189_; 
v___x_93876__boxed_4188_ = lean_unbox(v___x_4172_);
v_res_4189_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4166_, v___x_4167_, v___f_4168_, v_a_4169_, v_inv_4170_, v_arg_4171_, v___x_93876__boxed_4188_, v___x_4173_, v___x_4174_, v___x_4175_, v___x_4176_, v___x_4177_, v___x_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec_ref(v_a_4169_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; lean_object* v_env_4197_; lean_object* v___x_4198_; lean_object* v_mctx_4199_; lean_object* v_lctx_4200_; lean_object* v_options_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4196_ = lean_st_ref_get(v___y_4194_);
v_env_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc_ref(v_env_4197_);
lean_dec(v___x_4196_);
v___x_4198_ = lean_st_ref_get(v___y_4192_);
v_mctx_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc_ref(v_mctx_4199_);
lean_dec(v___x_4198_);
v_lctx_4200_ = lean_ctor_get(v___y_4191_, 2);
v_options_4201_ = lean_ctor_get(v___y_4193_, 2);
lean_inc_ref(v_options_4201_);
lean_inc_ref(v_lctx_4200_);
v___x_4202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4202_, 0, v_env_4197_);
lean_ctor_set(v___x_4202_, 1, v_mctx_4199_);
lean_ctor_set(v___x_4202_, 2, v_lctx_4200_);
lean_ctor_set(v___x_4202_, 3, v_options_4201_);
v___x_4203_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set(v___x_4203_, 1, v_msgData_4190_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_ref_4218_; lean_object* v___x_4219_; lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4228_; 
v_ref_4218_ = lean_ctor_get(v___y_4215_, 5);
v___x_4219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4222_ = v___x_4219_;
v_isShared_4223_ = v_isSharedCheck_4228_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4219_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4228_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4224_; lean_object* v___x_4226_; 
lean_inc(v_ref_4218_);
v___x_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4224_, 0, v_ref_4218_);
lean_ctor_set(v___x_4224_, 1, v_a_4220_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set_tag(v___x_4222_, 1);
lean_ctor_set(v___x_4222_, 0, v___x_4224_);
v___x_4226_ = v___x_4222_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4242_, size_t v_i_4243_, size_t v_stop_4244_, lean_object* v_b_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v_a_4256_; lean_object* v_a_4261_; uint8_t v___x_4263_; 
v___x_4263_ = lean_usize_dec_eq(v_i_4243_, v_stop_4244_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4247_, v___y_4249_, v___y_4251_, v___y_4253_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4266_; lean_object* v___y_4268_; uint8_t v___y_4269_; lean_object* v___y_4284_; lean_object* v_a_4285_; lean_object* v___x_4288_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
v___x_4266_ = lean_array_uget_borrowed(v_as_4242_, v_i_4243_);
lean_inc(v___x_4266_);
v___x_4288_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4266_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v_ref_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v_ref_4290_ = lean_ctor_get(v___y_4252_, 5);
v___x_4291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
v___x_4293_ = l_Lean_SourceInfo_fromRef(v_ref_4290_, v___x_4263_);
lean_inc(v___x_4293_);
v___x_4294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
lean_ctor_set(v___x_4294_, 1, v___x_4291_);
v___x_4295_ = l_Lean_Syntax_node1(v___x_4293_, v___x_4292_, v___x_4294_);
v___x_4296_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4295_, v_a_4289_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; 
lean_dec(v_a_4265_);
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref_known(v___x_4296_, 1);
v___x_4298_ = lean_array_mk(v_a_4297_);
v_a_4261_ = v___x_4298_;
goto v___jp_4260_;
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
v_a_4299_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4296_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4296_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
lean_inc(v_a_4299_);
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
v___y_4284_ = v___x_4304_;
v_a_4285_ = v_a_4299_;
goto v___jp_4283_;
}
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
v_a_4307_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4288_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4288_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
lean_inc(v_a_4307_);
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
v___y_4284_ = v___x_4312_;
v_a_4285_ = v_a_4307_;
goto v___jp_4283_;
}
}
}
v___jp_4267_:
{
if (v___y_4269_ == 0)
{
lean_object* v___x_4270_; 
lean_dec_ref(v___y_4268_);
v___x_4270_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4265_, v___y_4269_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec_ref_known(v___x_4270_, 1);
v___x_4271_ = lean_unsigned_to_nat(1u);
v___x_4272_ = lean_mk_empty_array_with_capacity(v___x_4271_);
lean_inc(v___x_4266_);
v___x_4273_ = lean_array_push(v___x_4272_, v___x_4266_);
v_a_4261_ = v___x_4273_;
goto v___jp_4260_;
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
lean_dec_ref(v_b_4245_);
v_a_4274_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4270_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4270_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
else
{
lean_dec(v_a_4265_);
lean_dec_ref(v_b_4245_);
if (lean_obj_tag(v___y_4268_) == 0)
{
lean_object* v_a_4282_; 
v_a_4282_ = lean_ctor_get(v___y_4268_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___y_4268_, 1);
v_a_4256_ = v_a_4282_;
goto v___jp_4255_;
}
else
{
return v___y_4268_;
}
}
}
v___jp_4283_:
{
uint8_t v___x_4286_; 
v___x_4286_ = l_Lean_Exception_isInterrupt(v_a_4285_);
if (v___x_4286_ == 0)
{
uint8_t v___x_4287_; 
v___x_4287_ = l_Lean_Exception_isRuntime(v_a_4285_);
v___y_4268_ = v___y_4284_;
v___y_4269_ = v___x_4287_;
goto v___jp_4267_;
}
else
{
lean_dec_ref(v_a_4285_);
v___y_4268_ = v___y_4284_;
v___y_4269_ = v___x_4286_;
goto v___jp_4267_;
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec_ref(v_b_4245_);
v_a_4315_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4264_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4264_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
else
{
lean_object* v___x_4323_; 
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v_b_4245_);
return v___x_4323_;
}
v___jp_4255_:
{
size_t v___x_4257_; size_t v___x_4258_; 
v___x_4257_ = ((size_t)1ULL);
v___x_4258_ = lean_usize_add(v_i_4243_, v___x_4257_);
v_i_4243_ = v___x_4258_;
v_b_4245_ = v_a_4256_;
goto _start;
}
v___jp_4260_:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Array_append___redArg(v_b_4245_, v_a_4261_);
lean_dec_ref(v_a_4261_);
v_a_4256_ = v___x_4262_;
goto v___jp_4255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4324_, lean_object* v_i_4325_, lean_object* v_stop_4326_, lean_object* v_b_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
size_t v_i_boxed_4337_; size_t v_stop_boxed_4338_; lean_object* v_res_4339_; 
v_i_boxed_4337_ = lean_unbox_usize(v_i_4325_);
lean_dec(v_i_4325_);
v_stop_boxed_4338_ = lean_unbox_usize(v_stop_4326_);
lean_dec(v_stop_4326_);
v_res_4339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4324_, v_i_boxed_4337_, v_stop_boxed_4338_, v_b_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec_ref(v_as_4324_);
return v_res_4339_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4342_ = l_Lean_stringToMessageData(v___x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4358_, lean_object* v_inv_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; 
lean_inc(v_inv_4359_);
v___x_4369_ = l_Lean_MVarId_getType(v_inv_4359_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4371_; lean_object* v_a_4372_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4369_, 1);
v___x_4371_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4370_, v_a_4365_);
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc_n(v_a_4372_, 2);
lean_dec_ref(v___x_4371_);
v___x_4386_ = l_Lean_Expr_cleanupAnnotations(v_a_4372_);
v___x_4387_ = l_Lean_Expr_isApp(v___x_4386_);
if (v___x_4387_ == 0)
{
lean_dec_ref(v___x_4386_);
lean_dec(v_inv_4359_);
v___y_4374_ = v_a_4360_;
v___y_4375_ = v_a_4361_;
v___y_4376_ = v_a_4362_;
v___y_4377_ = v_a_4363_;
v___y_4378_ = v_a_4364_;
v___y_4379_ = v_a_4365_;
v___y_4380_ = v_a_4366_;
v___y_4381_ = v_a_4367_;
goto v___jp_4373_;
}
else
{
lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4388_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4386_);
v___x_4389_ = l_Lean_Expr_isApp(v___x_4388_);
if (v___x_4389_ == 0)
{
lean_dec_ref(v___x_4388_);
lean_dec(v_inv_4359_);
v___y_4374_ = v_a_4360_;
v___y_4375_ = v_a_4361_;
v___y_4376_ = v_a_4362_;
v___y_4377_ = v_a_4363_;
v___y_4378_ = v_a_4364_;
v___y_4379_ = v_a_4365_;
v___y_4380_ = v_a_4366_;
v___y_4381_ = v_a_4367_;
goto v___jp_4373_;
}
else
{
lean_object* v_arg_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
v_arg_4390_ = lean_ctor_get(v___x_4388_, 1);
lean_inc_ref(v_arg_4390_);
v___x_4391_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4388_);
v___x_4392_ = l_Lean_Expr_isApp(v___x_4391_);
if (v___x_4392_ == 0)
{
lean_dec_ref(v___x_4391_);
lean_dec_ref(v_arg_4390_);
lean_dec(v_inv_4359_);
v___y_4374_ = v_a_4360_;
v___y_4375_ = v_a_4361_;
v___y_4376_ = v_a_4362_;
v___y_4377_ = v_a_4363_;
v___y_4378_ = v_a_4364_;
v___y_4379_ = v_a_4365_;
v___y_4380_ = v_a_4366_;
v___y_4381_ = v_a_4367_;
goto v___jp_4373_;
}
else
{
lean_object* v_arg_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
v_arg_4393_ = lean_ctor_get(v___x_4391_, 1);
lean_inc_ref(v_arg_4393_);
v___x_4394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4391_);
v___x_4395_ = l_Lean_Expr_isApp(v___x_4394_);
if (v___x_4395_ == 0)
{
lean_dec_ref(v___x_4394_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
lean_dec(v_inv_4359_);
v___y_4374_ = v_a_4360_;
v___y_4375_ = v_a_4361_;
v___y_4376_ = v_a_4362_;
v___y_4377_ = v_a_4363_;
v___y_4378_ = v_a_4364_;
v___y_4379_ = v_a_4365_;
v___y_4380_ = v_a_4366_;
v___y_4381_ = v_a_4367_;
goto v___jp_4373_;
}
else
{
lean_object* v_arg_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; uint8_t v___x_4402_; 
v_arg_4396_ = lean_ctor_get(v___x_4394_, 1);
lean_inc_ref(v_arg_4396_);
v___x_4397_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4394_);
v___x_4398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4400_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4401_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4402_ = l_Lean_Expr_isConstOf(v___x_4397_, v___x_4401_);
if (v___x_4402_ == 0)
{
lean_dec_ref(v___x_4397_);
lean_dec_ref(v_arg_4396_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
lean_dec(v_inv_4359_);
v___y_4374_ = v_a_4360_;
v___y_4375_ = v_a_4361_;
v___y_4376_ = v_a_4362_;
v___y_4377_ = v_a_4363_;
v___y_4378_ = v_a_4364_;
v___y_4379_ = v_a_4365_;
v___y_4380_ = v_a_4366_;
v___y_4381_ = v_a_4367_;
goto v___jp_4373_;
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v_a_4409_; lean_object* v___y_4421_; lean_object* v___x_4431_; lean_object* v___x_4432_; uint8_t v___x_4433_; 
lean_dec(v_a_4372_);
v___x_4403_ = lean_unsigned_to_nat(1u);
v___x_4404_ = l_Lean_Expr_constLevels_x21(v___x_4397_);
lean_dec_ref(v___x_4397_);
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4404_);
v___x_4407_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4404_, v___x_4404_, v___x_4403_, v___x_4406_);
lean_dec(v___x_4404_);
v___x_4431_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4432_ = lean_array_get_size(v_vcs_4358_);
v___x_4433_ = lean_nat_dec_lt(v___x_4405_, v___x_4432_);
if (v___x_4433_ == 0)
{
v_a_4409_ = v___x_4431_;
goto v___jp_4408_;
}
else
{
uint8_t v___x_4434_; 
v___x_4434_ = lean_nat_dec_le(v___x_4432_, v___x_4432_);
if (v___x_4434_ == 0)
{
if (v___x_4433_ == 0)
{
v_a_4409_ = v___x_4431_;
goto v___jp_4408_;
}
else
{
size_t v___x_4435_; size_t v___x_4436_; lean_object* v___x_4437_; 
v___x_4435_ = ((size_t)0ULL);
v___x_4436_ = lean_usize_of_nat(v___x_4432_);
v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4358_, v___x_4435_, v___x_4436_, v___x_4431_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
v___y_4421_ = v___x_4437_;
goto v___jp_4420_;
}
}
else
{
size_t v___x_4438_; size_t v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((size_t)0ULL);
v___x_4439_ = lean_usize_of_nat(v___x_4432_);
v___x_4440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4358_, v___x_4438_, v___x_4439_, v___x_4431_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
v___y_4421_ = v___x_4440_;
goto v___jp_4420_;
}
}
v___jp_4408_:
{
lean_object* v___x_4410_; lean_object* v___f_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___f_4418_; lean_object* v___x_4419_; 
v___x_4410_ = lean_box(v___x_4402_);
lean_inc_ref(v_arg_4390_);
lean_inc_n(v_inv_4359_, 2);
lean_inc_ref(v_a_4409_);
v___f_4411_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4411_, 0, v_a_4409_);
lean_closure_set(v___f_4411_, 1, v_inv_4359_);
lean_closure_set(v___f_4411_, 2, v___x_4410_);
lean_closure_set(v___f_4411_, 3, v___x_4403_);
lean_closure_set(v___f_4411_, 4, v_arg_4390_);
v___x_4412_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4413_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4414_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4415_ = l_Lean_mkConst(v___x_4414_, v___x_4407_);
v___x_4416_ = l_Lean_mkAppB(v___x_4415_, v_arg_4396_, v_arg_4393_);
v___x_4417_ = lean_box(v___x_4402_);
v___f_4418_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4418_, 0, v___x_4413_);
lean_closure_set(v___f_4418_, 1, v___x_4416_);
lean_closure_set(v___f_4418_, 2, v___f_4411_);
lean_closure_set(v___f_4418_, 3, v_a_4409_);
lean_closure_set(v___f_4418_, 4, v_inv_4359_);
lean_closure_set(v___f_4418_, 5, v_arg_4390_);
lean_closure_set(v___f_4418_, 6, v___x_4417_);
lean_closure_set(v___f_4418_, 7, v___x_4403_);
lean_closure_set(v___f_4418_, 8, v___x_4405_);
lean_closure_set(v___f_4418_, 9, v___x_4400_);
lean_closure_set(v___f_4418_, 10, v___x_4398_);
lean_closure_set(v___f_4418_, 11, v___x_4399_);
lean_closure_set(v___f_4418_, 12, v___x_4412_);
v___x_4419_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4359_, v___f_4418_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
return v___x_4419_;
}
v___jp_4420_:
{
if (lean_obj_tag(v___y_4421_) == 0)
{
lean_object* v_a_4422_; 
v_a_4422_ = lean_ctor_get(v___y_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___y_4421_, 1);
v_a_4409_ = v_a_4422_;
goto v___jp_4408_;
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v___x_4407_);
lean_dec_ref(v_arg_4396_);
lean_dec_ref(v_arg_4393_);
lean_dec_ref(v_arg_4390_);
lean_dec(v_inv_4359_);
v_a_4423_ = lean_ctor_get(v___y_4421_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___y_4421_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___y_4421_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___y_4421_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
}
}
}
}
v___jp_4373_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4382_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4383_ = l_Lean_MessageData_ofExpr(v_a_4372_);
v___x_4384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4382_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
v___x_4385_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4384_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
return v___x_4385_;
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_inv_4359_);
v_a_4441_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4369_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4369_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4449_, lean_object* v_inv_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4449_, v_inv_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec_ref(v_vcs_4449_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4461_, lean_object* v_msg_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4462_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4473_, lean_object* v_msg_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4473_, v_msg_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4485_, lean_object* v_name_4486_, uint8_t v_bi_4487_, lean_object* v_type_4488_, lean_object* v_k_4489_, uint8_t v_kind_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4486_, v_bi_4487_, v_type_4488_, v_k_4489_, v_kind_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4501_, lean_object* v_name_4502_, lean_object* v_bi_4503_, lean_object* v_type_4504_, lean_object* v_k_4505_, lean_object* v_kind_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
uint8_t v_bi_boxed_4516_; uint8_t v_kind_boxed_4517_; lean_object* v_res_4518_; 
v_bi_boxed_4516_ = lean_unbox(v_bi_4503_);
v_kind_boxed_4517_ = lean_unbox(v_kind_4506_);
v_res_4518_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4501_, v_name_4502_, v_bi_boxed_4516_, v_type_4504_, v_k_4505_, v_kind_boxed_4517_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4519_, lean_object* v_name_4520_, lean_object* v_type_4521_, lean_object* v_k_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4520_, v_type_4521_, v_k_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4533_, lean_object* v_name_4534_, lean_object* v_type_4535_, lean_object* v_k_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4533_, v_name_4534_, v_type_4535_, v_k_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4547_, size_t v_sz_4548_, size_t v_i_4549_, lean_object* v_b_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___x_4560_; 
v___x_4560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4547_, v_sz_4548_, v_i_4549_, v_b_4550_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4561_, lean_object* v_sz_4562_, lean_object* v_i_4563_, lean_object* v_b_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
size_t v_sz_boxed_4574_; size_t v_i_boxed_4575_; lean_object* v_res_4576_; 
v_sz_boxed_4574_ = lean_unbox_usize(v_sz_4562_);
lean_dec(v_sz_4562_);
v_i_boxed_4575_ = lean_unbox_usize(v_i_4563_);
lean_dec(v_i_4563_);
v_res_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4561_, v_sz_boxed_4574_, v_i_boxed_4575_, v_b_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec_ref(v_as_4561_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4577_, size_t v_sz_4578_, size_t v_i_4579_, lean_object* v_b_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v___x_4590_; 
v___x_4590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4577_, v_sz_4578_, v_i_4579_, v_b_4580_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
return v___x_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4591_, lean_object* v_sz_4592_, lean_object* v_i_4593_, lean_object* v_b_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
size_t v_sz_boxed_4604_; size_t v_i_boxed_4605_; lean_object* v_res_4606_; 
v_sz_boxed_4604_ = lean_unbox_usize(v_sz_4592_);
lean_dec(v_sz_4592_);
v_i_boxed_4605_ = lean_unbox_usize(v_i_4593_);
lean_dec(v_i_4593_);
v_res_4606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4591_, v_sz_boxed_4604_, v_i_boxed_4605_, v_b_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec_ref(v_as_4591_);
return v_res_4606_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
