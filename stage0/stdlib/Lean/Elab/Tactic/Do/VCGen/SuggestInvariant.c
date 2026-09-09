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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object* v_inv_476_, uint8_t v___x_477_, lean_object* v_as_478_, size_t v_sz_479_, size_t v_i_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_a_488_; uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_lt(v_i_480_, v_sz_479_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
lean_dec(v_inv_476_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v_b_481_);
return v___x_493_;
}
else
{
lean_object* v_a_494_; lean_object* v___x_495_; 
lean_dec_ref(v_b_481_);
v_a_494_ = lean_array_uget_borrowed(v_as_478_, v_i_480_);
lean_inc(v_a_494_);
v___x_495_ = l_Lean_MVarId_getType(v_a_494_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v_a_500_; lean_object* v___x_537_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v___x_498_ = l_Lean_instInhabitedExpr;
v___x_537_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_496_, v___y_483_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_Expr_consumeMData(v_a_538_);
lean_dec(v_a_538_);
v_a_500_ = v___x_539_;
goto v___jp_499_;
}
else
{
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_540_; 
v_a_540_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_537_, 1);
v_a_500_ = v_a_540_;
goto v___jp_499_;
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_inv_476_);
v_a_541_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_537_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_537_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_501_, 0, v_a_500_);
lean_inc(v_a_494_);
v___x_502_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_494_, v___x_501_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_528_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_528_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_528_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_528_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
if (lean_obj_tag(v_a_503_) == 1)
{
lean_object* v_val_507_; lean_object* v_snd_508_; lean_object* v_snd_509_; lean_object* v___x_510_; 
v_val_507_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_val_507_);
lean_dec_ref_known(v_a_503_, 1);
v_snd_508_ = lean_ctor_get(v_val_507_, 1);
lean_inc(v_snd_508_);
lean_dec(v_val_507_);
v_snd_509_ = lean_ctor_get(v_snd_508_, 1);
lean_inc(v_snd_509_);
lean_dec(v_snd_508_);
lean_inc(v_inv_476_);
v___x_510_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_509_, v_inv_476_);
lean_dec(v_snd_509_);
switch(lean_obj_tag(v___x_510_))
{
case 0:
{
lean_object* v_invariantUse_511_; lean_object* v_cursorSuffix_512_; lean_object* v_letMuts_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_invariantUse_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc_ref(v_invariantUse_511_);
lean_dec_ref_known(v___x_510_, 1);
v_cursorSuffix_512_ = lean_ctor_get(v_invariantUse_511_, 2);
lean_inc_ref(v_cursorSuffix_512_);
v_letMuts_513_ = lean_ctor_get(v_invariantUse_511_, 3);
lean_inc_ref(v_letMuts_513_);
lean_dec_ref(v_invariantUse_511_);
v___x_514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_515_ = l_Lean_Expr_isAppOf(v_cursorSuffix_512_, v___x_514_);
lean_dec_ref(v_cursorSuffix_512_);
if (v___x_515_ == 0)
{
if (v___x_477_ == 0)
{
lean_dec_ref(v_letMuts_513_);
lean_del_object(v___x_505_);
v_a_488_ = v___x_497_;
goto v___jp_487_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_array_get(v___x_498_, v_letMuts_513_, v___x_516_);
lean_dec_ref(v_letMuts_513_);
v___x_518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5));
v___x_519_ = l_Lean_Expr_isAppOf(v___x_517_, v___x_518_);
lean_dec(v___x_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_inv_476_);
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_520_);
v___x_522_ = v___x_505_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_del_object(v___x_505_);
v_a_488_ = v___x_497_;
goto v___jp_487_;
}
}
}
else
{
lean_dec_ref(v_letMuts_513_);
lean_del_object(v___x_505_);
v_a_488_ = v___x_497_;
goto v___jp_487_;
}
}
case 1:
{
lean_del_object(v___x_505_);
v_a_488_ = v___x_497_;
goto v___jp_487_;
}
default: 
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_inv_476_);
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_524_);
v___x_526_ = v___x_505_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
v_a_488_ = v___x_497_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_inv_476_);
v_a_529_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_502_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_502_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_inv_476_);
v_a_549_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_495_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_495_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
v___jp_487_:
{
size_t v___x_489_; size_t v___x_490_; 
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_480_, v___x_489_);
lean_inc_ref(v_a_488_);
v_i_480_ = v___x_490_;
v_b_481_ = v_a_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object* v_inv_557_, lean_object* v___x_558_, lean_object* v_as_559_, lean_object* v_sz_560_, lean_object* v_i_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
uint8_t v___x_4463__boxed_568_; size_t v_sz_boxed_569_; size_t v_i_boxed_570_; lean_object* v_res_571_; 
v___x_4463__boxed_568_ = lean_unbox(v___x_558_);
v_sz_boxed_569_ = lean_unbox_usize(v_sz_560_);
lean_dec(v_sz_560_);
v_i_boxed_570_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_557_, v___x_4463__boxed_568_, v_as_559_, v_sz_boxed_569_, v_i_boxed_570_, v_b_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v_as_559_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object* v_vcs_576_, lean_object* v_inv_577_, lean_object* v_letMutsTy_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0));
v___x_591_ = l_Lean_Expr_isAppOf(v_letMutsTy_578_, v___x_590_);
if (v___x_591_ == 0)
{
lean_dec(v_inv_577_);
goto v___jp_584_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = l_Lean_Expr_getAppNumArgs(v_letMutsTy_578_);
v___x_593_ = lean_unsigned_to_nat(2u);
v___x_594_ = lean_nat_dec_lt(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_sub(v___x_592_, v___x_595_);
lean_dec(v___x_592_);
lean_inc(v___x_596_);
v___x_597_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_578_, v___x_596_);
v___x_598_ = l_Lean_Expr_cleanupAnnotations(v___x_597_);
v___x_599_ = l_Lean_Expr_isApp(v___x_598_);
if (v___x_599_ == 0)
{
lean_dec_ref(v___x_598_);
lean_dec(v___x_596_);
lean_dec(v_inv_577_);
goto v___jp_587_;
}
else
{
lean_object* v_arg_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_arg_600_ = lean_ctor_get(v___x_598_, 1);
lean_inc_ref(v_arg_600_);
v___x_601_ = l_Lean_Expr_appFnCleanup___redArg(v___x_598_);
v___x_602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1));
v___x_603_ = l_Lean_Expr_isConstOf(v___x_601_, v___x_602_);
lean_dec_ref(v___x_601_);
if (v___x_603_ == 0)
{
lean_dec_ref(v_arg_600_);
lean_dec(v___x_596_);
lean_dec(v_inv_577_);
goto v___jp_587_;
}
else
{
lean_object* v___x_604_; size_t v_sz_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v_sz_605_ = lean_array_size(v_vcs_576_);
v___x_606_ = ((size_t)0ULL);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_577_, v___x_603_, v_vcs_576_, v_sz_605_, v___x_606_, v___x_604_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_631_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_631_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_631_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_631_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_fst_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_629_; 
v_fst_612_ = lean_ctor_get(v_a_608_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_a_608_, 1);
lean_dec(v_unused_630_);
v___x_614_ = v_a_608_;
v_isShared_615_ = v_isSharedCheck_629_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_fst_612_);
lean_dec(v_a_608_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_629_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
if (lean_obj_tag(v_fst_612_) == 0)
{
lean_object* v___x_616_; lean_object* v_00_u03c3_617_; lean_object* v___x_619_; 
v___x_616_ = lean_nat_sub(v___x_596_, v___x_595_);
lean_dec(v___x_596_);
v_00_u03c3_617_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_578_, v___x_616_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v_00_u03c3_617_);
lean_ctor_set(v___x_614_, 0, v_arg_600_);
v___x_619_ = v___x_614_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_arg_600_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_00_u03c3_617_);
v___x_619_ = v_reuseFailAlloc_624_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_620_);
v___x_622_ = v___x_610_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v_val_625_; lean_object* v___x_627_; 
lean_del_object(v___x_614_);
lean_dec_ref(v_arg_600_);
lean_dec(v___x_596_);
v_val_625_ = lean_ctor_get(v_fst_612_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v_fst_612_, 1);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_val_625_);
v___x_627_ = v___x_610_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_val_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_arg_600_);
lean_dec(v___x_596_);
v_a_632_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_607_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_607_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
else
{
lean_dec(v___x_592_);
lean_dec(v_inv_577_);
goto v___jp_584_;
}
}
v___jp_584_:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_box(0);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
v___jp_587_:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object* v_vcs_640_, lean_object* v_inv_641_, lean_object* v_letMutsTy_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_vcs_640_, v_inv_641_, v_letMutsTy_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec_ref(v_letMutsTy_642_);
lean_dec_ref(v_vcs_640_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object* v_dontRevert_649_, lean_object* v_as_650_, size_t v_i_651_, size_t v_stop_652_, lean_object* v_b_653_){
_start:
{
lean_object* v___y_655_; uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_eq(v_i_651_, v_stop_652_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_array_uget_borrowed(v_as_650_, v_i_651_);
lean_inc_ref(v_dontRevert_649_);
lean_inc(v___x_660_);
v___x_661_ = lean_apply_1(v_dontRevert_649_, v___x_660_);
v___x_662_ = lean_unbox(v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_inc(v___x_660_);
v___x_663_ = lean_array_push(v_b_653_, v___x_660_);
v___y_655_ = v___x_663_;
goto v___jp_654_;
}
else
{
v___y_655_ = v_b_653_;
goto v___jp_654_;
}
}
else
{
lean_dec_ref(v_dontRevert_649_);
return v_b_653_;
}
v___jp_654_:
{
size_t v___x_656_; size_t v___x_657_; 
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_add(v_i_651_, v___x_656_);
v_i_651_ = v___x_657_;
v_b_653_ = v___y_655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object* v_dontRevert_664_, lean_object* v_as_665_, lean_object* v_i_666_, lean_object* v_stop_667_, lean_object* v_b_668_){
_start:
{
size_t v_i_boxed_669_; size_t v_stop_boxed_670_; lean_object* v_res_671_; 
v_i_boxed_669_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_stop_boxed_670_ = lean_unbox_usize(v_stop_667_);
lean_dec(v_stop_667_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_664_, v_as_665_, v_i_boxed_669_, v_stop_boxed_670_, v_b_668_);
lean_dec_ref(v_as_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t v_sz_672_, size_t v_i_673_, lean_object* v_bs_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_lt(v_i_673_, v_sz_672_);
if (v___x_675_ == 0)
{
return v_bs_674_;
}
else
{
lean_object* v_v_676_; lean_object* v___x_677_; lean_object* v_bs_x27_678_; lean_object* v___x_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v_v_676_ = lean_array_uget(v_bs_674_, v_i_673_);
v___x_677_ = lean_unsigned_to_nat(0u);
v_bs_x27_678_ = lean_array_uset(v_bs_674_, v_i_673_, v___x_677_);
v___x_679_ = l_Lean_mkFVar(v_v_676_);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_add(v_i_673_, v___x_680_);
v___x_682_ = lean_array_uset(v_bs_x27_678_, v_i_673_, v___x_679_);
v_i_673_ = v___x_681_;
v_bs_674_ = v___x_682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object* v_sz_684_, lean_object* v_i_685_, lean_object* v_bs_686_){
_start:
{
size_t v_sz_boxed_687_; size_t v_i_boxed_688_; lean_object* v_res_689_; 
v_sz_boxed_687_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v_i_boxed_688_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_boxed_687_, v_i_boxed_688_, v_bs_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t v_sz_690_, size_t v_i_691_, lean_object* v_bs_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = lean_usize_dec_lt(v_i_691_, v_sz_690_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v_bs_692_);
return v___x_699_;
}
else
{
lean_object* v_v_700_; lean_object* v___x_701_; 
v_v_700_ = lean_array_uget_borrowed(v_bs_692_, v_i_691_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v_v_700_);
v___x_701_ = lean_infer_type(v_v_700_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_703_; lean_object* v_bs_x27_704_; size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = lean_unsigned_to_nat(0u);
v_bs_x27_704_ = lean_array_uset(v_bs_692_, v_i_691_, v___x_703_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_691_, v___x_705_);
v___x_707_ = lean_array_uset(v_bs_x27_704_, v_i_691_, v_a_702_);
v_i_691_ = v___x_706_;
v_bs_692_ = v___x_707_;
goto _start;
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_bs_692_);
v_a_709_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_701_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_701_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object* v_sz_717_, lean_object* v_i_718_, lean_object* v_bs_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
size_t v_sz_boxed_725_; size_t v_i_boxed_726_; lean_object* v_res_727_; 
v_sz_boxed_725_ = lean_unbox_usize(v_sz_717_);
lean_dec(v_sz_717_);
v_i_boxed_726_ = lean_unbox_usize(v_i_718_);
lean_dec(v_i_718_);
v_res_727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_boxed_725_, v_i_boxed_726_, v_bs_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_dontRevert_728_, lean_object* v_as_729_, size_t v_i_730_, size_t v_stop_731_, lean_object* v_b_732_){
_start:
{
lean_object* v___y_734_; uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_eq(v_i_730_, v_stop_731_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_739_ = lean_array_uget_borrowed(v_as_729_, v_i_730_);
v___x_740_ = l_Lean_Expr_fvarId_x21(v___x_739_);
lean_inc_ref(v_dontRevert_728_);
v___x_741_ = lean_apply_1(v_dontRevert_728_, v___x_740_);
v___x_742_ = lean_unbox(v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_inc(v___x_739_);
v___x_743_ = lean_array_push(v_b_732_, v___x_739_);
v___y_734_ = v___x_743_;
goto v___jp_733_;
}
else
{
v___y_734_ = v_b_732_;
goto v___jp_733_;
}
}
else
{
lean_dec_ref(v_dontRevert_728_);
return v_b_732_;
}
v___jp_733_:
{
size_t v___x_735_; size_t v___x_736_; 
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_730_, v___x_735_);
v_i_730_ = v___x_736_;
v_b_732_ = v___y_734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_dontRevert_744_, lean_object* v_as_745_, lean_object* v_i_746_, lean_object* v_stop_747_, lean_object* v_b_748_){
_start:
{
size_t v_i_boxed_749_; size_t v_stop_boxed_750_; lean_object* v_res_751_; 
v_i_boxed_749_ = lean_unbox_usize(v_i_746_);
lean_dec(v_i_746_);
v_stop_boxed_750_ = lean_unbox_usize(v_stop_747_);
lean_dec(v_stop_747_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_744_, v_as_745_, v_i_boxed_749_, v_stop_boxed_750_, v_b_748_);
lean_dec_ref(v_as_745_);
return v_res_751_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object* v_a_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
uint8_t v___x_754_; 
v___x_754_ = 0;
return v___x_754_;
}
else
{
lean_object* v_key_755_; lean_object* v_tail_756_; uint8_t v___x_757_; 
v_key_755_ = lean_ctor_get(v_x_753_, 0);
v_tail_756_ = lean_ctor_get(v_x_753_, 2);
v___x_757_ = lean_expr_eqv(v_key_755_, v_a_752_);
if (v___x_757_ == 0)
{
v_x_753_ = v_tail_756_;
goto _start;
}
else
{
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_a_759_, lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_759_, v_x_760_);
lean_dec(v_x_760_);
lean_dec_ref(v_a_759_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
return v_x_763_;
}
else
{
lean_object* v_key_765_; lean_object* v_value_766_; lean_object* v_tail_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_790_; 
v_key_765_ = lean_ctor_get(v_x_764_, 0);
v_value_766_ = lean_ctor_get(v_x_764_, 1);
v_tail_767_ = lean_ctor_get(v_x_764_, 2);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_764_);
if (v_isSharedCheck_790_ == 0)
{
v___x_769_ = v_x_764_;
v_isShared_770_ = v_isSharedCheck_790_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_tail_767_);
lean_inc(v_value_766_);
lean_inc(v_key_765_);
lean_dec(v_x_764_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_790_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; uint64_t v___x_772_; uint64_t v___x_773_; uint64_t v___x_774_; uint64_t v_fold_775_; uint64_t v___x_776_; uint64_t v___x_777_; uint64_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_771_ = lean_array_get_size(v_x_763_);
v___x_772_ = l_Lean_Expr_hash(v_key_765_);
v___x_773_ = 32ULL;
v___x_774_ = lean_uint64_shift_right(v___x_772_, v___x_773_);
v_fold_775_ = lean_uint64_xor(v___x_772_, v___x_774_);
v___x_776_ = 16ULL;
v___x_777_ = lean_uint64_shift_right(v_fold_775_, v___x_776_);
v___x_778_ = lean_uint64_xor(v_fold_775_, v___x_777_);
v___x_779_ = lean_uint64_to_usize(v___x_778_);
v___x_780_ = lean_usize_of_nat(v___x_771_);
v___x_781_ = ((size_t)1ULL);
v___x_782_ = lean_usize_sub(v___x_780_, v___x_781_);
v___x_783_ = lean_usize_land(v___x_779_, v___x_782_);
v___x_784_ = lean_array_uget_borrowed(v_x_763_, v___x_783_);
lean_inc(v___x_784_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 2, v___x_784_);
v___x_786_ = v___x_769_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_key_765_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_value_766_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v___x_784_);
v___x_786_ = v_reuseFailAlloc_789_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; 
v___x_787_ = lean_array_uset(v_x_763_, v___x_783_, v___x_786_);
v_x_763_ = v___x_787_;
v_x_764_ = v_tail_767_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_i_791_, lean_object* v_source_792_, lean_object* v_target_793_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_array_get_size(v_source_792_);
v___x_795_ = lean_nat_dec_lt(v_i_791_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec_ref(v_source_792_);
lean_dec(v_i_791_);
return v_target_793_;
}
else
{
lean_object* v_es_796_; lean_object* v___x_797_; lean_object* v_source_798_; lean_object* v_target_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_es_796_ = lean_array_fget(v_source_792_, v_i_791_);
v___x_797_ = lean_box(0);
v_source_798_ = lean_array_fset(v_source_792_, v_i_791_, v___x_797_);
v_target_799_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_target_793_, v_es_796_);
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = lean_nat_add(v_i_791_, v___x_800_);
lean_dec(v_i_791_);
v_i_791_ = v___x_801_;
v_source_792_ = v_source_798_;
v_target_793_ = v_target_799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(lean_object* v_data_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_nbuckets_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_804_ = lean_array_get_size(v_data_803_);
v___x_805_ = lean_unsigned_to_nat(2u);
v_nbuckets_806_ = lean_nat_mul(v___x_804_, v___x_805_);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_box(0);
v___x_809_ = lean_mk_array(v_nbuckets_806_, v___x_808_);
v___x_810_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v___x_807_, v_data_803_, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_811_, lean_object* v_a_812_, lean_object* v_b_813_){
_start:
{
lean_object* v_size_814_; lean_object* v_buckets_815_; lean_object* v___x_816_; uint64_t v___x_817_; uint64_t v___x_818_; uint64_t v___x_819_; uint64_t v_fold_820_; uint64_t v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v___x_827_; size_t v___x_828_; lean_object* v_bkt_829_; uint8_t v___x_830_; 
v_size_814_ = lean_ctor_get(v_m_811_, 0);
v_buckets_815_ = lean_ctor_get(v_m_811_, 1);
v___x_816_ = lean_array_get_size(v_buckets_815_);
v___x_817_ = l_Lean_Expr_hash(v_a_812_);
v___x_818_ = 32ULL;
v___x_819_ = lean_uint64_shift_right(v___x_817_, v___x_818_);
v_fold_820_ = lean_uint64_xor(v___x_817_, v___x_819_);
v___x_821_ = 16ULL;
v___x_822_ = lean_uint64_shift_right(v_fold_820_, v___x_821_);
v___x_823_ = lean_uint64_xor(v_fold_820_, v___x_822_);
v___x_824_ = lean_uint64_to_usize(v___x_823_);
v___x_825_ = lean_usize_of_nat(v___x_816_);
v___x_826_ = ((size_t)1ULL);
v___x_827_ = lean_usize_sub(v___x_825_, v___x_826_);
v___x_828_ = lean_usize_land(v___x_824_, v___x_827_);
v_bkt_829_ = lean_array_uget_borrowed(v_buckets_815_, v___x_828_);
v___x_830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_812_, v_bkt_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_851_; 
lean_inc_ref(v_buckets_815_);
lean_inc(v_size_814_);
v_isSharedCheck_851_ = !lean_is_exclusive(v_m_811_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; lean_object* v_unused_853_; 
v_unused_852_ = lean_ctor_get(v_m_811_, 1);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_m_811_, 0);
lean_dec(v_unused_853_);
v___x_832_ = v_m_811_;
v_isShared_833_ = v_isSharedCheck_851_;
goto v_resetjp_831_;
}
else
{
lean_dec(v_m_811_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_851_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v_size_x27_835_; lean_object* v___x_836_; lean_object* v_buckets_x27_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_834_ = lean_unsigned_to_nat(1u);
v_size_x27_835_ = lean_nat_add(v_size_814_, v___x_834_);
lean_dec(v_size_814_);
lean_inc(v_bkt_829_);
v___x_836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_836_, 0, v_a_812_);
lean_ctor_set(v___x_836_, 1, v_b_813_);
lean_ctor_set(v___x_836_, 2, v_bkt_829_);
v_buckets_x27_837_ = lean_array_uset(v_buckets_815_, v___x_828_, v___x_836_);
v___x_838_ = lean_unsigned_to_nat(4u);
v___x_839_ = lean_nat_mul(v_size_x27_835_, v___x_838_);
v___x_840_ = lean_unsigned_to_nat(3u);
v___x_841_ = lean_nat_div(v___x_839_, v___x_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_array_get_size(v_buckets_x27_837_);
v___x_843_ = lean_nat_dec_le(v___x_841_, v___x_842_);
lean_dec(v___x_841_);
if (v___x_843_ == 0)
{
lean_object* v_val_844_; lean_object* v___x_846_; 
v_val_844_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_buckets_x27_837_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_val_844_);
lean_ctor_set(v___x_832_, 0, v_size_x27_835_);
v___x_846_ = v___x_832_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_size_x27_835_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_val_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v___x_849_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_buckets_x27_837_);
lean_ctor_set(v___x_832_, 0, v_size_x27_835_);
v___x_849_ = v___x_832_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_size_x27_835_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_buckets_x27_837_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_dec(v_b_813_);
lean_dec_ref(v_a_812_);
return v_m_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_as_854_, size_t v_sz_855_, size_t v_i_856_, lean_object* v_b_857_){
_start:
{
uint8_t v___x_858_; 
v___x_858_ = lean_usize_dec_lt(v_i_856_, v_sz_855_);
if (v___x_858_ == 0)
{
return v_b_857_;
}
else
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v_r_861_; size_t v___x_862_; size_t v___x_863_; 
v_a_859_ = lean_array_uget_borrowed(v_as_854_, v_i_856_);
v___x_860_ = lean_box(0);
lean_inc(v_a_859_);
v_r_861_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_857_, v_a_859_, v___x_860_);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_856_, v___x_862_);
v_i_856_ = v___x_863_;
v_b_857_ = v_r_861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_as_865_, lean_object* v_sz_866_, lean_object* v_i_867_, lean_object* v_b_868_){
_start:
{
size_t v_sz_boxed_869_; size_t v_i_boxed_870_; lean_object* v_res_871_; 
v_sz_boxed_869_ = lean_unbox_usize(v_sz_866_);
lean_dec(v_sz_866_);
v_i_boxed_870_ = lean_unbox_usize(v_i_867_);
lean_dec(v_i_867_);
v_res_871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_865_, v_sz_boxed_869_, v_i_boxed_870_, v_b_868_);
lean_dec_ref(v_as_865_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_872_, lean_object* v_l_873_){
_start:
{
size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; 
v_sz_874_ = lean_array_size(v_l_873_);
v___x_875_ = ((size_t)0ULL);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_l_873_, v_sz_874_, v___x_875_, v_m_872_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_877_, lean_object* v_l_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_877_, v_l_878_);
lean_dec_ref(v_l_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_880_, size_t v_i_881_, size_t v_stop_882_, lean_object* v_b_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = lean_usize_dec_eq(v_i_881_, v_stop_882_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; size_t v___x_887_; size_t v___x_888_; 
v___x_885_ = lean_array_uget_borrowed(v_as_880_, v_i_881_);
lean_inc(v___x_885_);
v___x_886_ = l_Lean_collectFVars(v_b_883_, v___x_885_);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_add(v_i_881_, v___x_887_);
v_i_881_ = v___x_888_;
v_b_883_ = v___x_886_;
goto _start;
}
else
{
return v_b_883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_890_, lean_object* v_i_891_, lean_object* v_stop_892_, lean_object* v_b_893_){
_start:
{
size_t v_i_boxed_894_; size_t v_stop_boxed_895_; lean_object* v_res_896_; 
v_i_boxed_894_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_stop_boxed_895_ = lean_unbox_usize(v_stop_892_);
lean_dec(v_stop_892_);
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_890_, v_i_boxed_894_, v_stop_boxed_895_, v_b_893_);
lean_dec_ref(v_as_890_);
return v_res_896_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = lean_unsigned_to_nat(16u);
v___x_901_ = lean_mk_array(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object* v_dontRevert_905_, lean_object* v_a_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
v___x_912_ = 0;
v___x_913_ = 1;
lean_inc_ref(v_a_906_);
v___x_914_ = l_Lean_Meta_collectForwardDeps(v_a_906_, v___x_912_, v___x_913_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_988_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_988_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_988_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_988_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___y_921_; size_t v___y_922_; lean_object* v___y_923_; lean_object* v___x_933_; lean_object* v___x_934_; size_t v___y_936_; lean_object* v___y_937_; lean_object* v_fvarIds_938_; size_t v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_952_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_box(1);
v___x_934_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_979_ = lean_array_get_size(v_a_915_);
v___x_980_ = lean_nat_dec_lt(v___x_919_, v___x_979_);
if (v___x_980_ == 0)
{
lean_dec(v_a_915_);
v___y_952_ = v___x_934_;
goto v___jp_951_;
}
else
{
uint8_t v___x_981_; 
v___x_981_ = lean_nat_dec_le(v___x_979_, v___x_979_);
if (v___x_981_ == 0)
{
if (v___x_980_ == 0)
{
lean_dec(v_a_915_);
v___y_952_ = v___x_934_;
goto v___jp_951_;
}
else
{
size_t v___x_982_; size_t v___x_983_; lean_object* v___x_984_; 
v___x_982_ = ((size_t)0ULL);
v___x_983_ = lean_usize_of_nat(v___x_979_);
lean_inc_ref(v_dontRevert_905_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_905_, v_a_915_, v___x_982_, v___x_983_, v___x_934_);
lean_dec(v_a_915_);
v___y_952_ = v___x_984_;
goto v___jp_951_;
}
}
else
{
size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
v___x_985_ = ((size_t)0ULL);
v___x_986_ = lean_usize_of_nat(v___x_979_);
lean_inc_ref(v_dontRevert_905_);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_905_, v_a_915_, v___x_985_, v___x_986_, v___x_934_);
lean_dec(v_a_915_);
v___y_952_ = v___x_987_;
goto v___jp_951_;
}
}
v___jp_920_:
{
size_t v_sz_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_sz_924_ = lean_array_size(v___y_923_);
lean_inc_ref(v___y_923_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_924_, v___y_922_, v___y_923_);
v___x_926_ = l_Array_append___redArg(v___y_921_, v___x_925_);
lean_dec_ref(v___x_925_);
v___x_927_ = lean_array_get_size(v___y_923_);
lean_dec_ref(v___y_923_);
v___x_928_ = lean_nat_dec_eq(v___x_927_, v___x_919_);
if (v___x_928_ == 0)
{
lean_del_object(v___x_917_);
v_a_906_ = v___x_926_;
goto _start;
}
else
{
lean_object* v___x_931_; 
lean_dec_ref(v_dontRevert_905_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_926_);
v___x_931_ = v___x_917_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
v___jp_935_:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_array_get_size(v_fvarIds_938_);
v___x_940_ = lean_nat_dec_lt(v___x_919_, v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v_fvarIds_938_);
v___y_921_ = v___y_937_;
v___y_922_ = v___y_936_;
v___y_923_ = v___x_934_;
goto v___jp_920_;
}
else
{
uint8_t v___x_941_; 
v___x_941_ = lean_nat_dec_le(v___x_939_, v___x_939_);
if (v___x_941_ == 0)
{
if (v___x_940_ == 0)
{
lean_dec_ref(v_fvarIds_938_);
v___y_921_ = v___y_937_;
v___y_922_ = v___y_936_;
v___y_923_ = v___x_934_;
goto v___jp_920_;
}
else
{
size_t v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_usize_of_nat(v___x_939_);
lean_inc_ref(v_dontRevert_905_);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_905_, v_fvarIds_938_, v___y_936_, v___x_942_, v___x_934_);
lean_dec_ref(v_fvarIds_938_);
v___y_921_ = v___y_937_;
v___y_922_ = v___y_936_;
v___y_923_ = v___x_943_;
goto v___jp_920_;
}
}
else
{
size_t v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_usize_of_nat(v___x_939_);
lean_inc_ref(v_dontRevert_905_);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_905_, v_fvarIds_938_, v___y_936_, v___x_944_, v___x_934_);
lean_dec_ref(v_fvarIds_938_);
v___y_921_ = v___y_937_;
v___y_922_ = v___y_936_;
v___y_923_ = v___x_945_;
goto v___jp_920_;
}
}
}
v___jp_946_:
{
lean_object* v_fvarIds_950_; 
v_fvarIds_950_ = lean_ctor_get(v___y_949_, 2);
lean_inc_ref(v_fvarIds_950_);
lean_dec_ref(v___y_949_);
v___y_936_ = v___y_947_;
v___y_937_ = v___y_948_;
v_fvarIds_938_ = v_fvarIds_950_;
goto v___jp_935_;
}
v___jp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_953_ = lean_array_get_size(v___y_952_);
v___x_954_ = lean_array_get_size(v_a_906_);
lean_dec_ref(v_a_906_);
v___x_955_ = lean_nat_dec_eq(v___x_953_, v___x_954_);
if (v___x_955_ == 0)
{
size_t v_sz_956_; size_t v___x_957_; lean_object* v___x_958_; 
v_sz_956_ = lean_array_size(v___y_952_);
v___x_957_ = ((size_t)0ULL);
lean_inc_ref(v___y_952_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_956_, v___x_957_, v___y_952_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = lean_array_get_size(v_a_959_);
v___x_961_ = lean_nat_dec_lt(v___x_919_, v___x_960_);
if (v___x_961_ == 0)
{
lean_dec(v_a_959_);
v___y_936_ = v___x_957_;
v___y_937_ = v___y_952_;
v_fvarIds_938_ = v___x_934_;
goto v___jp_935_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_962_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_962_, v___y_952_);
v___x_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_933_);
lean_ctor_set(v___x_964_, 2, v___x_934_);
v___x_965_ = lean_nat_dec_le(v___x_960_, v___x_960_);
if (v___x_965_ == 0)
{
if (v___x_961_ == 0)
{
lean_dec_ref_known(v___x_964_, 3);
lean_dec(v_a_959_);
v___y_936_ = v___x_957_;
v___y_937_ = v___y_952_;
v_fvarIds_938_ = v___x_934_;
goto v___jp_935_;
}
else
{
size_t v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_usize_of_nat(v___x_960_);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_959_, v___x_957_, v___x_966_, v___x_964_);
lean_dec(v_a_959_);
v___y_947_ = v___x_957_;
v___y_948_ = v___y_952_;
v___y_949_ = v___x_967_;
goto v___jp_946_;
}
}
else
{
size_t v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_usize_of_nat(v___x_960_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_959_, v___x_957_, v___x_968_, v___x_964_);
lean_dec(v_a_959_);
v___y_947_ = v___x_957_;
v___y_948_ = v___y_952_;
v___y_949_ = v___x_969_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v___y_952_);
lean_del_object(v___x_917_);
lean_dec_ref(v_dontRevert_905_);
v_a_970_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_958_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_958_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v___x_978_; 
lean_del_object(v___x_917_);
lean_dec_ref(v_dontRevert_905_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___y_952_);
return v___x_978_;
}
}
}
}
else
{
lean_dec_ref(v_a_906_);
lean_dec_ref(v_dontRevert_905_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object* v_dontRevert_989_, lean_object* v_a_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_989_, v_a_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_996_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_997_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_998_ = lean_box(1);
v___x_999_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_1000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
lean_ctor_set(v___x_1000_, 2, v___x_997_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_1001_, lean_object* v_dontRevert_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___y_1009_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_fvarIds_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1016_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_1017_ = l_Lean_collectFVars(v___x_1016_, v_e_1001_);
v_fvarIds_1018_ = lean_ctor_get(v___x_1017_, 2);
lean_inc_ref(v_fvarIds_1018_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = lean_array_get_size(v_fvarIds_1018_);
v___x_1020_ = lean_nat_dec_lt(v___x_1014_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_dec_ref(v_fvarIds_1018_);
v___y_1009_ = v___x_1015_;
goto v___jp_1008_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1019_, v___x_1019_);
if (v___x_1021_ == 0)
{
if (v___x_1020_ == 0)
{
lean_dec_ref(v_fvarIds_1018_);
v___y_1009_ = v___x_1015_;
goto v___jp_1008_;
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1019_);
lean_inc_ref(v_dontRevert_1002_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1002_, v_fvarIds_1018_, v___x_1022_, v___x_1023_, v___x_1015_);
lean_dec_ref(v_fvarIds_1018_);
v___y_1009_ = v___x_1024_;
goto v___jp_1008_;
}
}
else
{
size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = lean_usize_of_nat(v___x_1019_);
lean_inc_ref(v_dontRevert_1002_);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1002_, v_fvarIds_1018_, v___x_1025_, v___x_1026_, v___x_1015_);
lean_dec_ref(v_fvarIds_1018_);
v___y_1009_ = v___x_1027_;
goto v___jp_1008_;
}
}
v___jp_1008_:
{
size_t v_sz_1010_; size_t v___x_1011_; lean_object* v_xs_1012_; lean_object* v___x_1013_; 
v_sz_1010_ = lean_array_size(v___y_1009_);
v___x_1011_ = ((size_t)0ULL);
v_xs_1012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1010_, v___x_1011_, v___y_1009_);
v___x_1013_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1002_, v_xs_1012_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1028_, lean_object* v_dontRevert_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1028_, v_dontRevert_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_1036_, lean_object* v_inst_1037_, lean_object* v_a_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1036_, v_a_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_1045_, lean_object* v_inst_1046_, lean_object* v_a_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1045_, v_inst_1046_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1054_, lean_object* v_m_1055_, lean_object* v_a_1056_, lean_object* v_b_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1055_, v_a_1056_, v_b_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1059_, lean_object* v_a_1060_, lean_object* v_x_1061_){
_start:
{
uint8_t v___x_1062_; 
v___x_1062_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_1060_, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1063_, lean_object* v_a_1064_, lean_object* v_x_1065_){
_start:
{
uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1063_, v_a_1064_, v_x_1065_);
lean_dec(v_x_1065_);
lean_dec_ref(v_a_1064_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1068_, lean_object* v_data_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_data_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1071_, lean_object* v_i_1072_, lean_object* v_source_1073_, lean_object* v_target_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v_i_1072_, v_source_1073_, v_target_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1086_, lean_object* v___x_1087_, lean_object* v___x_1088_, lean_object* v_i_1089_, lean_object* v_a_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_zero_1096_; uint8_t v_isZero_1097_; 
v_zero_1096_ = lean_unsigned_to_nat(0u);
v_isZero_1097_ = lean_nat_dec_eq(v_i_1089_, v_zero_1096_);
if (v_isZero_1097_ == 1)
{
lean_object* v___x_1098_; 
lean_dec(v_i_1089_);
lean_dec(v___x_1088_);
lean_dec_ref(v___x_1087_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_a_1090_);
return v___x_1098_;
}
else
{
lean_object* v_one_1099_; lean_object* v_n_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_one_1099_ = lean_unsigned_to_nat(1u);
v_n_1100_ = lean_nat_sub(v_i_1089_, v_one_1099_);
lean_dec(v_i_1089_);
v___x_1101_ = lean_array_fget_borrowed(v_a_1086_, v_n_1100_);
lean_inc_ref(v___x_1087_);
v___x_1102_ = l_Lean_LocalContext_getFVar_x21(v___x_1087_, v___x_1101_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_userName_1103_; lean_object* v_type_1104_; uint8_t v_bi_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_userName_1103_ = lean_ctor_get(v___x_1102_, 2);
lean_inc(v_userName_1103_);
v_type_1104_ = lean_ctor_get(v___x_1102_, 3);
lean_inc_ref(v_type_1104_);
v_bi_1105_ = lean_ctor_get_uint8(v___x_1102_, sizeof(void*)*4);
lean_dec_ref_known(v___x_1102_, 4);
v___x_1106_ = l_Lean_Expr_headBeta(v_type_1104_);
v___x_1107_ = lean_expr_abstract_range(v___x_1106_, v_n_1100_, v_a_1086_);
lean_dec_ref(v___x_1106_);
lean_inc_ref(v___x_1107_);
v___x_1108_ = l_Lean_Meta_getLevel(v___x_1107_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1111_ = lean_box(0);
lean_inc_n(v___x_1088_, 2);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1088_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1113_, 0, v_a_1109_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = l_Lean_mkConst(v___x_1110_, v___x_1113_);
v___x_1115_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1088_);
lean_inc_ref(v___x_1107_);
v___x_1116_ = l_Lean_mkLambda(v_userName_1103_, v_bi_1105_, v___x_1107_, v_a_1090_);
v___x_1117_ = l_Lean_mkApp3(v___x_1114_, v___x_1107_, v___x_1115_, v___x_1116_);
v_i_1089_ = v_n_1100_;
v_a_1090_ = v___x_1117_;
goto _start;
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v___x_1107_);
lean_dec(v_userName_1103_);
lean_dec(v_n_1100_);
lean_dec_ref(v_a_1090_);
lean_dec(v___x_1088_);
lean_dec_ref(v___x_1087_);
v_a_1119_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1108_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1108_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
uint8_t v_nondep_1127_; 
v_nondep_1127_ = lean_ctor_get_uint8(v___x_1102_, sizeof(void*)*5);
if (v_nondep_1127_ == 0)
{
lean_object* v_userName_1128_; lean_object* v_type_1129_; lean_object* v_value_1130_; uint8_t v___x_1131_; 
v_userName_1128_ = lean_ctor_get(v___x_1102_, 2);
lean_inc(v_userName_1128_);
v_type_1129_ = lean_ctor_get(v___x_1102_, 3);
lean_inc_ref(v_type_1129_);
v_value_1130_ = lean_ctor_get(v___x_1102_, 4);
lean_inc_ref(v_value_1130_);
lean_dec_ref_known(v___x_1102_, 5);
v___x_1131_ = lean_expr_has_loose_bvar(v_a_1090_, v_zero_1096_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v_value_1130_);
lean_dec_ref(v_type_1129_);
lean_dec(v_userName_1128_);
v___x_1132_ = lean_expr_lower_loose_bvars(v_a_1090_, v_one_1099_, v_one_1099_);
lean_dec_ref(v_a_1090_);
v_i_1089_ = v_n_1100_;
v_a_1090_ = v___x_1132_;
goto _start;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = l_Lean_Expr_headBeta(v_type_1129_);
v___x_1135_ = lean_expr_abstract_range(v___x_1134_, v_n_1100_, v_a_1086_);
lean_dec_ref(v___x_1134_);
v___x_1136_ = lean_expr_abstract_range(v_value_1130_, v_n_1100_, v_a_1086_);
lean_dec_ref(v_value_1130_);
v___x_1137_ = l_Lean_Expr_letE___override(v_userName_1128_, v___x_1135_, v___x_1136_, v_a_1090_, v_nondep_1127_);
v_i_1089_ = v_n_1100_;
v_a_1090_ = v___x_1137_;
goto _start;
}
}
else
{
lean_object* v_userName_1139_; lean_object* v_type_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_userName_1139_ = lean_ctor_get(v___x_1102_, 2);
lean_inc(v_userName_1139_);
v_type_1140_ = lean_ctor_get(v___x_1102_, 3);
lean_inc_ref(v_type_1140_);
lean_dec_ref_known(v___x_1102_, 5);
v___x_1141_ = l_Lean_Expr_headBeta(v_type_1140_);
v___x_1142_ = lean_expr_abstract_range(v___x_1141_, v_n_1100_, v_a_1086_);
lean_dec_ref(v___x_1141_);
lean_inc_ref(v___x_1142_);
v___x_1143_ = l_Lean_Meta_getLevel(v___x_1142_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1146_ = lean_box(0);
lean_inc_n(v___x_1088_, 2);
v___x_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1088_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_mkConst(v___x_1145_, v___x_1148_);
v___x_1150_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1088_);
v___x_1151_ = 0;
lean_inc_ref(v___x_1142_);
v___x_1152_ = l_Lean_mkLambda(v_userName_1139_, v___x_1151_, v___x_1142_, v_a_1090_);
v___x_1153_ = l_Lean_mkApp3(v___x_1149_, v___x_1142_, v___x_1150_, v___x_1152_);
v_i_1089_ = v_n_1100_;
v_a_1090_ = v___x_1153_;
goto _start;
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v___x_1142_);
lean_dec(v_userName_1139_);
lean_dec(v_n_1100_);
lean_dec_ref(v_a_1090_);
lean_dec(v___x_1088_);
lean_dec_ref(v___x_1087_);
v_a_1155_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1143_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1143_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1163_, lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v_i_1166_, lean_object* v_a_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1163_, v___x_1164_, v___x_1165_, v_i_1166_, v_a_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec_ref(v_a_1163_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1178_, lean_object* v_dontRevert_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1185_; 
lean_inc_ref(v_e_1178_);
v___x_1185_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1178_, v_dontRevert_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v_lctx_1187_; lean_object* v___x_1188_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v_lctx_1187_ = lean_ctor_get(v_a_1180_, 2);
lean_inc(v_a_1183_);
lean_inc_ref(v_a_1182_);
lean_inc(v_a_1181_);
lean_inc_ref(v_a_1180_);
lean_inc_ref(v_e_1178_);
v___x_1188_ = lean_infer_type(v_e_1178_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1211_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1211_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1211_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = l_Lean_Expr_cleanupAnnotations(v_a_1189_);
v___x_1194_ = l_Lean_Expr_isApp(v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1196_; 
lean_dec_ref(v___x_1193_);
lean_dec(v_a_1186_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v_e_1178_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_e_1178_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1198_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1193_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1200_ = l_Lean_Expr_isConstOf(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1202_; 
lean_dec_ref(v___x_1198_);
lean_dec(v_a_1186_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v_e_1178_);
v___x_1202_ = v___x_1191_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_e_1178_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_del_object(v___x_1191_);
v___x_1204_ = lean_box(0);
v___x_1205_ = l_Lean_Expr_constLevels_x21(v___x_1198_);
lean_dec_ref(v___x_1198_);
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = l_List_get_x21Internal___redArg(v___x_1204_, v___x_1205_, v___x_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_array_get_size(v_a_1186_);
v___x_1209_ = lean_expr_abstract(v_e_1178_, v_a_1186_);
lean_dec_ref(v_e_1178_);
lean_inc_ref(v_lctx_1187_);
v___x_1210_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1186_, v_lctx_1187_, v___x_1207_, v___x_1208_, v___x_1209_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1186_);
return v___x_1210_;
}
}
}
}
else
{
lean_dec(v_a_1186_);
lean_dec_ref(v_e_1178_);
return v___x_1188_;
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_e_1178_);
v_a_1212_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1185_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1185_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1220_, lean_object* v_dontRevert_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1220_, v_dontRevert_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1228_, lean_object* v___x_1229_, lean_object* v___x_1230_, lean_object* v_n_1231_, lean_object* v_i_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1228_, v___x_1229_, v___x_1230_, v_i_1232_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v_n_1244_, lean_object* v_i_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1241_, v___x_1242_, v___x_1243_, v_n_1244_, v_i_1245_, v_a_1246_, v_a_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v_n_1244_);
lean_dec_ref(v_a_1241_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1260_, lean_object* v_lhs_1261_, lean_object* v_rhs_1262_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1263_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1264_ = lean_box(0);
lean_inc(v_lvl_1260_);
v___x_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_lvl_1260_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = l_Lean_mkConst(v___x_1263_, v___x_1265_);
v___x_1267_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1260_);
v___x_1268_ = l_Lean_mkApp3(v___x_1266_, v___x_1267_, v_lhs_1261_, v_rhs_1262_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1275_, lean_object* v_lhs_1276_, lean_object* v_rhs_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1279_ = lean_box(0);
lean_inc(v_lvl_1275_);
v___x_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_lvl_1275_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_mkConst(v___x_1278_, v___x_1280_);
v___x_1282_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1275_);
v___x_1283_ = l_Lean_mkApp3(v___x_1281_, v___x_1282_, v_lhs_1276_, v_rhs_1277_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1284_){
_start:
{
lean_object* v_lvl_1285_; lean_object* v_cursorPred_1286_; lean_object* v_letMutsPred_1287_; lean_object* v___x_1288_; 
v_lvl_1285_ = lean_ctor_get(v_p_1284_, 0);
lean_inc(v_lvl_1285_);
v_cursorPred_1286_ = lean_ctor_get(v_p_1284_, 1);
lean_inc_ref(v_cursorPred_1286_);
v_letMutsPred_1287_ = lean_ctor_get(v_p_1284_, 2);
lean_inc_ref(v_letMutsPred_1287_);
lean_dec_ref(v_p_1284_);
v___x_1288_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1285_, v_cursorPred_1286_, v_letMutsPred_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(lean_object* v_x_1289_){
_start:
{
switch(lean_obj_tag(v_x_1289_))
{
case 0:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
return v___x_1290_;
}
case 1:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_unsigned_to_nat(1u);
return v___x_1291_;
}
case 2:
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_unsigned_to_nat(2u);
return v___x_1292_;
}
default: 
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_unsigned_to_nat(3u);
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___boxed(lean_object* v_x_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(v_x_1294_);
lean_dec(v_x_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1296_, lean_object* v_k_1297_){
_start:
{
if (lean_obj_tag(v_t_1296_) == 3)
{
lean_object* v_e_1298_; lean_object* v___x_1299_; 
v_e_1298_ = lean_ctor_get(v_t_1296_, 0);
lean_inc_ref(v_e_1298_);
lean_dec_ref_known(v_t_1296_, 1);
v___x_1299_ = lean_apply_1(v_k_1297_, v_e_1298_);
return v___x_1299_;
}
else
{
lean_dec(v_t_1296_);
return v_k_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1300_, lean_object* v_ctorIdx_1301_, lean_object* v_t_1302_, lean_object* v_h_1303_, lean_object* v_k_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1302_, v_k_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1306_, lean_object* v_ctorIdx_1307_, lean_object* v_t_1308_, lean_object* v_h_1309_, lean_object* v_k_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1306_, v_ctorIdx_1307_, v_t_1308_, v_h_1309_, v_k_1310_);
lean_dec(v_ctorIdx_1307_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1312_, lean_object* v_punit_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1312_, v_punit_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1315_, lean_object* v_t_1316_, lean_object* v_h_1317_, lean_object* v_punit_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1316_, v_punit_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1320_, lean_object* v_false_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1320_, v_false_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1323_, lean_object* v_t_1324_, lean_object* v_h_1325_, lean_object* v_false_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1324_, v_false_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1328_, lean_object* v_true_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1328_, v_true_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1331_, lean_object* v_t_1332_, lean_object* v_h_1333_, lean_object* v_true_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1332_, v_true_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1336_, lean_object* v_other_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1336_, v_other_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1339_, lean_object* v_t_1340_, lean_object* v_h_1341_, lean_object* v_other_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1340_, v_other_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1344_){
_start:
{
lean_object* v_snd_1346_; lean_object* v_fst_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1386_; 
v_snd_1346_ = lean_ctor_get(v_a_1344_, 1);
v_fst_1347_ = lean_ctor_get(v_a_1344_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_a_1344_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1349_ = v_a_1344_;
v_isShared_1350_ = v_isSharedCheck_1386_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snd_1346_);
lean_inc(v_fst_1347_);
lean_dec(v_a_1344_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1386_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_fst_1351_; lean_object* v_snd_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1385_; 
v_fst_1351_ = lean_ctor_get(v_snd_1346_, 0);
v_snd_1352_ = lean_ctor_get(v_snd_1346_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_snd_1346_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1354_ = v_snd_1346_;
v_isShared_1355_ = v_isSharedCheck_1385_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_snd_1352_);
lean_inc(v_fst_1351_);
lean_dec(v_snd_1346_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1385_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1357_ = lean_unsigned_to_nat(4u);
v___x_1358_ = l_Lean_Expr_isAppOfArity(v_fst_1351_, v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1360_; 
if (v_isShared_1355_ == 0)
{
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_fst_1351_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_snd_1352_);
v___x_1360_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___x_1360_);
v___x_1362_ = v___x_1349_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_fst_1347_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1366_ = lean_unsigned_to_nat(3u);
v___x_1367_ = lean_unsigned_to_nat(2u);
v___x_1368_ = l_Lean_Expr_getAppNumArgs(v_fst_1351_);
v___x_1369_ = lean_nat_sub(v___x_1368_, v___x_1367_);
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_sub(v___x_1369_, v___x_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = l_Lean_Expr_getRevArg_x21(v_fst_1351_, v___x_1371_);
v___x_1373_ = lean_array_push(v_snd_1352_, v___x_1372_);
v___x_1374_ = lean_nat_add(v_fst_1347_, v___x_1370_);
lean_dec(v_fst_1347_);
v___x_1375_ = lean_nat_sub(v___x_1368_, v___x_1366_);
lean_dec(v___x_1368_);
v___x_1376_ = lean_nat_sub(v___x_1375_, v___x_1370_);
lean_dec(v___x_1375_);
v___x_1377_ = l_Lean_Expr_getRevArg_x21(v_fst_1351_, v___x_1376_);
lean_dec(v_fst_1351_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___x_1373_);
lean_ctor_set(v___x_1354_, 0, v___x_1377_);
v___x_1379_ = v___x_1354_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1373_);
v___x_1379_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___x_1379_);
lean_ctor_set(v___x_1349_, 0, v___x_1374_);
v___x_1381_ = v___x_1349_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
v_a_1344_ = v___x_1381_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_fst_1390_, lean_object* v_p_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_inc(v_fst_1390_);
v___x_1392_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1390_);
v___x_1393_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1390_, v___x_1392_, v_p_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_letMutsTuple_1394_, lean_object* v___x_1395_, uint8_t v___x_1396_, lean_object* v_fvarId_1397_){
_start:
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1394_);
v___x_1399_ = l_Lean_instBEqFVarId_beq(v_fvarId_1397_, v___x_1398_);
lean_dec(v___x_1398_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; 
v___x_1400_ = l_Lean_LocalContext_contains(v___x_1395_, v_fvarId_1397_);
return v___x_1400_;
}
else
{
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1401_, lean_object* v___x_1402_, lean_object* v___x_1403_, lean_object* v_fvarId_1404_){
_start:
{
uint8_t v___x_9659__boxed_1405_; uint8_t v_res_1406_; lean_object* v_r_1407_; 
v___x_9659__boxed_1405_ = lean_unbox(v___x_1403_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1401_, v___x_1402_, v___x_9659__boxed_1405_, v_fvarId_1404_);
lean_dec(v_fvarId_1404_);
lean_dec_ref(v___x_1402_);
lean_dec_ref(v_letMutsTuple_1401_);
v_r_1407_ = lean_box(v_res_1406_);
return v_r_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1427_, lean_object* v___x_1428_, lean_object* v_xs_1429_, lean_object* v_letMuts_1430_, lean_object* v_as_1431_, size_t v_sz_1432_, size_t v_i_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_a_1441_; uint8_t v___x_1445_; 
v___x_1445_ = lean_usize_dec_lt(v_i_1433_, v_sz_1432_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1434_);
return v___x_1446_;
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_array_uget_borrowed(v_as_1431_, v_i_1433_);
lean_inc(v_a_1447_);
v___x_1448_ = l_Lean_MVarId_getType(v_a_1447_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_snd_1449_; lean_object* v_a_1450_; lean_object* v_fst_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1785_; 
v_snd_1449_ = lean_ctor_get(v_b_1434_, 1);
lean_inc(v_snd_1449_);
v_a_1450_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1448_, 1);
v_fst_1451_ = lean_ctor_get(v_b_1434_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_b_1434_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v_b_1434_, 1);
lean_dec(v_unused_1786_);
v___x_1453_ = v_b_1434_;
v_isShared_1454_ = v_isSharedCheck_1785_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_fst_1451_);
lean_dec(v_b_1434_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1785_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_fst_1455_; lean_object* v_snd_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1784_; 
v_fst_1455_ = lean_ctor_get(v_snd_1449_, 0);
v_snd_1456_ = lean_ctor_get(v_snd_1449_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_snd_1449_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1458_ = v_snd_1449_;
v_isShared_1459_ = v_isSharedCheck_1784_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_snd_1456_);
lean_inc(v_fst_1455_);
lean_dec(v_snd_1449_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1784_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; uint8_t v___y_1474_; lean_object* v___y_1574_; lean_object* v_prefixPoint_x3f_1575_; lean_object* v_suffixPoint_x3f_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v_prefixPoint_x3f_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v_a_1694_; lean_object* v_a_1699_; lean_object* v___x_1772_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1462_ = lean_box(0);
v___x_1772_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1450_, v___y_1436_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Lean_Expr_consumeMData(v_a_1773_);
lean_dec(v_a_1773_);
v_a_1699_ = v___x_1774_;
goto v___jp_1698_;
}
else
{
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1775_; 
v_a_1775_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1772_, 1);
v_a_1699_ = v_a_1775_;
goto v___jp_1698_;
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_del_object(v___x_1453_);
lean_dec(v_fst_1451_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1776_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1772_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1772_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
v___jp_1463_:
{
if (v___y_1474_ == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref(v___y_1466_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___y_1470_);
v___x_1476_ = v___x_1458_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___y_1470_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_snd_1456_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v___x_1476_);
lean_ctor_set(v___x_1453_, 0, v___y_1467_);
v___x_1478_ = v___x_1453_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___y_1467_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
v_a_1441_ = v___x_1478_;
goto v___jp_1440_;
}
}
}
else
{
lean_object* v___x_1482_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 1, v___x_1461_);
lean_ctor_set(v___x_1458_, 0, v___y_1466_);
v___x_1482_ = v___x_1458_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___y_1466_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1461_);
v___x_1482_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v___x_1482_);
lean_ctor_set(v___x_1453_, 0, v___x_1460_);
v___x_1484_ = v___x_1453_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1561_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v_snd_1487_ = lean_ctor_get(v_a_1486_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_a_1486_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v_a_1486_, 0);
lean_dec(v_unused_1562_);
v___x_1489_ = v_a_1486_;
v_isShared_1490_ = v_isSharedCheck_1561_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_dec(v_a_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1561_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_fst_1491_; lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1560_; 
v_fst_1491_ = lean_ctor_get(v_snd_1487_, 0);
v_snd_1492_ = lean_ctor_get(v_snd_1487_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_snd_1487_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1494_ = v_snd_1487_;
v_isShared_1495_ = v_isSharedCheck_1560_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_inc(v_fst_1491_);
lean_dec(v_snd_1487_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1560_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_points_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_points_1496_ = lean_ctor_get(v_snd_1456_, 0);
v___x_1497_ = lean_array_get_size(v_points_1496_);
v___x_1498_ = lean_array_get_size(v_snd_1492_);
v___x_1499_ = lean_nat_dec_lt(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1501_; 
lean_dec(v_snd_1492_);
lean_dec(v_fst_1491_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v_snd_1456_);
lean_ctor_set(v___x_1494_, 0, v___y_1470_);
v___x_1501_ = v___x_1494_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___y_1470_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_snd_1456_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1501_);
lean_ctor_set(v___x_1489_, 0, v___y_1467_);
v___x_1503_ = v___x_1489_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___y_1467_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
v_a_1441_ = v___x_1503_;
goto v___jp_1440_;
}
}
}
else
{
lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1557_; 
v_isSharedCheck_1557_ = !lean_is_exclusive(v_snd_1456_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; lean_object* v_unused_1559_; 
v_unused_1558_ = lean_ctor_get(v_snd_1456_, 1);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_snd_1456_, 0);
lean_dec(v_unused_1559_);
v___x_1507_ = v_snd_1456_;
v_isShared_1508_ = v_isSharedCheck_1557_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v_snd_1456_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1557_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2));
v___x_1510_ = l_Lean_Expr_isConstOf(v_fst_1491_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3));
lean_inc_ref(v___y_1464_);
lean_inc_ref(v___y_1469_);
lean_inc_ref(v___y_1472_);
v___x_1512_ = l_Lean_Name_mkStr4(v___y_1472_, v___y_1469_, v___y_1464_, v___x_1511_);
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = l_Lean_Expr_isAppOfArity(v_fst_1491_, v___x_1512_, v___x_1513_);
lean_dec(v___x_1512_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
lean_inc_ref(v___y_1464_);
lean_inc_ref(v___y_1469_);
lean_inc_ref(v___y_1472_);
v___x_1516_ = l_Lean_Name_mkStr4(v___y_1472_, v___y_1469_, v___y_1464_, v___x_1515_);
v___x_1517_ = l_Lean_Expr_isAppOfArity(v_fst_1491_, v___x_1516_, v___x_1513_);
lean_dec(v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_fst_1491_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1518_);
lean_ctor_set(v___x_1507_, 0, v_snd_1492_);
v___x_1520_ = v___x_1507_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_snd_1492_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1520_);
lean_ctor_set(v___x_1494_, 0, v___y_1470_);
v___x_1522_ = v___x_1494_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___y_1470_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1522_);
lean_ctor_set(v___x_1489_, 0, v___y_1467_);
v___x_1524_ = v___x_1489_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___y_1467_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
v_a_1441_ = v___x_1524_;
goto v___jp_1440_;
}
}
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_dec(v_fst_1491_);
v___x_1528_ = lean_box(2);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1528_);
lean_ctor_set(v___x_1507_, 0, v_snd_1492_);
v___x_1530_ = v___x_1507_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_snd_1492_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1532_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1530_);
lean_ctor_set(v___x_1494_, 0, v___y_1470_);
v___x_1532_ = v___x_1494_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___y_1470_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1532_);
lean_ctor_set(v___x_1489_, 0, v___y_1467_);
v___x_1534_ = v___x_1489_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___y_1467_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
v_a_1441_ = v___x_1534_;
goto v___jp_1440_;
}
}
}
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_dec(v_fst_1491_);
v___x_1538_ = lean_box(1);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1538_);
lean_ctor_set(v___x_1507_, 0, v_snd_1492_);
v___x_1540_ = v___x_1507_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_snd_1492_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1540_);
lean_ctor_set(v___x_1494_, 0, v___y_1470_);
v___x_1542_ = v___x_1494_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___y_1470_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1542_);
lean_ctor_set(v___x_1489_, 0, v___y_1467_);
v___x_1544_ = v___x_1489_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___y_1467_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
v_a_1441_ = v___x_1544_;
goto v___jp_1440_;
}
}
}
}
}
else
{
lean_object* v___x_1549_; 
lean_dec(v_fst_1491_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1462_);
lean_ctor_set(v___x_1507_, 0, v_snd_1492_);
v___x_1549_ = v___x_1507_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_snd_1492_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1462_);
v___x_1549_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1549_);
lean_ctor_set(v___x_1494_, 0, v___y_1470_);
v___x_1551_ = v___x_1494_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___y_1470_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1551_);
lean_ctor_set(v___x_1489_, 0, v___y_1467_);
v___x_1553_ = v___x_1489_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___y_1467_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
v_a_1441_ = v___x_1553_;
goto v___jp_1440_;
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
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v___y_1470_);
lean_dec(v___y_1467_);
lean_dec(v_snd_1456_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1563_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1485_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1485_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
}
}
v___jp_1573_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_1582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_1583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_1584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1585_ = lean_unsigned_to_nat(3u);
v___x_1586_ = l_Lean_Expr_isAppOfArity(v___y_1574_, v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec_ref(v___y_1574_);
lean_del_object(v___x_1458_);
lean_del_object(v___x_1453_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v_suffixPoint_x3f_1576_);
lean_ctor_set(v___x_1587_, 1, v_snd_1456_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_prefixPoint_x3f_1575_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v_a_1441_ = v___x_1588_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1589_ = l_Lean_Expr_appFn_x21(v___y_1574_);
v___x_1590_ = l_Lean_Expr_appArg_x21(v___x_1589_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = l_Lean_Expr_appArg_x21(v___y_1574_);
lean_dec_ref(v___y_1574_);
v___x_1592_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1593_ = l_Lean_Expr_isAppOfArity(v___x_1590_, v___x_1592_, v___x_1585_);
if (v___x_1593_ == 0)
{
lean_dec_ref(v___x_1590_);
v___y_1464_ = v___x_1583_;
v___y_1465_ = v___y_1580_;
v___y_1466_ = v___x_1591_;
v___y_1467_ = v_prefixPoint_x3f_1575_;
v___y_1468_ = v___y_1578_;
v___y_1469_ = v___x_1582_;
v___y_1470_ = v_suffixPoint_x3f_1576_;
v___y_1471_ = v___y_1577_;
v___y_1472_ = v___x_1581_;
v___y_1473_ = v___y_1579_;
v___y_1474_ = v___x_1593_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1594_ = lean_unsigned_to_nat(2u);
v___x_1595_ = l_Lean_Expr_getAppNumArgs(v___x_1590_);
v___x_1596_ = lean_nat_sub(v___x_1595_, v___x_1594_);
lean_dec(v___x_1595_);
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = lean_nat_sub(v___x_1596_, v___x_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = l_Lean_Expr_getRevArg_x21(v___x_1590_, v___x_1598_);
lean_dec_ref(v___x_1590_);
lean_inc(v_inv_1427_);
v___x_1600_ = l_Lean_mkMVar(v_inv_1427_);
v___x_1601_ = lean_expr_eqv(v___x_1599_, v___x_1600_);
lean_dec_ref(v___x_1600_);
lean_dec_ref(v___x_1599_);
v___y_1464_ = v___x_1583_;
v___y_1465_ = v___y_1580_;
v___y_1466_ = v___x_1591_;
v___y_1467_ = v_prefixPoint_x3f_1575_;
v___y_1468_ = v___y_1578_;
v___y_1469_ = v___x_1582_;
v___y_1470_ = v_suffixPoint_x3f_1576_;
v___y_1471_ = v___y_1577_;
v___y_1472_ = v___x_1581_;
v___y_1473_ = v___y_1579_;
v___y_1474_ = v___x_1601_;
goto v___jp_1463_;
}
}
}
v___jp_1602_:
{
lean_object* v___x_1613_; 
lean_inc(v_inv_1427_);
v___x_1613_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v___y_1603_, v_inv_1427_);
lean_dec_ref(v___y_1603_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_invariantUse_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1686_; 
v_invariantUse_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1686_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_invariantUse_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1686_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v_conditionIdx_1618_; lean_object* v_cursorSuffix_1619_; lean_object* v_letMutsTuple_1620_; uint8_t v___x_1621_; 
v_conditionIdx_1618_ = lean_ctor_get(v_invariantUse_1614_, 0);
lean_inc(v_conditionIdx_1618_);
v_cursorSuffix_1619_ = lean_ctor_get(v_invariantUse_1614_, 2);
lean_inc_ref(v_cursorSuffix_1619_);
v_letMutsTuple_1620_ = lean_ctor_get(v_invariantUse_1614_, 4);
lean_inc_ref(v_letMutsTuple_1620_);
lean_dec_ref(v_invariantUse_1614_);
v___x_1621_ = lean_nat_dec_eq(v_conditionIdx_1618_, v___x_1460_);
lean_dec(v_conditionIdx_1618_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec_ref(v_letMutsTuple_1620_);
lean_dec_ref(v_cursorSuffix_1619_);
lean_del_object(v___x_1616_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_del_object(v___x_1458_);
lean_del_object(v___x_1453_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v_fst_1455_);
lean_ctor_set(v___x_1622_, 1, v_snd_1456_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_prefixPoint_x3f_1608_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v_a_1441_ = v___x_1623_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1625_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1619_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_dec_ref(v_letMutsTuple_1620_);
lean_dec_ref(v_cursorSuffix_1619_);
lean_del_object(v___x_1616_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1604_);
v___y_1574_ = v___y_1605_;
v_prefixPoint_x3f_1575_ = v_prefixPoint_x3f_1608_;
v_suffixPoint_x3f_1576_ = v_fst_1455_;
v___y_1577_ = v___y_1609_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
goto v___jp_1573_;
}
else
{
uint8_t v___x_1626_; 
v___x_1626_ = l_Lean_Expr_isFVar(v_letMutsTuple_1620_);
if (v___x_1626_ == 0)
{
lean_dec_ref(v_letMutsTuple_1620_);
lean_dec_ref(v_cursorSuffix_1619_);
lean_del_object(v___x_1616_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1604_);
v___y_1574_ = v___y_1605_;
v_prefixPoint_x3f_1575_ = v_prefixPoint_x3f_1608_;
v_suffixPoint_x3f_1576_ = v_fst_1455_;
v___y_1577_ = v___y_1609_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc_ref(v_xs_1429_);
v___x_1628_ = l_Lean_Meta_mkProjection(v_xs_1429_, v___x_1627_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = l_Lean_Meta_mkEq(v_a_1629_, v_cursorSuffix_1619_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___f_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = lean_box(v___x_1621_);
lean_inc_ref(v___x_1428_);
lean_inc_ref(v_letMutsTuple_1620_);
v___f_1633_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1633_, 0, v_letMutsTuple_1620_);
lean_closure_set(v___f_1633_, 1, v___x_1428_);
lean_closure_set(v___f_1633_, 2, v___x_1632_);
v___x_1634_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1634_, 0, v___y_1606_);
lean_closure_set(v___x_1634_, 1, v___f_1633_);
lean_inc(v_a_1447_);
v___x_1635_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1447_, v___x_1634_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = l_Lean_Expr_replaceFVar(v_a_1636_, v_letMutsTuple_1620_, v_letMuts_1430_);
lean_dec(v_a_1636_);
if (lean_obj_tag(v_fst_1455_) == 1)
{
lean_object* v_val_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1631_);
lean_del_object(v___x_1616_);
lean_dec_ref(v___y_1607_);
v_val_1638_ = lean_ctor_get(v_fst_1455_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_fst_1455_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1640_ = v_fst_1455_;
v_isShared_1641_ = v_isSharedCheck_1656_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_val_1638_);
lean_dec(v_fst_1455_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1656_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_lvl_1642_; lean_object* v_cursorPred_1643_; lean_object* v_letMutsPred_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1655_; 
v_lvl_1642_ = lean_ctor_get(v_val_1638_, 0);
v_cursorPred_1643_ = lean_ctor_get(v_val_1638_, 1);
v_letMutsPred_1644_ = lean_ctor_get(v_val_1638_, 2);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_val_1638_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1646_ = v_val_1638_;
v_isShared_1647_ = v_isSharedCheck_1655_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_letMutsPred_1644_);
lean_inc(v_cursorPred_1643_);
lean_inc(v_lvl_1642_);
lean_dec(v_val_1638_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1655_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1604_, v_letMutsPred_1644_, v___x_1637_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 2, v___x_1648_);
v___x_1650_ = v___x_1646_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_lvl_1642_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_cursorPred_1643_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1652_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1650_);
v___x_1652_ = v___x_1640_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
v___y_1574_ = v___y_1605_;
v_prefixPoint_x3f_1575_ = v_prefixPoint_x3f_1608_;
v_suffixPoint_x3f_1576_ = v___x_1652_;
v___y_1577_ = v___y_1609_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
goto v___jp_1573_;
}
}
}
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
lean_dec(v_fst_1455_);
v___x_1657_ = lean_apply_1(v___y_1607_, v_a_1631_);
v___x_1658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1658_, 0, v___y_1604_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
lean_ctor_set(v___x_1658_, 2, v___x_1637_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 1);
lean_ctor_set(v___x_1616_, 0, v___x_1658_);
v___x_1660_ = v___x_1616_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
v___y_1574_ = v___y_1605_;
v_prefixPoint_x3f_1575_ = v_prefixPoint_x3f_1608_;
v_suffixPoint_x3f_1576_ = v___x_1660_;
v___y_1577_ = v___y_1609_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
goto v___jp_1573_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_a_1631_);
lean_dec_ref(v_letMutsTuple_1620_);
lean_del_object(v___x_1616_);
lean_dec(v_prefixPoint_x3f_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_del_object(v___x_1453_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1662_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1635_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1635_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v_letMutsTuple_1620_);
lean_del_object(v___x_1616_);
lean_dec(v_prefixPoint_x3f_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_del_object(v___x_1453_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1670_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1630_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1630_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v_letMutsTuple_1620_);
lean_dec_ref(v_cursorSuffix_1619_);
lean_del_object(v___x_1616_);
lean_dec(v_prefixPoint_x3f_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_del_object(v___x_1453_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1678_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1628_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1628_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
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
lean_dec(v___x_1613_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1604_);
v___y_1574_ = v___y_1605_;
v_prefixPoint_x3f_1575_ = v_prefixPoint_x3f_1608_;
v_suffixPoint_x3f_1576_ = v_fst_1455_;
v___y_1577_ = v___y_1609_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
goto v___jp_1573_;
}
}
v___jp_1687_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_inc_ref(v___y_1693_);
v___x_1695_ = lean_apply_1(v___y_1693_, v___y_1689_);
lean_inc(v___y_1690_);
v___x_1696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1696_, 0, v___y_1690_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
lean_ctor_set(v___x_1696_, 2, v_a_1694_);
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
v___y_1603_ = v___y_1688_;
v___y_1604_ = v___y_1690_;
v___y_1605_ = v___y_1691_;
v___y_1606_ = v___y_1692_;
v___y_1607_ = v___y_1693_;
v_prefixPoint_x3f_1608_ = v___x_1697_;
v___y_1609_ = v___y_1435_;
v___y_1610_ = v___y_1436_;
v___y_1611_ = v___y_1437_;
v___y_1612_ = v___y_1438_;
goto v___jp_1602_;
}
v___jp_1698_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_inc_ref(v_a_1699_);
v___x_1700_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1700_, 0, v_a_1699_);
lean_inc(v_a_1447_);
v___x_1701_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1447_, v___x_1700_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
if (lean_obj_tag(v_a_1702_) == 1)
{
lean_object* v_val_1703_; lean_object* v_snd_1704_; lean_object* v_fst_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1763_; 
v_val_1703_ = lean_ctor_get(v_a_1702_, 0);
lean_inc(v_val_1703_);
lean_dec_ref_known(v_a_1702_, 1);
v_snd_1704_ = lean_ctor_get(v_val_1703_, 1);
v_fst_1705_ = lean_ctor_get(v_val_1703_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_val_1703_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1707_ = v_val_1703_;
v_isShared_1708_ = v_isSharedCheck_1763_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snd_1704_);
lean_inc(v_fst_1705_);
lean_dec(v_val_1703_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1763_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_fst_1709_; lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1762_; 
v_fst_1709_ = lean_ctor_get(v_snd_1704_, 0);
v_snd_1710_ = lean_ctor_get(v_snd_1704_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_snd_1704_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1712_ = v_snd_1704_;
v_isShared_1713_ = v_isSharedCheck_1762_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_inc(v_fst_1709_);
lean_dec(v_snd_1704_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1762_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___f_1714_; lean_object* v___x_1715_; 
lean_inc(v_fst_1705_);
v___f_1714_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_1714_, 0, v_fst_1705_);
lean_inc(v_inv_1427_);
v___x_1715_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1710_, v_inv_1427_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_invariantUse_1716_; lean_object* v_conditionIdx_1717_; lean_object* v_cursorPrefix_1718_; lean_object* v_letMutsTuple_1719_; uint8_t v___x_1720_; 
v_invariantUse_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc_ref(v_invariantUse_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v_conditionIdx_1717_ = lean_ctor_get(v_invariantUse_1716_, 0);
lean_inc(v_conditionIdx_1717_);
v_cursorPrefix_1718_ = lean_ctor_get(v_invariantUse_1716_, 1);
lean_inc_ref(v_cursorPrefix_1718_);
v_letMutsTuple_1719_ = lean_ctor_get(v_invariantUse_1716_, 4);
lean_inc_ref(v_letMutsTuple_1719_);
lean_dec_ref(v_invariantUse_1716_);
v___x_1720_ = lean_nat_dec_eq(v_conditionIdx_1717_, v___x_1460_);
lean_dec(v_conditionIdx_1717_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1722_; 
lean_dec_ref(v_letMutsTuple_1719_);
lean_dec_ref(v_cursorPrefix_1718_);
lean_dec_ref(v___f_1714_);
lean_dec(v_snd_1710_);
lean_dec(v_fst_1709_);
lean_dec(v_fst_1705_);
lean_dec_ref(v_a_1699_);
lean_del_object(v___x_1458_);
lean_del_object(v___x_1453_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v_snd_1456_);
lean_ctor_set(v___x_1712_, 0, v_fst_1455_);
v___x_1722_ = v___x_1712_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_fst_1455_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_snd_1456_);
v___x_1722_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v___x_1722_);
lean_ctor_set(v___x_1707_, 0, v_fst_1451_);
v___x_1724_ = v___x_1707_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_fst_1451_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
v_a_1441_ = v___x_1724_;
goto v___jp_1440_;
}
}
}
else
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
lean_del_object(v___x_1712_);
lean_del_object(v___x_1707_);
v___x_1727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1728_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1718_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_dec_ref(v_letMutsTuple_1719_);
lean_dec_ref(v_cursorPrefix_1718_);
v___y_1603_ = v_fst_1709_;
v___y_1604_ = v_fst_1705_;
v___y_1605_ = v_a_1699_;
v___y_1606_ = v_snd_1710_;
v___y_1607_ = v___f_1714_;
v_prefixPoint_x3f_1608_ = v_fst_1451_;
v___y_1609_ = v___y_1435_;
v___y_1610_ = v___y_1436_;
v___y_1611_ = v___y_1437_;
v___y_1612_ = v___y_1438_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_fst_1451_);
v___x_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1429_);
v___x_1730_ = l_Lean_Meta_mkProjection(v_xs_1429_, v___x_1729_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = l_Lean_Meta_mkEq(v_a_1731_, v_cursorPrefix_1718_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
lean_inc_ref(v_letMuts_1430_);
v___x_1734_ = l_Lean_Meta_mkEq(v_letMuts_1430_, v_letMutsTuple_1719_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
lean_inc(v_fst_1705_);
v___x_1736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_fst_1705_, v_a_1735_);
v___y_1688_ = v_fst_1709_;
v___y_1689_ = v_a_1733_;
v___y_1690_ = v_fst_1705_;
v___y_1691_ = v_a_1699_;
v___y_1692_ = v_snd_1710_;
v___y_1693_ = v___f_1714_;
v_a_1694_ = v___x_1736_;
goto v___jp_1687_;
}
else
{
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1737_; 
v_a_1737_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1734_, 1);
v___y_1688_ = v_fst_1709_;
v___y_1689_ = v_a_1733_;
v___y_1690_ = v_fst_1705_;
v___y_1691_ = v_a_1699_;
v___y_1692_ = v_snd_1710_;
v___y_1693_ = v___f_1714_;
v_a_1694_ = v_a_1737_;
goto v___jp_1687_;
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_a_1733_);
lean_dec_ref(v___f_1714_);
lean_dec(v_snd_1710_);
lean_dec(v_fst_1709_);
lean_dec(v_fst_1705_);
lean_dec_ref(v_a_1699_);
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_del_object(v___x_1453_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1738_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1734_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1734_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v_letMutsTuple_1719_);
lean_dec_ref(v___f_1714_);
lean_dec(v_snd_1710_);
lean_dec(v_fst_1709_);
lean_dec(v_fst_1705_);
lean_dec_ref(v_a_1699_);
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_del_object(v___x_1453_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1746_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1732_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1732_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v_letMutsTuple_1719_);
lean_dec_ref(v_cursorPrefix_1718_);
lean_dec_ref(v___f_1714_);
lean_dec(v_snd_1710_);
lean_dec(v_fst_1709_);
lean_dec(v_fst_1705_);
lean_dec_ref(v_a_1699_);
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_del_object(v___x_1453_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1754_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1730_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1730_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1715_);
lean_del_object(v___x_1712_);
lean_del_object(v___x_1707_);
v___y_1603_ = v_fst_1709_;
v___y_1604_ = v_fst_1705_;
v___y_1605_ = v_a_1699_;
v___y_1606_ = v_snd_1710_;
v___y_1607_ = v___f_1714_;
v_prefixPoint_x3f_1608_ = v_fst_1451_;
v___y_1609_ = v___y_1435_;
v___y_1610_ = v___y_1436_;
v___y_1611_ = v___y_1437_;
v___y_1612_ = v___y_1438_;
goto v___jp_1602_;
}
}
}
}
else
{
lean_dec(v_a_1702_);
v___y_1574_ = v_a_1699_;
v_prefixPoint_x3f_1575_ = v_fst_1451_;
v_suffixPoint_x3f_1576_ = v_fst_1455_;
v___y_1577_ = v___y_1435_;
v___y_1578_ = v___y_1436_;
v___y_1579_ = v___y_1437_;
v___y_1580_ = v___y_1438_;
goto v___jp_1573_;
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_a_1699_);
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_del_object(v___x_1453_);
lean_dec(v_fst_1451_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1764_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1701_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1701_);
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
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_b_1434_);
lean_dec_ref(v_letMuts_1430_);
lean_dec_ref(v_xs_1429_);
lean_dec_ref(v___x_1428_);
lean_dec(v_inv_1427_);
v_a_1787_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1448_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1448_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
v___jp_1440_:
{
size_t v___x_1442_; size_t v___x_1443_; 
v___x_1442_ = ((size_t)1ULL);
v___x_1443_ = lean_usize_add(v_i_1433_, v___x_1442_);
v_i_1433_ = v___x_1443_;
v_b_1434_ = v_a_1441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1795_, lean_object* v___x_1796_, lean_object* v_xs_1797_, lean_object* v_letMuts_1798_, lean_object* v_as_1799_, lean_object* v_sz_1800_, lean_object* v_i_1801_, lean_object* v_b_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
size_t v_sz_boxed_1808_; size_t v_i_boxed_1809_; lean_object* v_res_1810_; 
v_sz_boxed_1808_ = lean_unbox_usize(v_sz_1800_);
lean_dec(v_sz_1800_);
v_i_boxed_1809_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1795_, v___x_1796_, v_xs_1797_, v_letMuts_1798_, v_as_1799_, v_sz_boxed_1808_, v_i_boxed_1809_, v_b_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v_as_1799_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1820_, lean_object* v_inv_1821_, lean_object* v_xs_1822_, lean_object* v_letMuts_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_lctx_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; size_t v_sz_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v_lctx_1829_ = lean_ctor_get(v_a_1824_, 2);
v___x_1830_ = lean_box(0);
v___x_1831_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1832_ = lean_array_size(v_vcs_1820_);
v___x_1833_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1829_);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1821_, v_lctx_1829_, v_xs_1822_, v_letMuts_1823_, v_vcs_1820_, v_sz_1832_, v___x_1833_, v___x_1831_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1878_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1878_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1878_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v_snd_1843_; lean_object* v_fst_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1877_; 
v_snd_1843_ = lean_ctor_get(v_a_1835_, 1);
v_fst_1844_ = lean_ctor_get(v_a_1835_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1846_ = v_a_1835_;
v_isShared_1847_ = v_isSharedCheck_1877_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snd_1843_);
lean_inc(v_fst_1844_);
lean_dec(v_a_1835_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1877_;
goto v_resetjp_1845_;
}
v___jp_1839_:
{
lean_object* v___x_1841_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1830_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1830_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
v_resetjp_1845_:
{
if (lean_obj_tag(v_fst_1844_) == 0)
{
lean_del_object(v___x_1846_);
lean_dec(v_snd_1843_);
goto v___jp_1839_;
}
else
{
lean_object* v_fst_1848_; 
v_fst_1848_ = lean_ctor_get(v_snd_1843_, 0);
lean_inc(v_fst_1848_);
if (lean_obj_tag(v_fst_1848_) == 0)
{
lean_dec_ref_known(v_fst_1844_, 1);
lean_del_object(v___x_1846_);
lean_dec(v_snd_1843_);
goto v___jp_1839_;
}
else
{
lean_object* v_snd_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1875_; 
lean_del_object(v___x_1837_);
v_snd_1849_ = lean_ctor_get(v_snd_1843_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_snd_1843_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v_snd_1843_, 0);
lean_dec(v_unused_1876_);
v___x_1851_ = v_snd_1843_;
v_isShared_1852_ = v_isSharedCheck_1875_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_snd_1849_);
lean_dec(v_snd_1843_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1875_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_val_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1874_; 
v_val_1853_ = lean_ctor_get(v_fst_1844_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_fst_1844_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1855_ = v_fst_1844_;
v_isShared_1856_ = v_isSharedCheck_1874_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_val_1853_);
lean_dec(v_fst_1844_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1874_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_val_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1873_; 
v_val_1857_ = lean_ctor_get(v_fst_1848_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_fst_1848_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1859_ = v_fst_1848_;
v_isShared_1860_ = v_isSharedCheck_1873_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_val_1857_);
lean_dec(v_fst_1848_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1873_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v_val_1857_);
v___x_1862_ = v___x_1851_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_val_1857_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_snd_1849_);
v___x_1862_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1862_);
lean_ctor_set(v___x_1846_, 0, v_val_1853_);
v___x_1864_ = v___x_1846_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_val_1853_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1864_);
v___x_1866_ = v___x_1859_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1866_);
v___x_1868_ = v___x_1855_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
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
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_a_1879_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1834_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1834_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1887_, lean_object* v_inv_1888_, lean_object* v_xs_1889_, lean_object* v_letMuts_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1887_, v_inv_1888_, v_xs_1889_, v_letMuts_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec_ref(v_vcs_1887_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_1897_, lean_object* v_a_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1898_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_1905_, lean_object* v_a_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_1905_, v_a_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_MVarId_getDecl(v_m_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v_userName_1921_; lean_object* v_lctx_1922_; lean_object* v_type_1923_; lean_object* v_localInstances_1924_; uint8_t v_kind_1925_; lean_object* v_numScopeArgs_1926_; lean_object* v___x_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_userName_1921_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_userName_1921_);
v_lctx_1922_ = lean_ctor_get(v_a_1920_, 1);
lean_inc_ref(v_lctx_1922_);
v_type_1923_ = lean_ctor_get(v_a_1920_, 2);
lean_inc_ref(v_type_1923_);
v_localInstances_1924_ = lean_ctor_get(v_a_1920_, 4);
lean_inc_ref(v_localInstances_1924_);
v_kind_1925_ = lean_ctor_get_uint8(v_a_1920_, sizeof(void*)*7);
v_numScopeArgs_1926_ = lean_ctor_get(v_a_1920_, 5);
lean_inc(v_numScopeArgs_1926_);
lean_dec(v_a_1920_);
v___x_1927_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1922_, v_localInstances_1924_, v_type_1923_, v_kind_1925_, v_userName_1921_, v_numScopeArgs_1926_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1936_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = l_Lean_Expr_mvarId_x21(v_a_1928_);
lean_dec(v_a_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1927_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1919_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1919_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_1960_){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = l_String_instInhabitedSlice;
v___x_1962_ = lean_panic_fn_borrowed(v___x_1961_, v_msg_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_1963_, lean_object* v_a_1964_, uint8_t v_b_1965_){
_start:
{
lean_object* v_str_1966_; lean_object* v_startInclusive_1967_; lean_object* v_endExclusive_1968_; lean_object* v___x_1969_; uint8_t v_decide_1970_; 
v_str_1966_ = lean_ctor_get(v_s_1963_, 0);
v_startInclusive_1967_ = lean_ctor_get(v_s_1963_, 1);
v_endExclusive_1968_ = lean_ctor_get(v_s_1963_, 2);
v___x_1969_ = lean_nat_sub(v_endExclusive_1968_, v_startInclusive_1967_);
v_decide_1970_ = lean_nat_dec_eq(v_a_1964_, v___x_1969_);
lean_dec(v___x_1969_);
if (v_decide_1970_ == 0)
{
uint32_t v___x_1971_; lean_object* v___x_1972_; uint32_t v___x_1973_; uint8_t v___x_1974_; 
v___x_1971_ = 64;
v___x_1972_ = lean_nat_add(v_startInclusive_1967_, v_a_1964_);
lean_dec(v_a_1964_);
v___x_1973_ = lean_string_utf8_get_fast(v_str_1966_, v___x_1972_);
v___x_1974_ = lean_uint32_dec_eq(v___x_1973_, v___x_1971_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_string_utf8_next_fast(v_str_1966_, v___x_1972_);
lean_dec(v___x_1972_);
v___x_1976_ = lean_nat_sub(v___x_1975_, v_startInclusive_1967_);
v_a_1964_ = v___x_1976_;
v_b_1965_ = v___x_1974_;
goto _start;
}
else
{
lean_dec(v___x_1972_);
return v___x_1974_;
}
}
else
{
lean_dec(v_a_1964_);
return v_b_1965_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object* v_s_1978_, lean_object* v_a_1979_, lean_object* v_b_1980_){
_start:
{
uint8_t v_b_boxed_1981_; uint8_t v_res_1982_; lean_object* v_r_1983_; 
v_b_boxed_1981_ = lean_unbox(v_b_1980_);
v_res_1982_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1978_, v_a_1979_, v_b_boxed_1981_);
lean_dec_ref(v_s_1978_);
v_r_1983_ = lean_box(v_res_1982_);
return v_r_1983_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_1984_){
_start:
{
lean_object* v_searcher_1985_; uint8_t v___x_1986_; uint8_t v___x_1987_; 
v_searcher_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = 0;
v___x_1987_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1984_, v_searcher_1985_, v___x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_1988_){
_start:
{
uint8_t v_res_1989_; lean_object* v_r_1990_; 
v_res_1989_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_1988_);
lean_dec_ref(v_s_1988_);
v_r_1990_ = lean_box(v_res_1989_);
return v_r_1990_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1994_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_1995_ = lean_unsigned_to_nat(14u);
v___x_1996_ = lean_unsigned_to_nat(22u);
v___x_1997_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_1998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_1999_ = l_mkPanicMessageWithDecl(v___x_1998_, v___x_1997_, v___x_1996_, v___x_1995_, v___x_1994_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_2000_){
_start:
{
switch(lean_obj_tag(v_x_2000_))
{
case 1:
{
lean_object* v_info_2001_; lean_object* v_kind_2002_; lean_object* v_args_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2013_; 
v_info_2001_ = lean_ctor_get(v_x_2000_, 0);
v_kind_2002_ = lean_ctor_get(v_x_2000_, 1);
v_args_2003_ = lean_ctor_get(v_x_2000_, 2);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_x_2000_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2005_ = v_x_2000_;
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_args_2003_);
lean_inc(v_kind_2002_);
lean_inc(v_info_2001_);
lean_dec(v_x_2000_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
size_t v_sz_2007_; size_t v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v_sz_2007_ = lean_array_size(v_args_2003_);
v___x_2008_ = ((size_t)0ULL);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_2007_, v___x_2008_, v_args_2003_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 2, v___x_2009_);
v___x_2011_ = v___x_2005_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_info_2001_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_kind_2002_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
case 3:
{
lean_object* v_info_2014_; lean_object* v_rawVal_2015_; lean_object* v_val_2016_; lean_object* v_preresolved_2017_; uint8_t v___y_2019_; lean_object* v_str_2032_; lean_object* v_startPos_2033_; lean_object* v_stopPos_2034_; uint8_t v___y_2036_; uint8_t v___x_2042_; uint8_t v___y_2044_; uint8_t v___x_2045_; 
v_info_2014_ = lean_ctor_get(v_x_2000_, 0);
v_rawVal_2015_ = lean_ctor_get(v_x_2000_, 1);
v_val_2016_ = lean_ctor_get(v_x_2000_, 2);
v_preresolved_2017_ = lean_ctor_get(v_x_2000_, 3);
v_str_2032_ = lean_ctor_get(v_rawVal_2015_, 0);
v_startPos_2033_ = lean_ctor_get(v_rawVal_2015_, 1);
v_stopPos_2034_ = lean_ctor_get(v_rawVal_2015_, 2);
v___x_2042_ = lean_string_is_valid_pos(v_str_2032_, v_startPos_2033_);
v___x_2045_ = lean_string_is_valid_pos(v_str_2032_, v_stopPos_2034_);
if (v___x_2045_ == 0)
{
v___y_2044_ = v___x_2045_;
goto v___jp_2043_;
}
else
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_nat_dec_le(v_startPos_2033_, v_stopPos_2034_);
v___y_2044_ = v___x_2046_;
goto v___jp_2043_;
}
v___jp_2018_:
{
if (v___y_2019_ == 0)
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2027_; 
lean_inc(v_preresolved_2017_);
lean_inc(v_val_2016_);
lean_inc_ref(v_rawVal_2015_);
lean_inc(v_info_2014_);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_x_2000_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; 
v_unused_2028_ = lean_ctor_get(v_x_2000_, 3);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_x_2000_, 2);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_x_2000_, 1);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_x_2000_, 0);
lean_dec(v_unused_2031_);
v___x_2021_ = v_x_2000_;
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v_x_2000_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = l_Lean_Name_eraseMacroScopes(v_val_2016_);
lean_dec(v_val_2016_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 2, v___x_2023_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_info_2014_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_rawVal_2015_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2026_, 3, v_preresolved_2017_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
else
{
return v_x_2000_;
}
}
v___jp_2035_:
{
if (v___y_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2037_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_2038_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_2037_);
v___x_2039_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2038_);
lean_dec_ref(v___x_2038_);
v___y_2019_ = v___x_2039_;
goto v___jp_2018_;
}
else
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
lean_inc(v_stopPos_2034_);
lean_inc(v_startPos_2033_);
lean_inc_ref(v_str_2032_);
v___x_2040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2040_, 0, v_str_2032_);
lean_ctor_set(v___x_2040_, 1, v_startPos_2033_);
lean_ctor_set(v___x_2040_, 2, v_stopPos_2034_);
v___x_2041_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2040_);
lean_dec_ref_known(v___x_2040_, 3);
v___y_2019_ = v___x_2041_;
goto v___jp_2018_;
}
}
v___jp_2043_:
{
if (v___x_2042_ == 0)
{
v___y_2036_ = v___x_2042_;
goto v___jp_2035_;
}
else
{
v___y_2036_ = v___y_2044_;
goto v___jp_2035_;
}
}
}
default: 
{
return v_x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_2047_, size_t v_i_2048_, lean_object* v_bs_2049_){
_start:
{
uint8_t v___x_2050_; 
v___x_2050_ = lean_usize_dec_lt(v_i_2048_, v_sz_2047_);
if (v___x_2050_ == 0)
{
return v_bs_2049_;
}
else
{
lean_object* v_v_2051_; lean_object* v___x_2052_; lean_object* v_bs_x27_2053_; lean_object* v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v_v_2051_ = lean_array_uget(v_bs_2049_, v_i_2048_);
v___x_2052_ = lean_unsigned_to_nat(0u);
v_bs_x27_2053_ = lean_array_uset(v_bs_2049_, v_i_2048_, v___x_2052_);
v___x_2054_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_2051_);
v___x_2055_ = ((size_t)1ULL);
v___x_2056_ = lean_usize_add(v_i_2048_, v___x_2055_);
v___x_2057_ = lean_array_uset(v_bs_x27_2053_, v_i_2048_, v___x_2054_);
v_i_2048_ = v___x_2056_;
v_bs_2049_ = v___x_2057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2059_, lean_object* v_i_2060_, lean_object* v_bs_2061_){
_start:
{
size_t v_sz_boxed_2062_; size_t v_i_boxed_2063_; lean_object* v_res_2064_; 
v_sz_boxed_2062_ = lean_unbox_usize(v_sz_2059_);
lean_dec(v_sz_2059_);
v_i_boxed_2063_ = lean_unbox_usize(v_i_2060_);
lean_dec(v_i_2060_);
v_res_2064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2062_, v_i_boxed_2063_, v_bs_2061_);
return v_res_2064_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2065_, lean_object* v_inst_2066_, lean_object* v_R_2067_, lean_object* v_a_2068_, uint8_t v_b_2069_, lean_object* v_c_2070_){
_start:
{
uint8_t v___x_2071_; 
v___x_2071_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2065_, v_a_2068_, v_b_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2072_, lean_object* v_inst_2073_, lean_object* v_R_2074_, lean_object* v_a_2075_, lean_object* v_b_2076_, lean_object* v_c_2077_){
_start:
{
uint8_t v_b_boxed_2078_; uint8_t v_res_2079_; lean_object* v_r_2080_; 
v_b_boxed_2078_ = lean_unbox(v_b_2076_);
v_res_2079_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2072_, v_inst_2073_, v_R_2074_, v_a_2075_, v_b_boxed_2078_, v_c_2077_);
lean_dec_ref(v_s_2072_);
v_r_2080_ = lean_box(v_res_2079_);
return v_r_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2081_, lean_object* v_h__1_2082_, lean_object* v_h__2_2083_, lean_object* v_h__3_2084_, lean_object* v_h__4_2085_){
_start:
{
switch(lean_obj_tag(v_x_2081_))
{
case 0:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec(v_h__3_2084_);
lean_dec(v_h__2_2083_);
lean_dec(v_h__1_2082_);
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_apply_1(v_h__4_2085_, v___x_2086_);
return v___x_2087_;
}
case 1:
{
lean_object* v_info_2088_; lean_object* v_kind_2089_; lean_object* v_args_2090_; lean_object* v___x_2091_; 
lean_dec(v_h__4_2085_);
lean_dec(v_h__3_2084_);
lean_dec(v_h__1_2082_);
v_info_2088_ = lean_ctor_get(v_x_2081_, 0);
lean_inc(v_info_2088_);
v_kind_2089_ = lean_ctor_get(v_x_2081_, 1);
lean_inc(v_kind_2089_);
v_args_2090_ = lean_ctor_get(v_x_2081_, 2);
lean_inc_ref(v_args_2090_);
lean_dec_ref_known(v_x_2081_, 3);
v___x_2091_ = lean_apply_3(v_h__2_2083_, v_info_2088_, v_kind_2089_, v_args_2090_);
return v___x_2091_;
}
case 2:
{
lean_object* v_info_2092_; lean_object* v_val_2093_; lean_object* v___x_2094_; 
lean_dec(v_h__4_2085_);
lean_dec(v_h__2_2083_);
lean_dec(v_h__1_2082_);
v_info_2092_ = lean_ctor_get(v_x_2081_, 0);
lean_inc(v_info_2092_);
v_val_2093_ = lean_ctor_get(v_x_2081_, 1);
lean_inc_ref(v_val_2093_);
lean_dec_ref_known(v_x_2081_, 2);
v___x_2094_ = lean_apply_2(v_h__3_2084_, v_info_2092_, v_val_2093_);
return v___x_2094_;
}
default: 
{
lean_object* v_info_2095_; lean_object* v_rawVal_2096_; lean_object* v_val_2097_; lean_object* v_preresolved_2098_; lean_object* v___x_2099_; 
lean_dec(v_h__4_2085_);
lean_dec(v_h__3_2084_);
lean_dec(v_h__2_2083_);
v_info_2095_ = lean_ctor_get(v_x_2081_, 0);
lean_inc(v_info_2095_);
v_rawVal_2096_ = lean_ctor_get(v_x_2081_, 1);
lean_inc_ref(v_rawVal_2096_);
v_val_2097_ = lean_ctor_get(v_x_2081_, 2);
lean_inc(v_val_2097_);
v_preresolved_2098_ = lean_ctor_get(v_x_2081_, 3);
lean_inc(v_preresolved_2098_);
lean_dec_ref_known(v_x_2081_, 4);
v___x_2099_ = lean_apply_4(v_h__1_2082_, v_info_2095_, v_rawVal_2096_, v_val_2097_, v_preresolved_2098_);
return v___x_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2100_, lean_object* v_x_2101_, lean_object* v_h__1_2102_, lean_object* v_h__2_2103_, lean_object* v_h__3_2104_, lean_object* v_h__4_2105_){
_start:
{
switch(lean_obj_tag(v_x_2101_))
{
case 0:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec(v_h__3_2104_);
lean_dec(v_h__2_2103_);
lean_dec(v_h__1_2102_);
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_apply_1(v_h__4_2105_, v___x_2106_);
return v___x_2107_;
}
case 1:
{
lean_object* v_info_2108_; lean_object* v_kind_2109_; lean_object* v_args_2110_; lean_object* v___x_2111_; 
lean_dec(v_h__4_2105_);
lean_dec(v_h__3_2104_);
lean_dec(v_h__1_2102_);
v_info_2108_ = lean_ctor_get(v_x_2101_, 0);
lean_inc(v_info_2108_);
v_kind_2109_ = lean_ctor_get(v_x_2101_, 1);
lean_inc(v_kind_2109_);
v_args_2110_ = lean_ctor_get(v_x_2101_, 2);
lean_inc_ref(v_args_2110_);
lean_dec_ref_known(v_x_2101_, 3);
v___x_2111_ = lean_apply_3(v_h__2_2103_, v_info_2108_, v_kind_2109_, v_args_2110_);
return v___x_2111_;
}
case 2:
{
lean_object* v_info_2112_; lean_object* v_val_2113_; lean_object* v___x_2114_; 
lean_dec(v_h__4_2105_);
lean_dec(v_h__2_2103_);
lean_dec(v_h__1_2102_);
v_info_2112_ = lean_ctor_get(v_x_2101_, 0);
lean_inc(v_info_2112_);
v_val_2113_ = lean_ctor_get(v_x_2101_, 1);
lean_inc_ref(v_val_2113_);
lean_dec_ref_known(v_x_2101_, 2);
v___x_2114_ = lean_apply_2(v_h__3_2104_, v_info_2112_, v_val_2113_);
return v___x_2114_;
}
default: 
{
lean_object* v_info_2115_; lean_object* v_rawVal_2116_; lean_object* v_val_2117_; lean_object* v_preresolved_2118_; lean_object* v___x_2119_; 
lean_dec(v_h__4_2105_);
lean_dec(v_h__3_2104_);
lean_dec(v_h__2_2103_);
v_info_2115_ = lean_ctor_get(v_x_2101_, 0);
lean_inc(v_info_2115_);
v_rawVal_2116_ = lean_ctor_get(v_x_2101_, 1);
lean_inc_ref(v_rawVal_2116_);
v_val_2117_ = lean_ctor_get(v_x_2101_, 2);
lean_inc(v_val_2117_);
v_preresolved_2118_ = lean_ctor_get(v_x_2101_, 3);
lean_inc(v_preresolved_2118_);
lean_dec_ref_known(v_x_2101_, 4);
v___x_2119_ = lean_apply_4(v_h__1_2102_, v_info_2115_, v_rawVal_2116_, v_val_2117_, v_preresolved_2118_);
return v___x_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2120_, lean_object* v_h__1_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_apply_2(v_h__1_2121_, v_x_2120_, lean_box(0));
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2123_, lean_object* v_P_2124_, lean_object* v_motive_2125_, lean_object* v_x_2126_, lean_object* v_h__1_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_apply_2(v_h__1_2127_, v_x_2126_, lean_box(0));
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2131_, lean_object* v_syn_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2134_, lean_object* v_syn_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2134_, v_syn_2135_);
lean_dec(v_name_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2143_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2171_ = lean_unsigned_to_nat(2u);
v___x_2172_ = l_Lean_Expr_isAppOfArity(v_e_2143_, v___x_2170_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2174_ = lean_unsigned_to_nat(3u);
v___x_2175_ = l_Lean_Expr_isAppOfArity(v_e_2143_, v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2177_ = l_Lean_Expr_isAppOfArity(v_e_2143_, v___x_2176_, v___x_2174_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2179_ = l_Lean_Expr_isAppOfArity(v_e_2143_, v___x_2178_, v___x_2174_);
if (v___x_2179_ == 0)
{
goto v___jp_2144_;
}
else
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Expr_appArg_x21(v_e_2143_);
if (lean_obj_tag(v___x_2180_) == 6)
{
lean_object* v_binderName_2181_; lean_object* v_binderType_2182_; lean_object* v_body_2183_; uint8_t v_binderInfo_2184_; lean_object* v___x_2185_; 
lean_dec_ref(v_e_2143_);
v_binderName_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_binderName_2181_);
v_binderType_2182_ = lean_ctor_get(v___x_2180_, 1);
lean_inc_ref(v_binderType_2182_);
v_body_2183_ = lean_ctor_get(v___x_2180_, 2);
lean_inc_ref(v_body_2183_);
v_binderInfo_2184_ = lean_ctor_get_uint8(v___x_2180_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_2180_, 3);
v___x_2185_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2183_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_dec_ref(v_binderType_2182_);
lean_dec(v_binderName_2181_);
return v___x_2185_;
}
else
{
lean_object* v_val_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2203_; 
v_val_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2203_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_val_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2203_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_fst_2190_; lean_object* v_snd_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2202_; 
v_fst_2190_ = lean_ctor_get(v_val_2186_, 0);
v_snd_2191_ = lean_ctor_get(v_val_2186_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_val_2186_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2193_ = v_val_2186_;
v_isShared_2194_ = v_isSharedCheck_2202_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_snd_2191_);
lean_inc(v_fst_2190_);
lean_dec(v_val_2186_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2202_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = l_Lean_mkForall(v_binderName_2181_, v_binderInfo_2184_, v_binderType_2182_, v_snd_2191_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 1, v___x_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_fst_2190_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2199_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2197_);
v___x_2199_ = v___x_2188_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2180_);
goto v___jp_2144_;
}
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = l_Lean_Expr_appFn_x21(v_e_2143_);
v___x_2205_ = l_Lean_Expr_appArg_x21(v___x_2204_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2205_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_dec_ref(v_e_2143_);
return v___x_2206_;
}
else
{
lean_object* v_val_2207_; lean_object* v_snd_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v_snd_2208_ = lean_ctor_get(v_val_2207_, 1);
lean_inc(v_snd_2208_);
lean_dec(v_val_2207_);
v___x_2209_ = l_Lean_Expr_appArg_x21(v_e_2143_);
lean_dec_ref(v_e_2143_);
v___x_2210_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2209_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_dec(v_snd_2208_);
return v___x_2210_;
}
else
{
lean_object* v_val_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2228_; 
v_val_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2228_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_val_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2228_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_fst_2215_; lean_object* v_snd_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2227_; 
v_fst_2215_ = lean_ctor_get(v_val_2211_, 0);
v_snd_2216_ = lean_ctor_get(v_val_2211_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_val_2211_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2218_ = v_val_2211_;
v_isShared_2219_ = v_isSharedCheck_2227_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_snd_2216_);
lean_inc(v_fst_2215_);
lean_dec(v_val_2211_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2227_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = l_Lean_mkOr(v_snd_2208_, v_snd_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_fst_2215_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2222_);
v___x_2224_ = v___x_2213_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
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
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = l_Lean_Expr_appFn_x21(v_e_2143_);
v___x_2230_ = l_Lean_Expr_appArg_x21(v___x_2229_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_dec_ref(v_e_2143_);
return v___x_2231_;
}
else
{
lean_object* v_val_2232_; lean_object* v_snd_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_val_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_val_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v_snd_2233_ = lean_ctor_get(v_val_2232_, 1);
lean_inc(v_snd_2233_);
lean_dec(v_val_2232_);
v___x_2234_ = l_Lean_Expr_appArg_x21(v_e_2143_);
lean_dec_ref(v_e_2143_);
v___x_2235_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2234_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_dec(v_snd_2233_);
return v___x_2235_;
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2253_; 
v_val_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2253_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_val_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2253_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_fst_2240_; lean_object* v_snd_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2252_; 
v_fst_2240_ = lean_ctor_get(v_val_2236_, 0);
v_snd_2241_ = lean_ctor_get(v_val_2236_, 1);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_val_2236_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2243_ = v_val_2236_;
v_isShared_2244_ = v_isSharedCheck_2252_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_snd_2241_);
lean_inc(v_fst_2240_);
lean_dec(v_val_2236_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2252_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = l_Lean_mkAnd(v_snd_2233_, v_snd_2241_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2245_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_fst_2240_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2247_);
v___x_2249_ = v___x_2238_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
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
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2254_ = lean_box(0);
v___x_2255_ = l_Lean_Expr_getAppFn(v_e_2143_);
v___x_2256_ = l_Lean_Expr_constLevels_x21(v___x_2255_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = l_List_get_x21Internal___redArg(v___x_2254_, v___x_2256_, v___x_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2260_ = l_Lean_Expr_getAppNumArgs(v_e_2143_);
v___x_2261_ = lean_nat_sub(v___x_2260_, v___x_2259_);
lean_dec(v___x_2260_);
v___x_2262_ = lean_nat_sub(v___x_2261_, v___x_2259_);
lean_dec(v___x_2261_);
v___x_2263_ = l_Lean_Expr_getRevArg_x21(v_e_2143_, v___x_2262_);
lean_dec_ref(v_e_2143_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2258_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
v___jp_2144_:
{
if (lean_obj_tag(v_e_2143_) == 8)
{
lean_object* v_declName_2145_; lean_object* v_type_2146_; lean_object* v_value_2147_; lean_object* v_body_2148_; uint8_t v_nondep_2149_; lean_object* v___x_2150_; 
v_declName_2145_ = lean_ctor_get(v_e_2143_, 0);
lean_inc(v_declName_2145_);
v_type_2146_ = lean_ctor_get(v_e_2143_, 1);
lean_inc_ref(v_type_2146_);
v_value_2147_ = lean_ctor_get(v_e_2143_, 2);
lean_inc_ref(v_value_2147_);
v_body_2148_ = lean_ctor_get(v_e_2143_, 3);
lean_inc_ref(v_body_2148_);
v_nondep_2149_ = lean_ctor_get_uint8(v_e_2143_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2143_, 4);
v___x_2150_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2148_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref(v_value_2147_);
lean_dec_ref(v_type_2146_);
lean_dec(v_declName_2145_);
return v___x_2150_;
}
else
{
lean_object* v_val_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2168_; 
v_val_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2168_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_val_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2168_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_fst_2155_; lean_object* v_snd_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2167_; 
v_fst_2155_ = lean_ctor_get(v_val_2151_, 0);
v_snd_2156_ = lean_ctor_get(v_val_2151_, 1);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_val_2151_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2158_ = v_val_2151_;
v_isShared_2159_ = v_isSharedCheck_2167_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_snd_2156_);
lean_inc(v_fst_2155_);
lean_dec(v_val_2151_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2167_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = l_Lean_Expr_letE___override(v_declName_2145_, v_type_2146_, v_value_2147_, v_snd_2156_, v_nondep_2149_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 1, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_fst_2155_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2162_);
v___x_2164_ = v___x_2153_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
else
{
lean_object* v___x_2169_; 
lean_dec_ref(v_e_2143_);
v___x_2169_ = lean_box(0);
return v___x_2169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2266_){
_start:
{
lean_object* v___x_2267_; 
lean_inc_ref(v_e_2266_);
v___x_2267_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
return v_e_2266_;
}
else
{
lean_object* v_val_2268_; lean_object* v_fst_2269_; lean_object* v_snd_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec_ref(v_e_2266_);
v_val_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_val_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v_fst_2269_ = lean_ctor_get(v_val_2268_, 0);
lean_inc_n(v_fst_2269_, 2);
v_snd_2270_ = lean_ctor_get(v_val_2268_, 1);
lean_inc(v_snd_2270_);
lean_dec(v_val_2268_);
v___x_2271_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2269_);
v___x_2272_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2269_, v___x_2271_, v_snd_2270_);
return v___x_2272_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Array_mkArray0(lean_box(0));
return v___x_2283_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2322_ = l_String_toRawSubstring_x27(v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2339_ = l_String_toRawSubstring_x27(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2354_, lean_object* v_default_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2361_; lean_object* v_handlers_2362_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2362_ = l_Lean_Syntax_SepArray_ofElems(v___x_2361_, v_handlers_2354_);
switch(lean_obj_tag(v_default_2355_))
{
case 0:
{
lean_object* v_ref_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_ref_2363_ = lean_ctor_get(v_a_2358_, 4);
v___x_2364_ = 0;
v___x_2365_ = l_Lean_SourceInfo_fromRef(v_ref_2363_, v___x_2364_);
v___x_2366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2365_, 3);
v___x_2368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2365_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2370_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2371_ = l_Array_append___redArg(v___x_2370_, v_handlers_2362_);
lean_dec_ref(v_handlers_2362_);
v___x_2372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2365_);
lean_ctor_set(v___x_2372_, 1, v___x_2369_);
lean_ctor_set(v___x_2372_, 2, v___x_2371_);
v___x_2373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2365_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_Lean_Syntax_node3(v___x_2365_, v___x_2366_, v___x_2368_, v___x_2372_, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
case 1:
{
lean_object* v_toCold_2377_; lean_object* v_ref_2378_; lean_object* v_currMacroScope_2379_; lean_object* v_quotContext_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_toCold_2377_ = lean_ctor_get(v_a_2358_, 0);
v_ref_2378_ = lean_ctor_get(v_a_2358_, 4);
v_currMacroScope_2379_ = lean_ctor_get(v_a_2358_, 9);
v_quotContext_2380_ = lean_ctor_get(v_toCold_2377_, 2);
v___x_2381_ = 0;
v___x_2382_ = l_Lean_SourceInfo_fromRef(v_ref_2378_, v___x_2381_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2382_, 12);
v___x_2385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2382_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2382_);
lean_ctor_set(v___x_2391_, 1, v___x_2389_);
v___x_2392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2382_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2396_ = l_Array_append___redArg(v___x_2395_, v_handlers_2362_);
lean_dec_ref(v_handlers_2362_);
v___x_2397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2382_);
lean_ctor_set(v___x_2397_, 1, v___x_2361_);
v___x_2398_ = lean_array_push(v___x_2396_, v___x_2397_);
v___x_2399_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2379_);
lean_inc(v_quotContext_2380_);
v___x_2401_ = l_Lean_addMacroScope(v_quotContext_2380_, v___x_2400_, v_currMacroScope_2379_);
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2403_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2382_);
lean_ctor_set(v___x_2403_, 1, v___x_2399_);
lean_ctor_set(v___x_2403_, 2, v___x_2401_);
lean_ctor_set(v___x_2403_, 3, v___x_2402_);
v___x_2404_ = lean_array_push(v___x_2398_, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2382_);
lean_ctor_set(v___x_2405_, 1, v___x_2388_);
lean_ctor_set(v___x_2405_, 2, v___x_2404_);
v___x_2406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2382_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = l_Lean_Syntax_node3(v___x_2382_, v___x_2392_, v___x_2394_, v___x_2405_, v___x_2407_);
v___x_2409_ = l_Lean_Syntax_node2(v___x_2382_, v___x_2390_, v___x_2391_, v___x_2408_);
v___x_2410_ = l_Lean_Syntax_node1(v___x_2382_, v___x_2388_, v___x_2409_);
v___x_2411_ = l_Lean_Syntax_node1(v___x_2382_, v___x_2387_, v___x_2410_);
v___x_2412_ = l_Lean_Syntax_node1(v___x_2382_, v___x_2386_, v___x_2411_);
v___x_2413_ = l_Lean_Syntax_node2(v___x_2382_, v___x_2383_, v___x_2385_, v___x_2412_);
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
case 2:
{
lean_object* v_toCold_2415_; lean_object* v_ref_2416_; lean_object* v_currMacroScope_2417_; lean_object* v_quotContext_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_toCold_2415_ = lean_ctor_get(v_a_2358_, 0);
v_ref_2416_ = lean_ctor_get(v_a_2358_, 4);
v_currMacroScope_2417_ = lean_ctor_get(v_a_2358_, 9);
v_quotContext_2418_ = lean_ctor_get(v_toCold_2415_, 2);
v___x_2419_ = 0;
v___x_2420_ = l_Lean_SourceInfo_fromRef(v_ref_2416_, v___x_2419_);
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2420_, 12);
v___x_2423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2420_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2420_);
lean_ctor_set(v___x_2429_, 1, v___x_2427_);
v___x_2430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2420_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2434_ = l_Array_append___redArg(v___x_2433_, v_handlers_2362_);
lean_dec_ref(v_handlers_2362_);
v___x_2435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2420_);
lean_ctor_set(v___x_2435_, 1, v___x_2361_);
v___x_2436_ = lean_array_push(v___x_2434_, v___x_2435_);
v___x_2437_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
lean_inc(v_currMacroScope_2417_);
lean_inc(v_quotContext_2418_);
v___x_2439_ = l_Lean_addMacroScope(v_quotContext_2418_, v___x_2438_, v_currMacroScope_2417_);
v___x_2440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
v___x_2441_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2420_);
lean_ctor_set(v___x_2441_, 1, v___x_2437_);
lean_ctor_set(v___x_2441_, 2, v___x_2439_);
lean_ctor_set(v___x_2441_, 3, v___x_2440_);
v___x_2442_ = lean_array_push(v___x_2436_, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2420_);
lean_ctor_set(v___x_2443_, 1, v___x_2426_);
lean_ctor_set(v___x_2443_, 2, v___x_2442_);
v___x_2444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2420_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = l_Lean_Syntax_node3(v___x_2420_, v___x_2430_, v___x_2432_, v___x_2443_, v___x_2445_);
v___x_2447_ = l_Lean_Syntax_node2(v___x_2420_, v___x_2428_, v___x_2429_, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_node1(v___x_2420_, v___x_2426_, v___x_2447_);
v___x_2449_ = l_Lean_Syntax_node1(v___x_2420_, v___x_2425_, v___x_2448_);
v___x_2450_ = l_Lean_Syntax_node1(v___x_2420_, v___x_2424_, v___x_2449_);
v___x_2451_ = l_Lean_Syntax_node2(v___x_2420_, v___x_2421_, v___x_2423_, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
return v___x_2452_;
}
default: 
{
lean_object* v_e_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_e_2453_ = lean_ctor_get(v_default_2355_, 0);
lean_inc_ref(v_e_2453_);
lean_dec_ref_known(v_default_2355_, 1);
v___x_2454_ = lean_box(1);
v___x_2455_ = l_Lean_PrettyPrinter_delab(v_e_2453_, v___x_2454_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2492_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2492_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2492_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_ref_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
v_ref_2460_ = lean_ctor_get(v_a_2358_, 4);
v___x_2461_ = 0;
v___x_2462_ = l_Lean_SourceInfo_fromRef(v_ref_2460_, v___x_2461_);
v___x_2463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2462_, 11);
v___x_2465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2462_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2462_);
lean_ctor_set(v___x_2471_, 1, v___x_2469_);
v___x_2472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2462_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2476_ = l_Array_append___redArg(v___x_2475_, v_handlers_2362_);
lean_dec_ref(v_handlers_2362_);
v___x_2477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2462_);
lean_ctor_set(v___x_2477_, 1, v___x_2361_);
v___x_2478_ = lean_array_push(v___x_2476_, v___x_2477_);
v___x_2479_ = lean_array_push(v___x_2478_, v_a_2456_);
v___x_2480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2462_);
lean_ctor_set(v___x_2480_, 1, v___x_2468_);
lean_ctor_set(v___x_2480_, 2, v___x_2479_);
v___x_2481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2462_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = l_Lean_Syntax_node3(v___x_2462_, v___x_2472_, v___x_2474_, v___x_2480_, v___x_2482_);
v___x_2484_ = l_Lean_Syntax_node2(v___x_2462_, v___x_2470_, v___x_2471_, v___x_2483_);
v___x_2485_ = l_Lean_Syntax_node1(v___x_2462_, v___x_2468_, v___x_2484_);
v___x_2486_ = l_Lean_Syntax_node1(v___x_2462_, v___x_2467_, v___x_2485_);
v___x_2487_ = l_Lean_Syntax_node1(v___x_2462_, v___x_2466_, v___x_2486_);
v___x_2488_ = l_Lean_Syntax_node2(v___x_2462_, v___x_2463_, v___x_2465_, v___x_2487_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2488_);
v___x_2490_ = v___x_2458_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
else
{
lean_dec_ref(v_handlers_2362_);
return v___x_2455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2493_, lean_object* v_default_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2493_, v_default_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec_ref(v_handlers_2493_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = l_Lean_Expr_hasMVar(v_e_2501_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_e_2501_);
return v___x_2505_;
}
else
{
lean_object* v___x_2506_; lean_object* v_mctx_2507_; lean_object* v___x_2508_; lean_object* v_fst_2509_; lean_object* v_snd_2510_; lean_object* v___x_2511_; lean_object* v_cache_2512_; lean_object* v_zetaDeltaFVarIds_2513_; lean_object* v_postponed_2514_; lean_object* v_diag_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2524_; 
v___x_2506_ = lean_st_ref_get(v___y_2502_);
v_mctx_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc_ref(v_mctx_2507_);
lean_dec(v___x_2506_);
v___x_2508_ = l_Lean_instantiateMVarsCore(v_mctx_2507_, v_e_2501_);
v_fst_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_fst_2509_);
v_snd_2510_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_snd_2510_);
lean_dec_ref(v___x_2508_);
v___x_2511_ = lean_st_ref_take(v___y_2502_);
v_cache_2512_ = lean_ctor_get(v___x_2511_, 1);
v_zetaDeltaFVarIds_2513_ = lean_ctor_get(v___x_2511_, 2);
v_postponed_2514_ = lean_ctor_get(v___x_2511_, 3);
v_diag_2515_ = lean_ctor_get(v___x_2511_, 4);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; 
v_unused_2525_ = lean_ctor_get(v___x_2511_, 0);
lean_dec(v_unused_2525_);
v___x_2517_ = v___x_2511_;
v_isShared_2518_ = v_isSharedCheck_2524_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_diag_2515_);
lean_inc(v_postponed_2514_);
lean_inc(v_zetaDeltaFVarIds_2513_);
lean_inc(v_cache_2512_);
lean_dec(v___x_2511_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2524_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v_snd_2510_);
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_snd_2510_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_cache_2512_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_zetaDeltaFVarIds_2513_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_postponed_2514_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_diag_2515_);
v___x_2520_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_st_ref_put(v___y_2502_, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_fst_2509_);
return v___x_2522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2526_, v___y_2527_);
lean_dec(v___y_2527_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2530_, v___y_2536_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
lean_inc(v___y_2556_);
lean_inc_ref(v___y_2555_);
lean_inc(v___y_2554_);
lean_inc_ref(v___y_2553_);
v___x_2562_ = lean_apply_9(v_x_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, lean_box(0));
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2574_, lean_object* v_x_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___f_2585_; lean_object* v___x_2586_; 
lean_inc(v___y_2579_);
lean_inc_ref(v___y_2578_);
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2576_);
v___f_2585_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2585_, 0, v_x_2575_);
lean_closure_set(v___f_2585_, 1, v___y_2576_);
lean_closure_set(v___f_2585_, 2, v___y_2577_);
lean_closure_set(v___f_2585_, 3, v___y_2578_);
lean_closure_set(v___f_2585_, 4, v___y_2579_);
v___x_2586_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2574_, v___f_2585_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2586_) == 0)
{
return v___x_2586_;
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2595_, lean_object* v_x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2595_, v_x_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2607_, lean_object* v_mvarId_2608_, lean_object* v_x_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2608_, v_x_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2620_, lean_object* v_mvarId_2621_, lean_object* v_x_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2620_, v_mvarId_2621_, v_x_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2633_, lean_object* v_inv_2634_, lean_object* v_xs_2635_, uint8_t v___x_2636_, lean_object* v___x_2637_, lean_object* v_letMuts_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
lean_inc_ref(v_letMuts_2638_);
lean_inc_ref(v_xs_2635_);
v___x_2648_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2633_, v_inv_2634_, v_xs_2635_, v_letMuts_2638_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2725_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2725_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2725_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
if (lean_obj_tag(v_a_2649_) == 1)
{
lean_object* v_val_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2720_; 
lean_del_object(v___x_2651_);
v_val_2653_ = lean_ctor_get(v_a_2649_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_a_2649_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2655_ = v_a_2649_;
v_isShared_2656_ = v_isSharedCheck_2720_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_val_2653_);
lean_dec(v_a_2649_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2720_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_snd_2657_; lean_object* v_fst_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2719_; 
v_snd_2657_ = lean_ctor_get(v_val_2653_, 1);
v_fst_2658_ = lean_ctor_get(v_val_2653_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_val_2653_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2660_ = v_val_2653_;
v_isShared_2661_ = v_isSharedCheck_2719_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2657_);
lean_inc(v_fst_2658_);
lean_dec(v_val_2653_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2719_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_fst_2662_; lean_object* v_snd_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2718_; 
v_fst_2662_ = lean_ctor_get(v_snd_2657_, 0);
v_snd_2663_ = lean_ctor_get(v_snd_2657_, 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_snd_2657_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2665_ = v_snd_2657_;
v_isShared_2666_ = v_isSharedCheck_2718_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_snd_2663_);
lean_inc(v_fst_2662_);
lean_dec(v_snd_2657_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2718_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v_lvl_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; uint8_t v___x_2677_; lean_object* v___x_2678_; 
v_lvl_2667_ = lean_ctor_get(v_fst_2658_, 0);
lean_inc(v_lvl_2667_);
v___x_2668_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2658_);
lean_inc(v_fst_2662_);
v___x_2669_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2662_);
v___x_2670_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2667_, v___x_2668_, v___x_2669_);
v___x_2671_ = lean_unsigned_to_nat(2u);
v___x_2672_ = lean_mk_empty_array_with_capacity(v___x_2671_);
v___x_2673_ = lean_array_push(v___x_2672_, v_xs_2635_);
lean_inc_ref(v_letMuts_2638_);
v___x_2674_ = lean_array_push(v___x_2673_, v_letMuts_2638_);
v___x_2675_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2670_);
v___x_2676_ = 0;
v___x_2677_ = 1;
v___x_2678_ = l_Lean_Meta_mkLambdaFVars(v___x_2674_, v___x_2675_, v___x_2676_, v___x_2636_, v___x_2676_, v___x_2636_, v___x_2677_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec_ref(v___x_2674_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v_letMutsPred_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v_letMutsPred_2680_ = lean_ctor_get(v_fst_2662_, 2);
lean_inc_ref(v_letMutsPred_2680_);
lean_dec(v_fst_2662_);
v___x_2681_ = lean_mk_empty_array_with_capacity(v___x_2637_);
v___x_2682_ = lean_array_push(v___x_2681_, v_letMuts_2638_);
v___x_2683_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2680_);
v___x_2684_ = l_Lean_Meta_mkLambdaFVars(v___x_2682_, v___x_2683_, v___x_2676_, v___x_2636_, v___x_2676_, v___x_2636_, v___x_2677_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec_ref(v___x_2682_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2701_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2701_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2701_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v_a_2685_);
v___x_2690_ = v___x_2665_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2685_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_snd_2663_);
v___x_2690_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2692_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2690_);
lean_ctor_set(v___x_2660_, 0, v_a_2679_);
v___x_2692_ = v___x_2660_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2679_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2694_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2692_);
v___x_2694_ = v___x_2655_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2696_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2694_);
v___x_2696_ = v___x_2687_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec(v_a_2679_);
lean_del_object(v___x_2665_);
lean_dec(v_snd_2663_);
lean_del_object(v___x_2660_);
lean_del_object(v___x_2655_);
v_a_2702_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2684_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2684_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_del_object(v___x_2665_);
lean_dec(v_snd_2663_);
lean_dec(v_fst_2662_);
lean_del_object(v___x_2660_);
lean_del_object(v___x_2655_);
lean_dec_ref(v_letMuts_2638_);
v_a_2710_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2678_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2678_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
lean_dec(v_a_2649_);
lean_dec_ref(v_letMuts_2638_);
lean_dec_ref(v_xs_2635_);
v___x_2721_ = lean_box(0);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2721_);
v___x_2723_ = v___x_2651_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec_ref(v_letMuts_2638_);
lean_dec_ref(v_xs_2635_);
v_a_2726_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2648_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2648_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2734_, lean_object* v_inv_2735_, lean_object* v_xs_2736_, lean_object* v___x_2737_, lean_object* v___x_2738_, lean_object* v_letMuts_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v___x_76920__boxed_2749_; lean_object* v_res_2750_; 
v___x_76920__boxed_2749_ = lean_unbox(v___x_2737_);
v_res_2750_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2734_, v_inv_2735_, v_xs_2736_, v___x_76920__boxed_2749_, v___x_2738_, v_letMuts_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___x_2738_);
lean_dec_ref(v_a_2734_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v_b_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; 
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2754_);
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
v___x_2762_ = lean_apply_10(v_k_2751_, v_b_2756_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, lean_box(0));
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v_b_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2775_, uint8_t v_bi_2776_, lean_object* v_type_2777_, lean_object* v_k_2778_, uint8_t v_kind_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v___f_2789_; lean_object* v___x_2790_; 
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
v___f_2789_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2789_, 0, v_k_2778_);
lean_closure_set(v___f_2789_, 1, v___y_2780_);
lean_closure_set(v___f_2789_, 2, v___y_2781_);
lean_closure_set(v___f_2789_, 3, v___y_2782_);
lean_closure_set(v___f_2789_, 4, v___y_2783_);
v___x_2790_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2775_, v_bi_2776_, v_type_2777_, v___f_2789_, v_kind_2779_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2790_) == 0)
{
return v___x_2790_;
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2799_, lean_object* v_bi_2800_, lean_object* v_type_2801_, lean_object* v_k_2802_, lean_object* v_kind_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
uint8_t v_bi_boxed_2813_; uint8_t v_kind_boxed_2814_; lean_object* v_res_2815_; 
v_bi_boxed_2813_ = lean_unbox(v_bi_2800_);
v_kind_boxed_2814_ = lean_unbox(v_kind_2803_);
v_res_2815_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2799_, v_bi_boxed_2813_, v_type_2801_, v_k_2802_, v_kind_boxed_2814_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2816_, lean_object* v_type_2817_, lean_object* v_k_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
uint8_t v___x_2828_; uint8_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = 0;
v___x_2829_ = 0;
v___x_2830_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2816_, v___x_2828_, v_type_2817_, v_k_2818_, v___x_2829_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2831_, lean_object* v_type_2832_, lean_object* v_k_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2831_, v_type_2832_, v_k_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2847_, lean_object* v_inv_2848_, uint8_t v___x_2849_, lean_object* v___x_2850_, lean_object* v_arg_2851_, lean_object* v_xs_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; lean_object* v___f_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2862_ = lean_box(v___x_2849_);
v___f_2863_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2863_, 0, v_a_2847_);
lean_closure_set(v___f_2863_, 1, v_inv_2848_);
lean_closure_set(v___f_2863_, 2, v_xs_2852_);
lean_closure_set(v___f_2863_, 3, v___x_2862_);
lean_closure_set(v___f_2863_, 4, v___x_2850_);
v___x_2864_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2865_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2864_, v_arg_2851_, v___f_2863_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2866_, lean_object* v_inv_2867_, lean_object* v___x_2868_, lean_object* v___x_2869_, lean_object* v_arg_2870_, lean_object* v_xs_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
uint8_t v___x_77240__boxed_2881_; lean_object* v_res_2882_; 
v___x_77240__boxed_2881_ = lean_unbox(v___x_2868_);
v_res_2882_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2866_, v_inv_2867_, v___x_77240__boxed_2881_, v___x_2869_, v_arg_2870_, v_xs_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2882_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2886_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = lean_unsigned_to_nat(32u);
v___x_2890_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2892_, lean_object* v_r_2893_, uint8_t v___x_2894_, lean_object* v___x_2895_, lean_object* v___x_2896_, lean_object* v_xs_2897_, lean_object* v_fst_2898_, lean_object* v_fst_2899_, lean_object* v_letMuts_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; 
lean_inc_ref(v_fst_2892_);
v___x_2910_ = l_Lean_Meta_mkNone(v_fst_2892_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2912_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_2913_ = lean_unsigned_to_nat(2u);
v___x_2914_ = lean_mk_empty_array_with_capacity(v___x_2913_);
lean_inc_ref(v___x_2914_);
v___x_2915_ = lean_array_push(v___x_2914_, v_a_2911_);
lean_inc_ref(v_letMuts_2900_);
v___x_2916_ = lean_array_push(v___x_2915_, v_letMuts_2900_);
v___x_2917_ = l_Lean_Meta_mkAppM(v___x_2912_, v___x_2916_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2919_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v___x_2919_ = l_Lean_Meta_mkSome(v_fst_2892_, v_r_2893_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
lean_inc_ref(v___x_2914_);
v___x_2921_ = lean_array_push(v___x_2914_, v_a_2920_);
v___x_2922_ = lean_array_push(v___x_2921_, v_letMuts_2900_);
v___x_2923_ = l_Lean_Meta_mkAppM(v___x_2912_, v___x_2922_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2908_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2908_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2929_ = lean_unsigned_to_nat(100000u);
v___x_2930_ = 0;
v___x_2931_ = 0;
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2933_, 0, v___x_2929_);
lean_ctor_set(v___x_2933_, 1, v___x_2913_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 1, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 2, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 3, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 4, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 5, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 6, v___x_2931_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 7, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 8, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 9, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 10, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 11, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 12, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 13, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 14, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 15, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 16, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 17, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 18, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 19, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 20, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 21, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 22, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 23, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 24, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 25, v___x_2894_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 26, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 27, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 28, v___x_2930_);
v___x_2934_ = lean_mk_empty_array_with_capacity(v___x_2895_);
lean_inc_ref(v___x_2934_);
v___x_2935_ = lean_array_push(v___x_2934_, v_a_2926_);
v___x_2936_ = l_Lean_Options_empty;
v___x_2937_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2933_, v___x_2935_, v_a_2928_, v___x_2936_, v___y_2905_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2939_ = lean_mk_empty_array_with_capacity(v___x_2896_);
v___x_2940_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2941_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2939_, v___x_2940_, v___x_2930_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; size_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc_n(v_a_2942_, 2);
lean_dec_ref_known(v___x_2941_, 1);
v___x_2943_ = lean_array_push(v___x_2914_, v_xs_2897_);
v___x_2944_ = lean_array_push(v___x_2943_, v_a_2918_);
v___x_2945_ = l_Lean_Expr_beta(v_fst_2898_, v___x_2944_);
v___x_2946_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2896_, 2);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___x_2896_);
v___x_2948_ = lean_unsigned_to_nat(32u);
v___x_2949_ = lean_mk_empty_array_with_capacity(v___x_2948_);
v___x_2950_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2951_ = ((size_t)5ULL);
v___x_2952_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2949_);
lean_ctor_set(v___x_2952_, 2, v___x_2896_);
lean_ctor_set(v___x_2952_, 3, v___x_2896_);
lean_ctor_set_usize(v___x_2952_, 4, v___x_2951_);
v___x_2953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2946_);
lean_ctor_set(v___x_2953_, 1, v___x_2946_);
lean_ctor_set(v___x_2953_, 2, v___x_2946_);
lean_ctor_set(v___x_2953_, 3, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2947_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
lean_inc(v_a_2938_);
v___x_2955_ = l_Lean_Meta_simp(v___x_2945_, v_a_2938_, v_a_2942_, v___x_2932_, v___x_2954_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v_fst_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v_fst_2957_ = lean_ctor_get(v_a_2956_, 0);
lean_inc(v_fst_2957_);
lean_dec(v_a_2956_);
v___x_2958_ = lean_array_push(v___x_2934_, v_a_2924_);
v___x_2959_ = l_Lean_Expr_beta(v_fst_2899_, v___x_2958_);
v___x_2960_ = l_Lean_Meta_simp(v___x_2959_, v_a_2938_, v_a_2942_, v___x_2932_, v___x_2954_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec_ref_known(v___x_2954_, 2);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v_fst_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2999_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v_fst_2962_ = lean_ctor_get(v_a_2961_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_a_2961_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v_a_2961_, 1);
lean_dec(v_unused_3000_);
v___x_2964_ = v_a_2961_;
v_isShared_2965_ = v_isSharedCheck_2999_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_fst_2962_);
lean_dec(v_a_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2999_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v_expr_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_expr_2966_ = lean_ctor_get(v_fst_2957_, 0);
lean_inc_ref(v_expr_2966_);
lean_dec(v_fst_2957_);
v___x_2967_ = lean_box(1);
v___x_2968_ = l_Lean_PrettyPrinter_delab(v_expr_2966_, v___x_2967_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v_expr_2970_; lean_object* v___x_2971_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v_expr_2970_ = lean_ctor_get(v_fst_2962_, 0);
lean_inc_ref(v_expr_2970_);
lean_dec(v_fst_2962_);
v___x_2971_ = l_Lean_PrettyPrinter_delab(v_expr_2970_, v___x_2967_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2982_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2982_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2982_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 1, v_a_2972_);
lean_ctor_set(v___x_2964_, 0, v_a_2969_);
v___x_2977_ = v___x_2964_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2969_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2979_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2977_);
v___x_2979_ = v___x_2974_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_a_2969_);
lean_del_object(v___x_2964_);
v_a_2983_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2971_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2971_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_del_object(v___x_2964_);
lean_dec(v_fst_2962_);
v_a_2991_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2968_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2968_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v_fst_2957_);
v_a_3001_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2960_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2960_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref_known(v___x_2954_, 2);
lean_dec(v_a_2942_);
lean_dec(v_a_2938_);
lean_dec_ref(v___x_2934_);
lean_dec(v_a_2924_);
lean_dec_ref(v_fst_2899_);
v_a_3009_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2955_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2955_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec(v_a_2938_);
lean_dec_ref(v___x_2934_);
lean_dec(v_a_2924_);
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2914_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_fst_2898_);
lean_dec_ref(v_xs_2897_);
lean_dec(v___x_2896_);
v_a_3017_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_2941_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_2941_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v___x_2934_);
lean_dec(v_a_2924_);
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2914_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_fst_2898_);
lean_dec_ref(v_xs_2897_);
lean_dec(v___x_2896_);
v_a_3025_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2937_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2937_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_a_2926_);
lean_dec(v_a_2924_);
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2914_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_fst_2898_);
lean_dec_ref(v_xs_2897_);
lean_dec(v___x_2896_);
v_a_3033_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_2927_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_2927_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v_a_2924_);
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2914_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_fst_2898_);
lean_dec_ref(v_xs_2897_);
lean_dec(v___x_2896_);
v_a_3041_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_2925_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_2925_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2914_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_fst_2898_);
lean_dec_ref(v_xs_2897_);
lean_dec(v___x_2896_);
v_a_3049_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_2923_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_2923_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2914_);
lean_dec_ref(v_letMuts_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_fst_2898_);
lean_dec_ref(v_xs_2897_);
lean_dec(v___x_2896_);
v_a_3057_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_2919_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_2919_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref(v___x_2914_);
lean_dec_ref(v_letMuts_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_fst_2898_);
lean_dec_ref(v_xs_2897_);
lean_dec(v___x_2896_);
lean_dec_ref(v_r_2893_);
lean_dec_ref(v_fst_2892_);
v_a_3065_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_2917_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_2917_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v_letMuts_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_fst_2898_);
lean_dec_ref(v_xs_2897_);
lean_dec(v___x_2896_);
lean_dec_ref(v_r_2893_);
lean_dec_ref(v_fst_2892_);
v_a_3073_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_2910_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_2910_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3081_ = _args[0];
lean_object* v_r_3082_ = _args[1];
lean_object* v___x_3083_ = _args[2];
lean_object* v___x_3084_ = _args[3];
lean_object* v___x_3085_ = _args[4];
lean_object* v_xs_3086_ = _args[5];
lean_object* v_fst_3087_ = _args[6];
lean_object* v_fst_3088_ = _args[7];
lean_object* v_letMuts_3089_ = _args[8];
lean_object* v___y_3090_ = _args[9];
lean_object* v___y_3091_ = _args[10];
lean_object* v___y_3092_ = _args[11];
lean_object* v___y_3093_ = _args[12];
lean_object* v___y_3094_ = _args[13];
lean_object* v___y_3095_ = _args[14];
lean_object* v___y_3096_ = _args[15];
lean_object* v___y_3097_ = _args[16];
lean_object* v___y_3098_ = _args[17];
_start:
{
uint8_t v___x_77313__boxed_3099_; lean_object* v_res_3100_; 
v___x_77313__boxed_3099_ = lean_unbox(v___x_3083_);
v_res_3100_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3081_, v_r_3082_, v___x_77313__boxed_3099_, v___x_3084_, v___x_3085_, v_xs_3086_, v_fst_3087_, v_fst_3088_, v_letMuts_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___x_3084_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3101_, uint8_t v___x_3102_, lean_object* v___x_3103_, lean_object* v___x_3104_, lean_object* v_xs_3105_, lean_object* v_fst_3106_, lean_object* v_fst_3107_, lean_object* v_snd_3108_, lean_object* v_r_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v___f_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3119_ = lean_box(v___x_3102_);
v___f_3120_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3120_, 0, v_fst_3101_);
lean_closure_set(v___f_3120_, 1, v_r_3109_);
lean_closure_set(v___f_3120_, 2, v___x_3119_);
lean_closure_set(v___f_3120_, 3, v___x_3103_);
lean_closure_set(v___f_3120_, 4, v___x_3104_);
lean_closure_set(v___f_3120_, 5, v_xs_3105_);
lean_closure_set(v___f_3120_, 6, v_fst_3106_);
lean_closure_set(v___f_3120_, 7, v_fst_3107_);
v___x_3121_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3122_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3121_, v_snd_3108_, v___f_3120_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3123_ = _args[0];
lean_object* v___x_3124_ = _args[1];
lean_object* v___x_3125_ = _args[2];
lean_object* v___x_3126_ = _args[3];
lean_object* v_xs_3127_ = _args[4];
lean_object* v_fst_3128_ = _args[5];
lean_object* v_fst_3129_ = _args[6];
lean_object* v_snd_3130_ = _args[7];
lean_object* v_r_3131_ = _args[8];
lean_object* v___y_3132_ = _args[9];
lean_object* v___y_3133_ = _args[10];
lean_object* v___y_3134_ = _args[11];
lean_object* v___y_3135_ = _args[12];
lean_object* v___y_3136_ = _args[13];
lean_object* v___y_3137_ = _args[14];
lean_object* v___y_3138_ = _args[15];
lean_object* v___y_3139_ = _args[16];
lean_object* v___y_3140_ = _args[17];
_start:
{
uint8_t v___x_77709__boxed_3141_; lean_object* v_res_3142_; 
v___x_77709__boxed_3141_ = lean_unbox(v___x_3124_);
v_res_3142_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3123_, v___x_77709__boxed_3141_, v___x_3125_, v___x_3126_, v_xs_3127_, v_fst_3128_, v_fst_3129_, v_snd_3130_, v_r_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3146_, uint8_t v___x_3147_, lean_object* v___x_3148_, lean_object* v___x_3149_, lean_object* v_fst_3150_, lean_object* v_fst_3151_, lean_object* v_snd_3152_, lean_object* v_xs_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3163_ = lean_box(v___x_3147_);
lean_inc_ref(v_fst_3146_);
v___f_3164_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3164_, 0, v_fst_3146_);
lean_closure_set(v___f_3164_, 1, v___x_3163_);
lean_closure_set(v___f_3164_, 2, v___x_3148_);
lean_closure_set(v___f_3164_, 3, v___x_3149_);
lean_closure_set(v___f_3164_, 4, v_xs_3153_);
lean_closure_set(v___f_3164_, 5, v_fst_3150_);
lean_closure_set(v___f_3164_, 6, v_fst_3151_);
lean_closure_set(v___f_3164_, 7, v_snd_3152_);
v___x_3165_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3166_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3165_, v_fst_3146_, v___f_3164_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3167_ = _args[0];
lean_object* v___x_3168_ = _args[1];
lean_object* v___x_3169_ = _args[2];
lean_object* v___x_3170_ = _args[3];
lean_object* v_fst_3171_ = _args[4];
lean_object* v_fst_3172_ = _args[5];
lean_object* v_snd_3173_ = _args[6];
lean_object* v_xs_3174_ = _args[7];
lean_object* v___y_3175_ = _args[8];
lean_object* v___y_3176_ = _args[9];
lean_object* v___y_3177_ = _args[10];
lean_object* v___y_3178_ = _args[11];
lean_object* v___y_3179_ = _args[12];
lean_object* v___y_3180_ = _args[13];
lean_object* v___y_3181_ = _args[14];
lean_object* v___y_3182_ = _args[15];
lean_object* v___y_3183_ = _args[16];
_start:
{
uint8_t v___x_77772__boxed_3184_; lean_object* v_res_3185_; 
v___x_77772__boxed_3184_ = lean_unbox(v___x_3168_);
v_res_3185_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3167_, v___x_77772__boxed_3184_, v___x_3169_, v___x_3170_, v_fst_3171_, v_fst_3172_, v_snd_3173_, v_xs_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3186_, size_t v_sz_3187_, size_t v_i_3188_, lean_object* v_b_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_usize_dec_lt(v_i_3188_, v_sz_3187_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_b_3189_);
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; lean_object* v_a_3198_; lean_object* v___x_3199_; 
v___x_3197_ = lean_box(1);
v_a_3198_ = lean_array_uget_borrowed(v_as_3186_, v_i_3188_);
lean_inc(v_a_3198_);
v___x_3199_ = l_Lean_PrettyPrinter_delab(v_a_3198_, v___x_3197_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; size_t v___x_3202_; size_t v___x_3203_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = lean_array_push(v_b_3189_, v_a_3200_);
v___x_3202_ = ((size_t)1ULL);
v___x_3203_ = lean_usize_add(v_i_3188_, v___x_3202_);
v_i_3188_ = v___x_3203_;
v_b_3189_ = v___x_3201_;
goto _start;
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v_b_3189_);
v_a_3205_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3199_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3199_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3213_, lean_object* v_sz_3214_, lean_object* v_i_3215_, lean_object* v_b_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
size_t v_sz_boxed_3222_; size_t v_i_boxed_3223_; lean_object* v_res_3224_; 
v_sz_boxed_3222_ = lean_unbox_usize(v_sz_3214_);
lean_dec(v_sz_3214_);
v_i_boxed_3223_ = lean_unbox_usize(v_i_3215_);
lean_dec(v_i_3215_);
v_res_3224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3213_, v_sz_boxed_3222_, v_i_boxed_3223_, v_b_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec_ref(v_as_3213_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3245_, lean_object* v_fst_3246_, lean_object* v_snd_3247_, lean_object* v___x_3248_, lean_object* v___x_3249_, lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v___x_3255_, uint8_t v___x_3256_, lean_object* v_letMuts_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3267_ = lean_unsigned_to_nat(2u);
v___x_3268_ = lean_mk_empty_array_with_capacity(v___x_3267_);
v___x_3269_ = lean_array_push(v___x_3268_, v_xs_3245_);
v___x_3270_ = lean_array_push(v___x_3269_, v_letMuts_3257_);
v___x_3271_ = l_Lean_Expr_beta(v_fst_3246_, v___x_3270_);
v___x_3272_ = lean_box(1);
v___x_3273_ = l_Lean_PrettyPrinter_delab(v___x_3271_, v___x_3272_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3413_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3276_ = v___x_3273_;
v_isShared_3277_ = v_isSharedCheck_3413_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3413_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
uint8_t v___y_3279_; lean_object* v_points_3316_; lean_object* v_default_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3412_; 
v_points_3316_ = lean_ctor_get(v_snd_3247_, 0);
v_default_3317_ = lean_ctor_get(v_snd_3247_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_snd_3247_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3319_ = v_snd_3247_;
v_isShared_3320_ = v_isSharedCheck_3412_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_default_3317_);
lean_inc(v_points_3316_);
lean_dec(v_snd_3247_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3412_;
goto v_resetjp_3318_;
}
v___jp_3278_:
{
lean_object* v_toCold_3280_; lean_object* v_ref_3281_; lean_object* v_currMacroScope_3282_; lean_object* v_quotContext_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3314_; 
v_toCold_3280_ = lean_ctor_get(v___y_3264_, 0);
v_ref_3281_ = lean_ctor_get(v___y_3264_, 4);
v_currMacroScope_3282_ = lean_ctor_get(v___y_3264_, 9);
v_quotContext_3283_ = lean_ctor_get(v_toCold_3280_, 2);
v___x_3284_ = l_Lean_SourceInfo_fromRef(v_ref_3281_, v___y_3279_);
v___x_3285_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3286_ = l_Lean_Name_mkStr3(v___x_3254_, v___x_3255_, v___x_3285_);
v___x_3287_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3288_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3284_, 11);
v___x_3289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3284_);
lean_ctor_set(v___x_3289_, 1, v___x_3287_);
lean_ctor_set(v___x_3289_, 2, v___x_3288_);
v___x_3290_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3284_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3284_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_String_toRawSubstring_x27(v___x_3248_);
lean_inc_n(v_currMacroScope_3282_, 2);
lean_inc_n(v_quotContext_3283_, 2);
v___x_3297_ = l_Lean_addMacroScope(v_quotContext_3283_, v___x_3249_, v_currMacroScope_3282_);
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3284_);
lean_ctor_set(v___x_3299_, 1, v___x_3296_);
lean_ctor_set(v___x_3299_, 2, v___x_3297_);
lean_ctor_set(v___x_3299_, 3, v___x_3298_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3284_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l_String_toRawSubstring_x27(v___x_3250_);
v___x_3303_ = l_Lean_addMacroScope(v_quotContext_3283_, v___x_3251_, v_currMacroScope_3282_);
v___x_3304_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3284_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
lean_ctor_set(v___x_3304_, 2, v___x_3303_);
lean_ctor_set(v___x_3304_, 3, v___x_3298_);
v___x_3305_ = l_Lean_Syntax_node3(v___x_3284_, v___x_3292_, v___x_3299_, v___x_3301_, v___x_3304_);
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3284_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_Syntax_node3(v___x_3284_, v___x_3293_, v___x_3295_, v___x_3305_, v___x_3307_);
v___x_3309_ = l_Lean_Syntax_node1(v___x_3284_, v___x_3292_, v___x_3308_);
v___x_3310_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3284_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = l_Lean_Syntax_node5(v___x_3284_, v___x_3286_, v___x_3289_, v___x_3291_, v___x_3309_, v___x_3311_, v_a_3274_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3312_);
v___x_3314_ = v___x_3276_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
v_resetjp_3318_:
{
uint8_t v___y_3322_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3373_ = lean_array_get_size(v_points_3316_);
v___x_3374_ = lean_nat_dec_eq(v___x_3373_, v___x_3253_);
if (v___x_3374_ == 0)
{
lean_del_object(v___x_3276_);
lean_dec_ref(v___x_3255_);
lean_dec_ref(v___x_3254_);
v___y_3322_ = v___x_3374_;
goto v___jp_3321_;
}
else
{
if (lean_obj_tag(v_default_3317_) == 3)
{
uint8_t v___x_3375_; 
lean_del_object(v___x_3276_);
lean_dec_ref(v___x_3255_);
lean_dec_ref(v___x_3254_);
v___x_3375_ = 0;
v___y_3322_ = v___x_3375_;
goto v___jp_3321_;
}
else
{
lean_del_object(v___x_3319_);
lean_dec_ref(v_points_3316_);
if (lean_obj_tag(v_default_3317_) == 2)
{
if (v___x_3256_ == 0)
{
v___y_3279_ = v___x_3256_;
goto v___jp_3278_;
}
else
{
lean_object* v_toCold_3376_; lean_object* v_ref_3377_; lean_object* v_currMacroScope_3378_; lean_object* v_quotContext_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_del_object(v___x_3276_);
v_toCold_3376_ = lean_ctor_get(v___y_3264_, 0);
v_ref_3377_ = lean_ctor_get(v___y_3264_, 4);
v_currMacroScope_3378_ = lean_ctor_get(v___y_3264_, 9);
v_quotContext_3379_ = lean_ctor_get(v_toCold_3376_, 2);
v___x_3380_ = 0;
v___x_3381_ = l_Lean_SourceInfo_fromRef(v_ref_3377_, v___x_3380_);
v___x_3382_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3383_ = l_Lean_Name_mkStr3(v___x_3254_, v___x_3255_, v___x_3382_);
v___x_3384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3385_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3381_, 11);
v___x_3386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3381_);
lean_ctor_set(v___x_3386_, 1, v___x_3384_);
lean_ctor_set(v___x_3386_, 2, v___x_3385_);
v___x_3387_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3381_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3381_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = l_String_toRawSubstring_x27(v___x_3248_);
lean_inc_n(v_currMacroScope_3378_, 2);
lean_inc_n(v_quotContext_3379_, 2);
v___x_3394_ = l_Lean_addMacroScope(v_quotContext_3379_, v___x_3249_, v_currMacroScope_3378_);
v___x_3395_ = lean_box(0);
v___x_3396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3381_);
lean_ctor_set(v___x_3396_, 1, v___x_3393_);
lean_ctor_set(v___x_3396_, 2, v___x_3394_);
lean_ctor_set(v___x_3396_, 3, v___x_3395_);
v___x_3397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3381_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = l_String_toRawSubstring_x27(v___x_3250_);
v___x_3400_ = l_Lean_addMacroScope(v_quotContext_3379_, v___x_3251_, v_currMacroScope_3378_);
v___x_3401_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3381_);
lean_ctor_set(v___x_3401_, 1, v___x_3399_);
lean_ctor_set(v___x_3401_, 2, v___x_3400_);
lean_ctor_set(v___x_3401_, 3, v___x_3395_);
v___x_3402_ = l_Lean_Syntax_node3(v___x_3381_, v___x_3389_, v___x_3396_, v___x_3398_, v___x_3401_);
v___x_3403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3381_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
v___x_3405_ = l_Lean_Syntax_node3(v___x_3381_, v___x_3390_, v___x_3392_, v___x_3402_, v___x_3404_);
v___x_3406_ = l_Lean_Syntax_node1(v___x_3381_, v___x_3389_, v___x_3405_);
v___x_3407_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3381_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = l_Lean_Syntax_node5(v___x_3381_, v___x_3383_, v___x_3386_, v___x_3388_, v___x_3406_, v___x_3408_, v_a_3274_);
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
}
else
{
uint8_t v___x_3411_; 
lean_dec(v_default_3317_);
v___x_3411_ = 0;
v___y_3279_ = v___x_3411_;
goto v___jp_3278_;
}
}
}
v___jp_3321_:
{
lean_object* v_toCold_3323_; lean_object* v_ref_3324_; lean_object* v_currMacroScope_3325_; lean_object* v_quotContext_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3331_; 
v_toCold_3323_ = lean_ctor_get(v___y_3264_, 0);
v_ref_3324_ = lean_ctor_get(v___y_3264_, 4);
v_currMacroScope_3325_ = lean_ctor_get(v___y_3264_, 9);
v_quotContext_3326_ = lean_ctor_get(v_toCold_3323_, 2);
v___x_3327_ = l_Lean_SourceInfo_fromRef(v_ref_3324_, v___y_3322_);
v___x_3328_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3327_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set_tag(v___x_3319_, 2);
lean_ctor_set(v___x_3319_, 1, v___x_3328_);
lean_ctor_set(v___x_3319_, 0, v___x_3327_);
v___x_3331_ = v___x_3319_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v___x_3328_);
v___x_3331_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; size_t v_sz_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3332_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3327_, 11);
v___x_3336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3327_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_String_toRawSubstring_x27(v___x_3248_);
lean_inc_n(v_currMacroScope_3325_, 2);
lean_inc_n(v_quotContext_3326_, 2);
v___x_3338_ = l_Lean_addMacroScope(v_quotContext_3326_, v___x_3249_, v_currMacroScope_3325_);
v___x_3339_ = lean_box(0);
v___x_3340_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3327_);
lean_ctor_set(v___x_3340_, 1, v___x_3337_);
lean_ctor_set(v___x_3340_, 2, v___x_3338_);
lean_ctor_set(v___x_3340_, 3, v___x_3339_);
v___x_3341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3342_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3327_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = l_String_toRawSubstring_x27(v___x_3250_);
v___x_3344_ = l_Lean_addMacroScope(v_quotContext_3326_, v___x_3251_, v_currMacroScope_3325_);
v___x_3345_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3327_);
lean_ctor_set(v___x_3345_, 1, v___x_3343_);
lean_ctor_set(v___x_3345_, 2, v___x_3344_);
lean_ctor_set(v___x_3345_, 3, v___x_3339_);
v___x_3346_ = l_Lean_Syntax_node3(v___x_3327_, v___x_3333_, v___x_3340_, v___x_3342_, v___x_3345_);
v___x_3347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3327_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = l_Lean_Syntax_node3(v___x_3327_, v___x_3334_, v___x_3336_, v___x_3346_, v___x_3348_);
v___x_3350_ = l_Lean_Syntax_node1(v___x_3327_, v___x_3333_, v___x_3349_);
v___x_3351_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3327_);
lean_ctor_set(v___x_3352_, 1, v___x_3333_);
lean_ctor_set(v___x_3352_, 2, v___x_3351_);
v___x_3353_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3327_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l_Lean_Syntax_node4(v___x_3327_, v___x_3332_, v___x_3350_, v___x_3352_, v___x_3354_, v_a_3274_);
v___x_3356_ = l_Lean_Syntax_node2(v___x_3327_, v___x_3329_, v___x_3331_, v___x_3355_);
v___x_3357_ = lean_mk_empty_array_with_capacity(v___x_3252_);
v___x_3358_ = lean_array_push(v___x_3357_, v___x_3356_);
v_sz_3359_ = lean_array_size(v_points_3316_);
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3316_, v_sz_3359_, v___x_3360_, v___x_3358_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec_ref(v_points_3316_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v___x_3363_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3362_, v_default_3317_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v_a_3362_);
return v___x_3363_;
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec(v_default_3317_);
v_a_3364_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3361_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3361_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
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
lean_dec_ref(v___x_3255_);
lean_dec_ref(v___x_3254_);
lean_dec(v___x_3251_);
lean_dec_ref(v___x_3250_);
lean_dec(v___x_3249_);
lean_dec_ref(v___x_3248_);
lean_dec_ref(v_snd_3247_);
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3414_ = _args[0];
lean_object* v_fst_3415_ = _args[1];
lean_object* v_snd_3416_ = _args[2];
lean_object* v___x_3417_ = _args[3];
lean_object* v___x_3418_ = _args[4];
lean_object* v___x_3419_ = _args[5];
lean_object* v___x_3420_ = _args[6];
lean_object* v___x_3421_ = _args[7];
lean_object* v___x_3422_ = _args[8];
lean_object* v___x_3423_ = _args[9];
lean_object* v___x_3424_ = _args[10];
lean_object* v___x_3425_ = _args[11];
lean_object* v_letMuts_3426_ = _args[12];
lean_object* v___y_3427_ = _args[13];
lean_object* v___y_3428_ = _args[14];
lean_object* v___y_3429_ = _args[15];
lean_object* v___y_3430_ = _args[16];
lean_object* v___y_3431_ = _args[17];
lean_object* v___y_3432_ = _args[18];
lean_object* v___y_3433_ = _args[19];
lean_object* v___y_3434_ = _args[20];
lean_object* v___y_3435_ = _args[21];
_start:
{
uint8_t v___x_77982__boxed_3436_; lean_object* v_res_3437_; 
v___x_77982__boxed_3436_ = lean_unbox(v___x_3425_);
v_res_3437_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3414_, v_fst_3415_, v_snd_3416_, v___x_3417_, v___x_3418_, v___x_3419_, v___x_3420_, v___x_3421_, v___x_3422_, v___x_3423_, v___x_3424_, v___x_77982__boxed_3436_, v_letMuts_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___x_3422_);
lean_dec(v___x_3421_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3438_, lean_object* v_snd_3439_, lean_object* v___x_3440_, lean_object* v___x_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v___x_3444_, lean_object* v___x_3445_, uint8_t v___x_3446_, lean_object* v_arg_3447_, lean_object* v_xs_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; 
v___x_3458_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3459_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3460_ = lean_box(v___x_3446_);
v___f_3461_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3461_, 0, v_xs_3448_);
lean_closure_set(v___f_3461_, 1, v_fst_3438_);
lean_closure_set(v___f_3461_, 2, v_snd_3439_);
lean_closure_set(v___f_3461_, 3, v___x_3440_);
lean_closure_set(v___f_3461_, 4, v___x_3441_);
lean_closure_set(v___f_3461_, 5, v___x_3458_);
lean_closure_set(v___f_3461_, 6, v___x_3459_);
lean_closure_set(v___f_3461_, 7, v___x_3442_);
lean_closure_set(v___f_3461_, 8, v___x_3443_);
lean_closure_set(v___f_3461_, 9, v___x_3444_);
lean_closure_set(v___f_3461_, 10, v___x_3445_);
lean_closure_set(v___f_3461_, 11, v___x_3460_);
v___x_3462_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3459_, v_arg_3447_, v___f_3461_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3463_ = _args[0];
lean_object* v_snd_3464_ = _args[1];
lean_object* v___x_3465_ = _args[2];
lean_object* v___x_3466_ = _args[3];
lean_object* v___x_3467_ = _args[4];
lean_object* v___x_3468_ = _args[5];
lean_object* v___x_3469_ = _args[6];
lean_object* v___x_3470_ = _args[7];
lean_object* v___x_3471_ = _args[8];
lean_object* v_arg_3472_ = _args[9];
lean_object* v_xs_3473_ = _args[10];
lean_object* v___y_3474_ = _args[11];
lean_object* v___y_3475_ = _args[12];
lean_object* v___y_3476_ = _args[13];
lean_object* v___y_3477_ = _args[14];
lean_object* v___y_3478_ = _args[15];
lean_object* v___y_3479_ = _args[16];
lean_object* v___y_3480_ = _args[17];
lean_object* v___y_3481_ = _args[18];
lean_object* v___y_3482_ = _args[19];
_start:
{
uint8_t v___x_78329__boxed_3483_; lean_object* v_res_3484_; 
v___x_78329__boxed_3483_ = lean_unbox(v___x_3471_);
v_res_3484_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3463_, v_snd_3464_, v___x_3465_, v___x_3466_, v___x_3467_, v___x_3468_, v___x_3469_, v___x_3470_, v___x_78329__boxed_3483_, v_arg_3472_, v_xs_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3485_, size_t v_sz_3486_, size_t v_i_3487_, lean_object* v_b_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_usize_dec_lt(v_i_3487_, v_sz_3486_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_b_3488_);
return v___x_3495_;
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_a_3496_ = lean_array_uget_borrowed(v_as_3485_, v_i_3487_);
v___x_3497_ = lean_box(1);
lean_inc(v_a_3496_);
v___x_3498_ = l_Lean_PrettyPrinter_delab(v_a_3496_, v___x_3497_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; size_t v___x_3501_; size_t v___x_3502_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = lean_array_push(v_b_3488_, v_a_3499_);
v___x_3501_ = ((size_t)1ULL);
v___x_3502_ = lean_usize_add(v_i_3487_, v___x_3501_);
v_i_3487_ = v___x_3502_;
v_b_3488_ = v___x_3500_;
goto _start;
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_b_3488_);
v_a_3504_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3498_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3498_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3512_, lean_object* v_sz_3513_, lean_object* v_i_3514_, lean_object* v_b_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
size_t v_sz_boxed_3521_; size_t v_i_boxed_3522_; lean_object* v_res_3523_; 
v_sz_boxed_3521_ = lean_unbox_usize(v_sz_3513_);
lean_dec(v_sz_3513_);
v_i_boxed_3522_ = lean_unbox_usize(v_i_3514_);
lean_dec(v_i_3514_);
v_res_3523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3512_, v_sz_boxed_3521_, v_i_boxed_3522_, v_b_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v_as_3512_);
return v_res_3523_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3532_ = l_String_toRawSubstring_x27(v___x_3531_);
return v___x_3532_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3543_ = l_String_toRawSubstring_x27(v___x_3542_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3548_ = l_String_toRawSubstring_x27(v___x_3547_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3550_ = l_String_toRawSubstring_x27(v___x_3549_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3554_ = l_String_toRawSubstring_x27(v___x_3553_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3559_ = l_String_toRawSubstring_x27(v___x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3569_, lean_object* v___x_3570_, lean_object* v___f_3571_, lean_object* v_a_3572_, lean_object* v_inv_3573_, lean_object* v_arg_3574_, uint8_t v___x_3575_, lean_object* v___x_3576_, lean_object* v___x_3577_, lean_object* v___x_3578_, lean_object* v___x_3579_, lean_object* v___x_3580_, lean_object* v___x_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_a_3592_; lean_object* v___y_3596_; lean_object* v___x_3598_; 
lean_inc_ref(v___x_3570_);
lean_inc(v___x_3569_);
v___x_3598_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3569_, v___x_3570_, v___f_3571_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3572_, v_inv_3573_, v_arg_3574_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
if (lean_obj_tag(v_a_3601_) == 1)
{
lean_object* v_val_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_4087_; 
lean_dec_ref(v_arg_3574_);
v_val_3602_ = lean_ctor_get(v_a_3601_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_3604_ = v_a_3601_;
v_isShared_3605_ = v_isSharedCheck_4087_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_val_3602_);
lean_dec(v_a_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_4087_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
if (lean_obj_tag(v_a_3599_) == 1)
{
lean_object* v_val_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_4009_; 
lean_del_object(v___x_3604_);
v_val_3606_ = lean_ctor_get(v_a_3599_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_a_3599_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3608_ = v_a_3599_;
v_isShared_3609_ = v_isSharedCheck_4009_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_val_3606_);
lean_dec(v_a_3599_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_4009_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v_snd_3610_; lean_object* v_fst_3611_; lean_object* v_snd_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_4008_; 
v_snd_3610_ = lean_ctor_get(v_val_3606_, 1);
lean_inc(v_snd_3610_);
v_fst_3611_ = lean_ctor_get(v_val_3602_, 0);
v_snd_3612_ = lean_ctor_get(v_val_3602_, 1);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_val_3602_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3614_ = v_val_3602_;
v_isShared_3615_ = v_isSharedCheck_4008_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_snd_3612_);
lean_inc(v_fst_3611_);
lean_dec(v_val_3602_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_4008_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v_fst_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_4006_; 
v_fst_3616_ = lean_ctor_get(v_val_3606_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_val_3606_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; 
v_unused_4007_ = lean_ctor_get(v_val_3606_, 1);
lean_dec(v_unused_4007_);
v___x_3618_ = v_val_3606_;
v_isShared_3619_ = v_isSharedCheck_4006_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_fst_3616_);
lean_dec(v_val_3606_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_4006_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v_fst_3620_; lean_object* v_snd_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_4005_; 
v_fst_3620_ = lean_ctor_get(v_snd_3610_, 0);
v_snd_3621_ = lean_ctor_get(v_snd_3610_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_snd_3610_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3623_ = v_snd_3610_;
v_isShared_3624_ = v_isSharedCheck_4005_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_snd_3621_);
lean_inc(v_fst_3620_);
lean_dec(v_snd_3610_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_4005_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; lean_object* v___f_3626_; lean_object* v___x_3627_; 
v___x_3625_ = lean_box(v___x_3575_);
lean_inc(v___x_3577_);
v___f_3626_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3626_, 0, v_fst_3611_);
lean_closure_set(v___f_3626_, 1, v___x_3625_);
lean_closure_set(v___f_3626_, 2, v___x_3576_);
lean_closure_set(v___f_3626_, 3, v___x_3577_);
lean_closure_set(v___f_3626_, 4, v_fst_3616_);
lean_closure_set(v___f_3626_, 5, v_fst_3620_);
lean_closure_set(v___f_3626_, 6, v_snd_3612_);
lean_inc(v___x_3569_);
v___x_3627_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3569_, v___x_3570_, v___f_3626_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v_fst_3629_; lean_object* v_snd_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3996_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
v_fst_3629_ = lean_ctor_get(v_a_3628_, 0);
v_snd_3630_ = lean_ctor_get(v_a_3628_, 1);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_a_3628_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3632_ = v_a_3628_;
v_isShared_3633_ = v_isSharedCheck_3996_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_snd_3630_);
lean_inc(v_fst_3629_);
lean_dec(v_a_3628_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3996_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v_points_3634_; lean_object* v_default_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3995_; 
v_points_3634_ = lean_ctor_get(v_snd_3621_, 0);
v_default_3635_ = lean_ctor_get(v_snd_3621_, 1);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_snd_3621_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3637_ = v_snd_3621_;
v_isShared_3638_ = v_isSharedCheck_3995_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_default_3635_);
lean_inc(v_points_3634_);
lean_dec(v_snd_3621_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3995_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3639_ = lean_array_get_size(v_points_3634_);
v___x_3640_ = lean_nat_dec_eq(v___x_3639_, v___x_3577_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; size_t v_sz_3642_; size_t v___x_3643_; lean_object* v___x_3644_; 
lean_del_object(v___x_3608_);
v___x_3641_ = lean_mk_empty_array_with_capacity(v___x_3577_);
lean_dec(v___x_3577_);
v_sz_3642_ = lean_array_size(v_points_3634_);
v___x_3643_ = ((size_t)0ULL);
v___x_3644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3634_, v_sz_3642_, v___x_3643_, v___x_3641_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec_ref(v_points_3634_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v___x_3646_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3645_, v_default_3635_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v_a_3645_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_toCold_3647_; lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3730_; 
v_toCold_3647_ = lean_ctor_get(v___y_3588_, 0);
lean_inc_ref(v_toCold_3647_);
v_a_3648_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3650_ = v___x_3646_;
v_isShared_3651_ = v_isSharedCheck_3730_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3730_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_ref_3652_; lean_object* v_currMacroScope_3653_; lean_object* v_quotContext_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3664_; 
v_ref_3652_ = lean_ctor_get(v___y_3588_, 4);
lean_inc(v_ref_3652_);
v_currMacroScope_3653_ = lean_ctor_get(v___y_3588_, 9);
lean_inc_n(v_currMacroScope_3653_, 2);
lean_dec_ref(v___y_3588_);
v_quotContext_3654_ = lean_ctor_get(v_toCold_3647_, 2);
lean_inc_n(v_quotContext_3654_, 2);
lean_dec_ref(v_toCold_3647_);
v___x_3655_ = l_Lean_SourceInfo_fromRef(v_ref_3652_, v___x_3640_);
lean_dec(v_ref_3652_);
v___x_3656_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3657_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3658_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3578_);
v___x_3659_ = l_Lean_Name_mkStr2(v___x_3578_, v___x_3658_);
v___x_3660_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3659_, v_currMacroScope_3653_);
v___x_3661_ = l_Lean_Name_mkStr4(v___x_3579_, v___x_3580_, v___x_3578_, v___x_3658_);
v___x_3662_ = lean_box(0);
lean_inc(v___x_3661_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 1);
lean_ctor_set(v___x_3637_, 1, v___x_3662_);
lean_ctor_set(v___x_3637_, 0, v___x_3661_);
v___x_3664_ = v___x_3637_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3661_);
v___x_3666_ = v___x_3650_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3661_);
v___x_3666_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set_tag(v___x_3632_, 1);
lean_ctor_set(v___x_3632_, 1, v___x_3662_);
lean_ctor_set(v___x_3632_, 0, v___x_3666_);
v___x_3668_ = v___x_3632_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v___x_3662_);
v___x_3668_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3670_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set_tag(v___x_3623_, 1);
lean_ctor_set(v___x_3623_, 1, v___x_3668_);
lean_ctor_set(v___x_3623_, 0, v___x_3664_);
v___x_3670_ = v___x_3623_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
lean_inc_n(v___x_3655_, 2);
v___x_3671_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3655_);
lean_ctor_set(v___x_3671_, 1, v___x_3657_);
lean_ctor_set(v___x_3671_, 2, v___x_3660_);
lean_ctor_set(v___x_3671_, 3, v___x_3670_);
v___x_3672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3673_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 2);
lean_ctor_set(v___x_3618_, 1, v___x_3674_);
lean_ctor_set(v___x_3618_, 0, v___x_3655_);
v___x_3676_ = v___x_3618_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3677_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3678_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3653_);
lean_inc(v_quotContext_3654_);
v___x_3679_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3678_, v_currMacroScope_3653_);
lean_inc_n(v___x_3655_, 2);
v___x_3680_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3655_);
lean_ctor_set(v___x_3680_, 1, v___x_3677_);
lean_ctor_set(v___x_3680_, 2, v___x_3679_);
lean_ctor_set(v___x_3680_, 3, v___x_3662_);
v___x_3681_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3615_ == 0)
{
lean_ctor_set_tag(v___x_3614_, 2);
lean_ctor_set(v___x_3614_, 1, v___x_3681_);
lean_ctor_set(v___x_3614_, 0, v___x_3655_);
v___x_3683_ = v___x_3614_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3684_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3685_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3655_, 19);
v___x_3686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3655_);
lean_ctor_set(v___x_3686_, 1, v___x_3684_);
v___x_3687_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3688_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3689_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3653_, 4);
lean_inc_n(v_quotContext_3654_, 4);
v___x_3690_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3689_, v_currMacroScope_3653_);
v___x_3691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3655_);
lean_ctor_set(v___x_3691_, 1, v___x_3688_);
lean_ctor_set(v___x_3691_, 2, v___x_3690_);
lean_ctor_set(v___x_3691_, 3, v___x_3662_);
v___x_3692_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3694_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3693_, v_currMacroScope_3653_);
v___x_3695_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3655_);
lean_ctor_set(v___x_3695_, 1, v___x_3692_);
lean_ctor_set(v___x_3695_, 2, v___x_3694_);
lean_ctor_set(v___x_3695_, 3, v___x_3662_);
lean_inc_ref(v___x_3695_);
v___x_3696_ = l_Lean_Syntax_node2(v___x_3655_, v___x_3672_, v___x_3691_, v___x_3695_);
v___x_3697_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3655_);
lean_ctor_set(v___x_3698_, 1, v___x_3672_);
lean_ctor_set(v___x_3698_, 2, v___x_3697_);
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3655_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
lean_inc_ref(v___x_3700_);
lean_inc_ref(v___x_3698_);
v___x_3701_ = l_Lean_Syntax_node4(v___x_3655_, v___x_3687_, v___x_3696_, v___x_3698_, v___x_3700_, v_snd_3630_);
lean_inc_ref(v___x_3686_);
v___x_3702_ = l_Lean_Syntax_node2(v___x_3655_, v___x_3685_, v___x_3686_, v___x_3701_);
v___x_3703_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3655_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
lean_inc_ref_n(v___x_3704_, 2);
lean_inc_ref_n(v___x_3683_, 2);
lean_inc_ref_n(v___x_3676_, 2);
v___x_3705_ = l_Lean_Syntax_node5(v___x_3655_, v___x_3673_, v___x_3676_, v___x_3680_, v___x_3683_, v___x_3702_, v___x_3704_);
v___x_3706_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3707_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3708_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3707_, v_currMacroScope_3653_);
v___x_3709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3655_);
lean_ctor_set(v___x_3709_, 1, v___x_3706_);
lean_ctor_set(v___x_3709_, 2, v___x_3708_);
lean_ctor_set(v___x_3709_, 3, v___x_3662_);
v___x_3710_ = l_String_toRawSubstring_x27(v___x_3581_);
v___x_3711_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3569_, v_currMacroScope_3653_);
v___x_3712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3655_);
lean_ctor_set(v___x_3712_, 1, v___x_3710_);
lean_ctor_set(v___x_3712_, 2, v___x_3711_);
lean_ctor_set(v___x_3712_, 3, v___x_3662_);
v___x_3713_ = l_Lean_Syntax_node2(v___x_3655_, v___x_3672_, v___x_3712_, v___x_3695_);
v___x_3714_ = l_Lean_Syntax_node4(v___x_3655_, v___x_3687_, v___x_3713_, v___x_3698_, v___x_3700_, v_fst_3629_);
v___x_3715_ = l_Lean_Syntax_node2(v___x_3655_, v___x_3685_, v___x_3686_, v___x_3714_);
v___x_3716_ = l_Lean_Syntax_node5(v___x_3655_, v___x_3673_, v___x_3676_, v___x_3709_, v___x_3683_, v___x_3715_, v___x_3704_);
v___x_3717_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3718_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3719_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3718_, v_currMacroScope_3653_);
v___x_3720_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3655_);
lean_ctor_set(v___x_3720_, 1, v___x_3717_);
lean_ctor_set(v___x_3720_, 2, v___x_3719_);
lean_ctor_set(v___x_3720_, 3, v___x_3662_);
v___x_3721_ = l_Lean_Syntax_node5(v___x_3655_, v___x_3673_, v___x_3676_, v___x_3720_, v___x_3683_, v_a_3648_, v___x_3704_);
v___x_3722_ = l_Lean_Syntax_node3(v___x_3655_, v___x_3672_, v___x_3705_, v___x_3716_, v___x_3721_);
v___x_3723_ = l_Lean_Syntax_node2(v___x_3655_, v___x_3656_, v___x_3671_, v___x_3722_);
v_a_3592_ = v___x_3723_;
goto v___jp_3591_;
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
lean_del_object(v___x_3637_);
lean_del_object(v___x_3632_);
lean_dec(v_snd_3630_);
lean_dec(v_fst_3629_);
lean_del_object(v___x_3623_);
lean_del_object(v___x_3618_);
lean_del_object(v___x_3614_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec_ref(v___x_3578_);
lean_dec(v___x_3569_);
v___y_3596_ = v___x_3646_;
goto v___jp_3595_;
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_del_object(v___x_3637_);
lean_dec(v_default_3635_);
lean_del_object(v___x_3632_);
lean_dec(v_snd_3630_);
lean_dec(v_fst_3629_);
lean_del_object(v___x_3623_);
lean_del_object(v___x_3618_);
lean_del_object(v___x_3614_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec_ref(v___x_3578_);
lean_dec(v___x_3569_);
v_a_3731_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3644_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3644_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_dec_ref(v_points_3634_);
lean_dec(v___x_3577_);
switch(lean_obj_tag(v_default_3635_))
{
case 2:
{
lean_object* v_toCold_3739_; lean_object* v_ref_3740_; lean_object* v_currMacroScope_3741_; lean_object* v_quotContext_3742_; uint8_t v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3753_; 
v_toCold_3739_ = lean_ctor_get(v___y_3588_, 0);
lean_inc_ref(v_toCold_3739_);
v_ref_3740_ = lean_ctor_get(v___y_3588_, 4);
lean_inc(v_ref_3740_);
v_currMacroScope_3741_ = lean_ctor_get(v___y_3588_, 9);
lean_inc_n(v_currMacroScope_3741_, 2);
lean_dec_ref(v___y_3588_);
v_quotContext_3742_ = lean_ctor_get(v_toCold_3739_, 2);
lean_inc_n(v_quotContext_3742_, 2);
lean_dec_ref(v_toCold_3739_);
v___x_3743_ = 0;
v___x_3744_ = l_Lean_SourceInfo_fromRef(v_ref_3740_, v___x_3743_);
lean_dec(v_ref_3740_);
v___x_3745_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3746_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3747_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3578_);
v___x_3748_ = l_Lean_Name_mkStr2(v___x_3578_, v___x_3747_);
v___x_3749_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3748_, v_currMacroScope_3741_);
lean_inc_ref(v___x_3580_);
lean_inc_ref(v___x_3579_);
v___x_3750_ = l_Lean_Name_mkStr4(v___x_3579_, v___x_3580_, v___x_3578_, v___x_3747_);
v___x_3751_ = lean_box(0);
lean_inc(v___x_3750_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 1);
lean_ctor_set(v___x_3637_, 1, v___x_3751_);
lean_ctor_set(v___x_3637_, 0, v___x_3750_);
v___x_3753_ = v___x_3637_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3755_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3750_);
v___x_3755_ = v___x_3608_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3750_);
v___x_3755_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3757_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set_tag(v___x_3632_, 1);
lean_ctor_set(v___x_3632_, 1, v___x_3751_);
lean_ctor_set(v___x_3632_, 0, v___x_3755_);
v___x_3757_ = v___x_3632_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v___x_3751_);
v___x_3757_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set_tag(v___x_3623_, 1);
lean_ctor_set(v___x_3623_, 1, v___x_3757_);
lean_ctor_set(v___x_3623_, 0, v___x_3753_);
v___x_3759_ = v___x_3623_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
lean_inc_n(v___x_3744_, 2);
v___x_3760_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3744_);
lean_ctor_set(v___x_3760_, 1, v___x_3746_);
lean_ctor_set(v___x_3760_, 2, v___x_3749_);
lean_ctor_set(v___x_3760_, 3, v___x_3759_);
v___x_3761_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 2);
lean_ctor_set(v___x_3618_, 1, v___x_3763_);
lean_ctor_set(v___x_3618_, 0, v___x_3744_);
v___x_3765_ = v___x_3618_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3766_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3741_);
lean_inc(v_quotContext_3742_);
v___x_3768_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3767_, v_currMacroScope_3741_);
lean_inc_n(v___x_3744_, 2);
v___x_3769_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3744_);
lean_ctor_set(v___x_3769_, 1, v___x_3766_);
lean_ctor_set(v___x_3769_, 2, v___x_3768_);
lean_ctor_set(v___x_3769_, 3, v___x_3751_);
v___x_3770_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3615_ == 0)
{
lean_ctor_set_tag(v___x_3614_, 2);
lean_ctor_set(v___x_3614_, 1, v___x_3770_);
lean_ctor_set(v___x_3614_, 0, v___x_3744_);
v___x_3772_ = v___x_3614_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3773_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3744_, 22);
v___x_3775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3744_);
lean_ctor_set(v___x_3775_, 1, v___x_3773_);
v___x_3776_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3777_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3778_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3741_, 5);
lean_inc_n(v_quotContext_3742_, 5);
v___x_3779_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3778_, v_currMacroScope_3741_);
v___x_3780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3744_);
lean_ctor_set(v___x_3780_, 1, v___x_3777_);
lean_ctor_set(v___x_3780_, 2, v___x_3779_);
lean_ctor_set(v___x_3780_, 3, v___x_3751_);
v___x_3781_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3782_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3783_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3782_, v_currMacroScope_3741_);
v___x_3784_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3744_);
lean_ctor_set(v___x_3784_, 1, v___x_3781_);
lean_ctor_set(v___x_3784_, 2, v___x_3783_);
lean_ctor_set(v___x_3784_, 3, v___x_3751_);
lean_inc_ref(v___x_3784_);
v___x_3785_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3761_, v___x_3780_, v___x_3784_);
v___x_3786_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3744_);
lean_ctor_set(v___x_3787_, 1, v___x_3761_);
lean_ctor_set(v___x_3787_, 2, v___x_3786_);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3744_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
lean_inc_ref(v___x_3789_);
lean_inc_ref(v___x_3787_);
v___x_3790_ = l_Lean_Syntax_node4(v___x_3744_, v___x_3776_, v___x_3785_, v___x_3787_, v___x_3789_, v_snd_3630_);
lean_inc_ref(v___x_3775_);
v___x_3791_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3774_, v___x_3775_, v___x_3790_);
v___x_3792_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3744_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
lean_inc_ref_n(v___x_3793_, 2);
lean_inc_ref_n(v___x_3772_, 2);
lean_inc_ref_n(v___x_3765_, 2);
v___x_3794_ = l_Lean_Syntax_node5(v___x_3744_, v___x_3762_, v___x_3765_, v___x_3769_, v___x_3772_, v___x_3791_, v___x_3793_);
v___x_3795_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3796_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3797_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3796_, v_currMacroScope_3741_);
v___x_3798_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3744_);
lean_ctor_set(v___x_3798_, 1, v___x_3795_);
lean_ctor_set(v___x_3798_, 2, v___x_3797_);
lean_ctor_set(v___x_3798_, 3, v___x_3751_);
v___x_3799_ = l_String_toRawSubstring_x27(v___x_3581_);
v___x_3800_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3569_, v_currMacroScope_3741_);
v___x_3801_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3744_);
lean_ctor_set(v___x_3801_, 1, v___x_3799_);
lean_ctor_set(v___x_3801_, 2, v___x_3800_);
lean_ctor_set(v___x_3801_, 3, v___x_3751_);
v___x_3802_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3761_, v___x_3801_, v___x_3784_);
v___x_3803_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3804_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3805_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3804_, v_currMacroScope_3741_);
v___x_3806_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3744_);
lean_ctor_set(v___x_3806_, 1, v___x_3803_);
lean_ctor_set(v___x_3806_, 2, v___x_3805_);
lean_ctor_set(v___x_3806_, 3, v___x_3751_);
v___x_3807_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3811_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3810_, v_currMacroScope_3741_);
v___x_3812_ = l_Lean_Name_mkStr4(v___x_3579_, v___x_3580_, v___x_3808_, v___x_3809_);
v___x_3813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
lean_ctor_set(v___x_3813_, 1, v___x_3751_);
v___x_3814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v___x_3751_);
v___x_3815_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3744_);
lean_ctor_set(v___x_3815_, 1, v___x_3807_);
lean_ctor_set(v___x_3815_, 2, v___x_3811_);
lean_ctor_set(v___x_3815_, 3, v___x_3814_);
v___x_3816_ = l_Lean_Syntax_node5(v___x_3744_, v___x_3762_, v___x_3765_, v___x_3806_, v___x_3772_, v___x_3815_, v___x_3793_);
v___x_3817_ = l_Lean_Syntax_node1(v___x_3744_, v___x_3761_, v___x_3816_);
v___x_3818_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3745_, v_fst_3629_, v___x_3817_);
v___x_3819_ = l_Lean_Syntax_node4(v___x_3744_, v___x_3776_, v___x_3802_, v___x_3787_, v___x_3789_, v___x_3818_);
v___x_3820_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3774_, v___x_3775_, v___x_3819_);
v___x_3821_ = l_Lean_Syntax_node5(v___x_3744_, v___x_3762_, v___x_3765_, v___x_3798_, v___x_3772_, v___x_3820_, v___x_3793_);
v___x_3822_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3761_, v___x_3794_, v___x_3821_);
v___x_3823_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3745_, v___x_3760_, v___x_3822_);
v_a_3592_ = v___x_3823_;
goto v___jp_3591_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_del_object(v___x_3608_);
v_e_3830_ = lean_ctor_get(v_default_3635_, 0);
lean_inc_ref(v_e_3830_);
lean_dec_ref_known(v_default_3635_, 1);
v___x_3831_ = lean_box(1);
v___x_3832_ = l_Lean_PrettyPrinter_delab(v_e_3830_, v___x_3831_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_toCold_3833_; lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3919_; 
v_toCold_3833_ = lean_ctor_get(v___y_3588_, 0);
lean_inc_ref(v_toCold_3833_);
v_a_3834_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3836_ = v___x_3832_;
v_isShared_3837_ = v_isSharedCheck_3919_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3832_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3919_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v_ref_3838_; lean_object* v_currMacroScope_3839_; lean_object* v_quotContext_3840_; uint8_t v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3851_; 
v_ref_3838_ = lean_ctor_get(v___y_3588_, 4);
lean_inc(v_ref_3838_);
v_currMacroScope_3839_ = lean_ctor_get(v___y_3588_, 9);
lean_inc_n(v_currMacroScope_3839_, 2);
lean_dec_ref(v___y_3588_);
v_quotContext_3840_ = lean_ctor_get(v_toCold_3833_, 2);
lean_inc_n(v_quotContext_3840_, 2);
lean_dec_ref(v_toCold_3833_);
v___x_3841_ = 0;
v___x_3842_ = l_Lean_SourceInfo_fromRef(v_ref_3838_, v___x_3841_);
lean_dec(v_ref_3838_);
v___x_3843_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3844_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3845_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3578_);
v___x_3846_ = l_Lean_Name_mkStr2(v___x_3578_, v___x_3845_);
v___x_3847_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3846_, v_currMacroScope_3839_);
v___x_3848_ = l_Lean_Name_mkStr4(v___x_3579_, v___x_3580_, v___x_3578_, v___x_3845_);
v___x_3849_ = lean_box(0);
lean_inc(v___x_3848_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 1);
lean_ctor_set(v___x_3637_, 1, v___x_3849_);
lean_ctor_set(v___x_3637_, 0, v___x_3848_);
v___x_3851_ = v___x_3637_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3848_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3853_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3848_);
v___x_3853_ = v___x_3836_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3848_);
v___x_3853_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3855_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set_tag(v___x_3632_, 1);
lean_ctor_set(v___x_3632_, 1, v___x_3849_);
lean_ctor_set(v___x_3632_, 0, v___x_3853_);
v___x_3855_ = v___x_3632_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v___x_3849_);
v___x_3855_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3857_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set_tag(v___x_3623_, 1);
lean_ctor_set(v___x_3623_, 1, v___x_3855_);
lean_ctor_set(v___x_3623_, 0, v___x_3851_);
v___x_3857_ = v___x_3623_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3863_; 
lean_inc_n(v___x_3842_, 2);
v___x_3858_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3842_);
lean_ctor_set(v___x_3858_, 1, v___x_3844_);
lean_ctor_set(v___x_3858_, 2, v___x_3847_);
lean_ctor_set(v___x_3858_, 3, v___x_3857_);
v___x_3859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3860_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3861_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 2);
lean_ctor_set(v___x_3618_, 1, v___x_3861_);
lean_ctor_set(v___x_3618_, 0, v___x_3842_);
v___x_3863_ = v___x_3618_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3864_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3865_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3839_);
lean_inc(v_quotContext_3840_);
v___x_3866_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3865_, v_currMacroScope_3839_);
lean_inc_n(v___x_3842_, 2);
v___x_3867_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3842_);
lean_ctor_set(v___x_3867_, 1, v___x_3864_);
lean_ctor_set(v___x_3867_, 2, v___x_3866_);
lean_ctor_set(v___x_3867_, 3, v___x_3849_);
v___x_3868_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3615_ == 0)
{
lean_ctor_set_tag(v___x_3614_, 2);
lean_ctor_set(v___x_3614_, 1, v___x_3868_);
lean_ctor_set(v___x_3614_, 0, v___x_3842_);
v___x_3870_ = v___x_3614_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3871_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3872_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3842_, 21);
v___x_3873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3842_);
lean_ctor_set(v___x_3873_, 1, v___x_3871_);
v___x_3874_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3875_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3876_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3839_, 4);
lean_inc_n(v_quotContext_3840_, 4);
v___x_3877_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3876_, v_currMacroScope_3839_);
v___x_3878_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3842_);
lean_ctor_set(v___x_3878_, 1, v___x_3875_);
lean_ctor_set(v___x_3878_, 2, v___x_3877_);
lean_ctor_set(v___x_3878_, 3, v___x_3849_);
v___x_3879_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3880_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3881_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3880_, v_currMacroScope_3839_);
v___x_3882_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3842_);
lean_ctor_set(v___x_3882_, 1, v___x_3879_);
lean_ctor_set(v___x_3882_, 2, v___x_3881_);
lean_ctor_set(v___x_3882_, 3, v___x_3849_);
lean_inc_ref(v___x_3882_);
v___x_3883_ = l_Lean_Syntax_node2(v___x_3842_, v___x_3859_, v___x_3878_, v___x_3882_);
v___x_3884_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3842_);
lean_ctor_set(v___x_3885_, 1, v___x_3859_);
lean_ctor_set(v___x_3885_, 2, v___x_3884_);
v___x_3886_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3842_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
lean_inc_ref(v___x_3887_);
lean_inc_ref(v___x_3885_);
v___x_3888_ = l_Lean_Syntax_node4(v___x_3842_, v___x_3874_, v___x_3883_, v___x_3885_, v___x_3887_, v_snd_3630_);
lean_inc_ref(v___x_3873_);
v___x_3889_ = l_Lean_Syntax_node2(v___x_3842_, v___x_3872_, v___x_3873_, v___x_3888_);
v___x_3890_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3842_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
lean_inc_ref_n(v___x_3891_, 2);
lean_inc_ref_n(v___x_3870_, 2);
lean_inc_ref_n(v___x_3863_, 2);
v___x_3892_ = l_Lean_Syntax_node5(v___x_3842_, v___x_3860_, v___x_3863_, v___x_3867_, v___x_3870_, v___x_3889_, v___x_3891_);
v___x_3893_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3894_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3895_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3894_, v_currMacroScope_3839_);
v___x_3896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3842_);
lean_ctor_set(v___x_3896_, 1, v___x_3893_);
lean_ctor_set(v___x_3896_, 2, v___x_3895_);
lean_ctor_set(v___x_3896_, 3, v___x_3849_);
v___x_3897_ = l_String_toRawSubstring_x27(v___x_3581_);
v___x_3898_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3569_, v_currMacroScope_3839_);
v___x_3899_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3842_);
lean_ctor_set(v___x_3899_, 1, v___x_3897_);
lean_ctor_set(v___x_3899_, 2, v___x_3898_);
lean_ctor_set(v___x_3899_, 3, v___x_3849_);
v___x_3900_ = l_Lean_Syntax_node2(v___x_3842_, v___x_3859_, v___x_3899_, v___x_3882_);
v___x_3901_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3902_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3903_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3902_, v_currMacroScope_3839_);
v___x_3904_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3842_);
lean_ctor_set(v___x_3904_, 1, v___x_3901_);
lean_ctor_set(v___x_3904_, 2, v___x_3903_);
lean_ctor_set(v___x_3904_, 3, v___x_3849_);
v___x_3905_ = l_Lean_Syntax_node5(v___x_3842_, v___x_3860_, v___x_3863_, v___x_3904_, v___x_3870_, v_a_3834_, v___x_3891_);
v___x_3906_ = l_Lean_Syntax_node1(v___x_3842_, v___x_3859_, v___x_3905_);
v___x_3907_ = l_Lean_Syntax_node2(v___x_3842_, v___x_3843_, v_fst_3629_, v___x_3906_);
v___x_3908_ = l_Lean_Syntax_node4(v___x_3842_, v___x_3874_, v___x_3900_, v___x_3885_, v___x_3887_, v___x_3907_);
v___x_3909_ = l_Lean_Syntax_node2(v___x_3842_, v___x_3872_, v___x_3873_, v___x_3908_);
v___x_3910_ = l_Lean_Syntax_node5(v___x_3842_, v___x_3860_, v___x_3863_, v___x_3896_, v___x_3870_, v___x_3909_, v___x_3891_);
v___x_3911_ = l_Lean_Syntax_node2(v___x_3842_, v___x_3859_, v___x_3892_, v___x_3910_);
v___x_3912_ = l_Lean_Syntax_node2(v___x_3842_, v___x_3843_, v___x_3858_, v___x_3911_);
v_a_3592_ = v___x_3912_;
goto v___jp_3591_;
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
lean_del_object(v___x_3637_);
lean_del_object(v___x_3632_);
lean_dec(v_snd_3630_);
lean_dec(v_fst_3629_);
lean_del_object(v___x_3623_);
lean_del_object(v___x_3618_);
lean_del_object(v___x_3614_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec_ref(v___x_3578_);
lean_dec(v___x_3569_);
v___y_3596_ = v___x_3832_;
goto v___jp_3595_;
}
}
default: 
{
lean_object* v_toCold_3920_; lean_object* v_ref_3921_; lean_object* v_currMacroScope_3922_; lean_object* v_quotContext_3923_; uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v_default_3635_);
v_toCold_3920_ = lean_ctor_get(v___y_3588_, 0);
lean_inc_ref(v_toCold_3920_);
v_ref_3921_ = lean_ctor_get(v___y_3588_, 4);
lean_inc(v_ref_3921_);
v_currMacroScope_3922_ = lean_ctor_get(v___y_3588_, 9);
lean_inc_n(v_currMacroScope_3922_, 2);
lean_dec_ref(v___y_3588_);
v_quotContext_3923_ = lean_ctor_get(v_toCold_3920_, 2);
lean_inc_n(v_quotContext_3923_, 2);
lean_dec_ref(v_toCold_3920_);
v___x_3924_ = 0;
v___x_3925_ = l_Lean_SourceInfo_fromRef(v_ref_3921_, v___x_3924_);
lean_dec(v_ref_3921_);
v___x_3926_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3927_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3928_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3578_);
v___x_3929_ = l_Lean_Name_mkStr2(v___x_3578_, v___x_3928_);
v___x_3930_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3929_, v_currMacroScope_3922_);
v___x_3931_ = l_Lean_Name_mkStr4(v___x_3579_, v___x_3580_, v___x_3578_, v___x_3928_);
v___x_3932_ = lean_box(0);
lean_inc(v___x_3931_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 1);
lean_ctor_set(v___x_3637_, 1, v___x_3932_);
lean_ctor_set(v___x_3637_, 0, v___x_3931_);
v___x_3934_ = v___x_3637_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3931_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3936_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3931_);
v___x_3936_ = v___x_3608_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3931_);
v___x_3936_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3938_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set_tag(v___x_3632_, 1);
lean_ctor_set(v___x_3632_, 1, v___x_3932_);
lean_ctor_set(v___x_3632_, 0, v___x_3936_);
v___x_3938_ = v___x_3632_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v___x_3932_);
v___x_3938_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set_tag(v___x_3623_, 1);
lean_ctor_set(v___x_3623_, 1, v___x_3938_);
lean_ctor_set(v___x_3623_, 0, v___x_3934_);
v___x_3940_ = v___x_3623_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
lean_inc_n(v___x_3925_, 2);
v___x_3941_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3925_);
lean_ctor_set(v___x_3941_, 1, v___x_3927_);
lean_ctor_set(v___x_3941_, 2, v___x_3930_);
lean_ctor_set(v___x_3941_, 3, v___x_3940_);
v___x_3942_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3943_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 2);
lean_ctor_set(v___x_3618_, 1, v___x_3944_);
lean_ctor_set(v___x_3618_, 0, v___x_3925_);
v___x_3946_ = v___x_3618_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3953_; 
v___x_3947_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3948_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3922_);
lean_inc(v_quotContext_3923_);
v___x_3949_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3948_, v_currMacroScope_3922_);
lean_inc_n(v___x_3925_, 2);
v___x_3950_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3925_);
lean_ctor_set(v___x_3950_, 1, v___x_3947_);
lean_ctor_set(v___x_3950_, 2, v___x_3949_);
lean_ctor_set(v___x_3950_, 3, v___x_3932_);
v___x_3951_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3615_ == 0)
{
lean_ctor_set_tag(v___x_3614_, 2);
lean_ctor_set(v___x_3614_, 1, v___x_3951_);
lean_ctor_set(v___x_3614_, 0, v___x_3925_);
v___x_3953_ = v___x_3614_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3989_, 1, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3955_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3925_, 17);
v___x_3956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3925_);
lean_ctor_set(v___x_3956_, 1, v___x_3954_);
v___x_3957_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3958_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3959_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3922_, 3);
lean_inc_n(v_quotContext_3923_, 3);
v___x_3960_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3959_, v_currMacroScope_3922_);
v___x_3961_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3925_);
lean_ctor_set(v___x_3961_, 1, v___x_3958_);
lean_ctor_set(v___x_3961_, 2, v___x_3960_);
lean_ctor_set(v___x_3961_, 3, v___x_3932_);
v___x_3962_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3963_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3964_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3963_, v_currMacroScope_3922_);
v___x_3965_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3925_);
lean_ctor_set(v___x_3965_, 1, v___x_3962_);
lean_ctor_set(v___x_3965_, 2, v___x_3964_);
lean_ctor_set(v___x_3965_, 3, v___x_3932_);
lean_inc_ref(v___x_3965_);
v___x_3966_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3942_, v___x_3961_, v___x_3965_);
v___x_3967_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3925_);
lean_ctor_set(v___x_3968_, 1, v___x_3942_);
lean_ctor_set(v___x_3968_, 2, v___x_3967_);
v___x_3969_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3925_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
lean_inc_ref(v___x_3970_);
lean_inc_ref(v___x_3968_);
v___x_3971_ = l_Lean_Syntax_node4(v___x_3925_, v___x_3957_, v___x_3966_, v___x_3968_, v___x_3970_, v_snd_3630_);
lean_inc_ref(v___x_3956_);
v___x_3972_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3955_, v___x_3956_, v___x_3971_);
v___x_3973_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3925_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
lean_inc_ref(v___x_3974_);
lean_inc_ref(v___x_3953_);
lean_inc_ref(v___x_3946_);
v___x_3975_ = l_Lean_Syntax_node5(v___x_3925_, v___x_3943_, v___x_3946_, v___x_3950_, v___x_3953_, v___x_3972_, v___x_3974_);
v___x_3976_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3977_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3978_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3977_, v_currMacroScope_3922_);
v___x_3979_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3925_);
lean_ctor_set(v___x_3979_, 1, v___x_3976_);
lean_ctor_set(v___x_3979_, 2, v___x_3978_);
lean_ctor_set(v___x_3979_, 3, v___x_3932_);
v___x_3980_ = l_String_toRawSubstring_x27(v___x_3581_);
v___x_3981_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3569_, v_currMacroScope_3922_);
v___x_3982_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3925_);
lean_ctor_set(v___x_3982_, 1, v___x_3980_);
lean_ctor_set(v___x_3982_, 2, v___x_3981_);
lean_ctor_set(v___x_3982_, 3, v___x_3932_);
v___x_3983_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3942_, v___x_3982_, v___x_3965_);
v___x_3984_ = l_Lean_Syntax_node4(v___x_3925_, v___x_3957_, v___x_3983_, v___x_3968_, v___x_3970_, v_fst_3629_);
v___x_3985_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3955_, v___x_3956_, v___x_3984_);
v___x_3986_ = l_Lean_Syntax_node5(v___x_3925_, v___x_3943_, v___x_3946_, v___x_3979_, v___x_3953_, v___x_3985_, v___x_3974_);
v___x_3987_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3942_, v___x_3975_, v___x_3986_);
v___x_3988_ = l_Lean_Syntax_node2(v___x_3925_, v___x_3926_, v___x_3941_, v___x_3987_);
v_a_3592_ = v___x_3988_;
goto v___jp_3591_;
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
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_del_object(v___x_3623_);
lean_dec(v_snd_3621_);
lean_del_object(v___x_3618_);
lean_del_object(v___x_3614_);
lean_del_object(v___x_3608_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec_ref(v___x_3578_);
lean_dec(v___x_3577_);
lean_dec(v___x_3569_);
v_a_3997_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3627_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3627_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
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
lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4084_; 
lean_dec(v_a_3599_);
lean_dec(v___x_3577_);
lean_dec(v___x_3576_);
lean_dec_ref(v___x_3570_);
v_isSharedCheck_4084_ = !lean_is_exclusive(v_val_3602_);
if (v_isSharedCheck_4084_ == 0)
{
lean_object* v_unused_4085_; lean_object* v_unused_4086_; 
v_unused_4085_ = lean_ctor_get(v_val_3602_, 1);
lean_dec(v_unused_4085_);
v_unused_4086_ = lean_ctor_get(v_val_3602_, 0);
lean_dec(v_unused_4086_);
v___x_4011_ = v_val_3602_;
v_isShared_4012_ = v_isSharedCheck_4084_;
goto v_resetjp_4010_;
}
else
{
lean_dec(v_val_3602_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4084_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v_toCold_4013_; lean_object* v_ref_4014_; lean_object* v_currMacroScope_4015_; lean_object* v_quotContext_4016_; uint8_t v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
v_toCold_4013_ = lean_ctor_get(v___y_3588_, 0);
lean_inc_ref(v_toCold_4013_);
v_ref_4014_ = lean_ctor_get(v___y_3588_, 4);
lean_inc(v_ref_4014_);
v_currMacroScope_4015_ = lean_ctor_get(v___y_3588_, 9);
lean_inc_n(v_currMacroScope_4015_, 2);
lean_dec_ref(v___y_3588_);
v_quotContext_4016_ = lean_ctor_get(v_toCold_4013_, 2);
lean_inc_n(v_quotContext_4016_, 2);
lean_dec_ref(v_toCold_4013_);
v___x_4017_ = 0;
v___x_4018_ = l_Lean_SourceInfo_fromRef(v_ref_4014_, v___x_4017_);
lean_dec(v_ref_4014_);
v___x_4019_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4020_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4021_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3578_);
v___x_4022_ = l_Lean_Name_mkStr2(v___x_3578_, v___x_4021_);
v___x_4023_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4022_, v_currMacroScope_4015_);
v___x_4024_ = l_Lean_Name_mkStr4(v___x_3579_, v___x_3580_, v___x_3578_, v___x_4021_);
v___x_4025_ = lean_box(0);
lean_inc(v___x_4024_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set_tag(v___x_4011_, 1);
lean_ctor_set(v___x_4011_, 1, v___x_4025_);
lean_ctor_set(v___x_4011_, 0, v___x_4024_);
v___x_4027_ = v___x_4011_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4024_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4029_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 0);
lean_ctor_set(v___x_3604_, 0, v___x_4024_);
v___x_4029_ = v___x_3604_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4024_);
v___x_4029_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v___x_4025_);
v___x_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4027_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
lean_inc_n(v___x_4018_, 23);
v___x_4032_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4018_);
lean_ctor_set(v___x_4032_, 1, v___x_4020_);
lean_ctor_set(v___x_4032_, 2, v___x_4023_);
lean_ctor_set(v___x_4032_, 3, v___x_4031_);
v___x_4033_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4034_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4035_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_4036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4018_);
lean_ctor_set(v___x_4036_, 1, v___x_4035_);
v___x_4037_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4038_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_4015_, 4);
lean_inc_n(v_quotContext_4016_, 4);
v___x_4039_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4038_, v_currMacroScope_4015_);
v___x_4040_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4018_);
lean_ctor_set(v___x_4040_, 1, v___x_4037_);
lean_ctor_set(v___x_4040_, 2, v___x_4039_);
lean_ctor_set(v___x_4040_, 3, v___x_4025_);
v___x_4041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_4042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4018_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
v___x_4045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4018_);
lean_ctor_set(v___x_4045_, 1, v___x_4043_);
v___x_4046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4047_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4048_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_4049_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4048_, v_currMacroScope_4015_);
v___x_4050_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4018_);
lean_ctor_set(v___x_4050_, 1, v___x_4047_);
lean_ctor_set(v___x_4050_, 2, v___x_4049_);
lean_ctor_set(v___x_4050_, 3, v___x_4025_);
v___x_4051_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4052_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4053_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4052_, v_currMacroScope_4015_);
v___x_4054_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4018_);
lean_ctor_set(v___x_4054_, 1, v___x_4051_);
lean_ctor_set(v___x_4054_, 2, v___x_4053_);
lean_ctor_set(v___x_4054_, 3, v___x_4025_);
lean_inc_ref(v___x_4054_);
v___x_4055_ = l_Lean_Syntax_node2(v___x_4018_, v___x_4033_, v___x_4050_, v___x_4054_);
v___x_4056_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4018_);
lean_ctor_set(v___x_4057_, 1, v___x_4033_);
lean_ctor_set(v___x_4057_, 2, v___x_4056_);
v___x_4058_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4018_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4061_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4018_);
lean_ctor_set(v___x_4062_, 1, v___x_4061_);
v___x_4063_ = l_Lean_Syntax_node1(v___x_4018_, v___x_4060_, v___x_4062_);
lean_inc(v___x_4063_);
lean_inc_ref(v___x_4059_);
lean_inc_ref(v___x_4057_);
v___x_4064_ = l_Lean_Syntax_node4(v___x_4018_, v___x_4046_, v___x_4055_, v___x_4057_, v___x_4059_, v___x_4063_);
lean_inc_ref(v___x_4045_);
v___x_4065_ = l_Lean_Syntax_node2(v___x_4018_, v___x_4044_, v___x_4045_, v___x_4064_);
v___x_4066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4018_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
lean_inc_ref(v___x_4067_);
lean_inc_ref(v___x_4042_);
lean_inc_ref(v___x_4036_);
v___x_4068_ = l_Lean_Syntax_node5(v___x_4018_, v___x_4034_, v___x_4036_, v___x_4040_, v___x_4042_, v___x_4065_, v___x_4067_);
v___x_4069_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4070_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4071_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4070_, v_currMacroScope_4015_);
v___x_4072_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4018_);
lean_ctor_set(v___x_4072_, 1, v___x_4069_);
lean_ctor_set(v___x_4072_, 2, v___x_4071_);
lean_ctor_set(v___x_4072_, 3, v___x_4025_);
v___x_4073_ = l_String_toRawSubstring_x27(v___x_3581_);
v___x_4074_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_3569_, v_currMacroScope_4015_);
v___x_4075_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4018_);
lean_ctor_set(v___x_4075_, 1, v___x_4073_);
lean_ctor_set(v___x_4075_, 2, v___x_4074_);
lean_ctor_set(v___x_4075_, 3, v___x_4025_);
v___x_4076_ = l_Lean_Syntax_node2(v___x_4018_, v___x_4033_, v___x_4075_, v___x_4054_);
v___x_4077_ = l_Lean_Syntax_node4(v___x_4018_, v___x_4046_, v___x_4076_, v___x_4057_, v___x_4059_, v___x_4063_);
v___x_4078_ = l_Lean_Syntax_node2(v___x_4018_, v___x_4044_, v___x_4045_, v___x_4077_);
v___x_4079_ = l_Lean_Syntax_node5(v___x_4018_, v___x_4034_, v___x_4036_, v___x_4072_, v___x_4042_, v___x_4078_, v___x_4067_);
v___x_4080_ = l_Lean_Syntax_node2(v___x_4018_, v___x_4033_, v___x_4068_, v___x_4079_);
v___x_4081_ = l_Lean_Syntax_node2(v___x_4018_, v___x_4019_, v___x_4032_, v___x_4080_);
v_a_3592_ = v___x_4081_;
goto v___jp_3591_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3601_);
lean_dec_ref(v___x_3578_);
if (lean_obj_tag(v_a_3599_) == 1)
{
lean_object* v_val_4088_; lean_object* v_snd_4089_; lean_object* v_fst_4090_; lean_object* v_snd_4091_; lean_object* v___x_4092_; lean_object* v___f_4093_; lean_object* v___x_4094_; 
v_val_4088_ = lean_ctor_get(v_a_3599_, 0);
lean_inc(v_val_4088_);
lean_dec_ref_known(v_a_3599_, 1);
v_snd_4089_ = lean_ctor_get(v_val_4088_, 1);
lean_inc(v_snd_4089_);
v_fst_4090_ = lean_ctor_get(v_val_4088_, 0);
lean_inc(v_fst_4090_);
lean_dec(v_val_4088_);
v_snd_4091_ = lean_ctor_get(v_snd_4089_, 1);
lean_inc(v_snd_4091_);
lean_dec(v_snd_4089_);
v___x_4092_ = lean_box(v___x_3575_);
lean_inc(v___x_3569_);
v___f_4093_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4093_, 0, v_fst_4090_);
lean_closure_set(v___f_4093_, 1, v_snd_4091_);
lean_closure_set(v___f_4093_, 2, v___x_3581_);
lean_closure_set(v___f_4093_, 3, v___x_3569_);
lean_closure_set(v___f_4093_, 4, v___x_3576_);
lean_closure_set(v___f_4093_, 5, v___x_3577_);
lean_closure_set(v___f_4093_, 6, v___x_3579_);
lean_closure_set(v___f_4093_, 7, v___x_3580_);
lean_closure_set(v___f_4093_, 8, v___x_4092_);
lean_closure_set(v___f_4093_, 9, v_arg_3574_);
v___x_4094_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3569_, v___x_3570_, v___f_4093_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec_ref(v___y_3588_);
v___y_3596_ = v___x_4094_;
goto v___jp_3595_;
}
else
{
lean_object* v_toCold_4095_; lean_object* v_ref_4096_; lean_object* v_currMacroScope_4097_; lean_object* v_quotContext_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_dec(v_a_3599_);
lean_dec(v___x_3577_);
lean_dec(v___x_3576_);
lean_dec_ref(v_arg_3574_);
lean_dec_ref(v___x_3570_);
v_toCold_4095_ = lean_ctor_get(v___y_3588_, 0);
lean_inc_ref(v_toCold_4095_);
v_ref_4096_ = lean_ctor_get(v___y_3588_, 4);
lean_inc(v_ref_4096_);
v_currMacroScope_4097_ = lean_ctor_get(v___y_3588_, 9);
lean_inc_n(v_currMacroScope_4097_, 2);
lean_dec_ref(v___y_3588_);
v_quotContext_4098_ = lean_ctor_get(v_toCold_4095_, 2);
lean_inc_n(v_quotContext_4098_, 2);
lean_dec_ref(v_toCold_4095_);
v___x_4099_ = 0;
v___x_4100_ = l_Lean_SourceInfo_fromRef(v_ref_4096_, v___x_4099_);
lean_dec(v_ref_4096_);
v___x_4101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4102_ = l_Lean_Name_mkStr3(v___x_3579_, v___x_3580_, v___x_4101_);
v___x_4103_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4104_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4100_, 13);
v___x_4105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4100_);
lean_ctor_set(v___x_4105_, 1, v___x_4103_);
lean_ctor_set(v___x_4105_, 2, v___x_4104_);
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_4107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4100_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4100_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
v___x_4112_ = l_String_toRawSubstring_x27(v___x_3581_);
v___x_4113_ = l_Lean_addMacroScope(v_quotContext_4098_, v___x_3569_, v_currMacroScope_4097_);
v___x_4114_ = lean_box(0);
v___x_4115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4100_);
lean_ctor_set(v___x_4115_, 1, v___x_4112_);
lean_ctor_set(v___x_4115_, 2, v___x_4113_);
lean_ctor_set(v___x_4115_, 3, v___x_4114_);
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4100_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4120_ = l_Lean_addMacroScope(v_quotContext_4098_, v___x_4119_, v_currMacroScope_4097_);
v___x_4121_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4100_);
lean_ctor_set(v___x_4121_, 1, v___x_4118_);
lean_ctor_set(v___x_4121_, 2, v___x_4120_);
lean_ctor_set(v___x_4121_, 3, v___x_4114_);
v___x_4122_ = l_Lean_Syntax_node3(v___x_4100_, v___x_4108_, v___x_4115_, v___x_4117_, v___x_4121_);
v___x_4123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4100_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = l_Lean_Syntax_node3(v___x_4100_, v___x_4109_, v___x_4111_, v___x_4122_, v___x_4124_);
v___x_4126_ = l_Lean_Syntax_node1(v___x_4100_, v___x_4108_, v___x_4125_);
v___x_4127_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4100_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4130_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4100_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = l_Lean_Syntax_node1(v___x_4100_, v___x_4129_, v___x_4131_);
v___x_4133_ = l_Lean_Syntax_node5(v___x_4100_, v___x_4102_, v___x_4105_, v___x_4107_, v___x_4126_, v___x_4128_, v___x_4132_);
v_a_3592_ = v___x_4133_;
goto v___jp_3591_;
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec(v_a_3599_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec_ref(v___x_3578_);
lean_dec(v___x_3577_);
lean_dec(v___x_3576_);
lean_dec_ref(v_arg_3574_);
lean_dec_ref(v___x_3570_);
lean_dec(v___x_3569_);
v_a_4134_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_3600_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_3600_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec_ref(v___x_3578_);
lean_dec(v___x_3577_);
lean_dec(v___x_3576_);
lean_dec_ref(v_arg_3574_);
lean_dec(v_inv_3573_);
lean_dec_ref(v___x_3570_);
lean_dec(v___x_3569_);
v_a_4142_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_3598_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_3598_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
v___jp_3591_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3592_);
v___x_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
return v___x_3594_;
}
v___jp_3595_:
{
if (lean_obj_tag(v___y_3596_) == 0)
{
lean_object* v_a_3597_; 
v_a_3597_ = lean_ctor_get(v___y_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___y_3596_, 1);
v_a_3592_ = v_a_3597_;
goto v___jp_3591_;
}
else
{
return v___y_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4150_ = _args[0];
lean_object* v___x_4151_ = _args[1];
lean_object* v___f_4152_ = _args[2];
lean_object* v_a_4153_ = _args[3];
lean_object* v_inv_4154_ = _args[4];
lean_object* v_arg_4155_ = _args[5];
lean_object* v___x_4156_ = _args[6];
lean_object* v___x_4157_ = _args[7];
lean_object* v___x_4158_ = _args[8];
lean_object* v___x_4159_ = _args[9];
lean_object* v___x_4160_ = _args[10];
lean_object* v___x_4161_ = _args[11];
lean_object* v___x_4162_ = _args[12];
lean_object* v___y_4163_ = _args[13];
lean_object* v___y_4164_ = _args[14];
lean_object* v___y_4165_ = _args[15];
lean_object* v___y_4166_ = _args[16];
lean_object* v___y_4167_ = _args[17];
lean_object* v___y_4168_ = _args[18];
lean_object* v___y_4169_ = _args[19];
lean_object* v___y_4170_ = _args[20];
lean_object* v___y_4171_ = _args[21];
_start:
{
uint8_t v___x_78846__boxed_4172_; lean_object* v_res_4173_; 
v___x_78846__boxed_4172_ = lean_unbox(v___x_4156_);
v_res_4173_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4150_, v___x_4151_, v___f_4152_, v_a_4153_, v_inv_4154_, v_arg_4155_, v___x_78846__boxed_4172_, v___x_4157_, v___x_4158_, v___x_4159_, v___x_4160_, v___x_4161_, v___x_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec_ref(v_a_4153_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v___x_4180_; lean_object* v_env_4181_; lean_object* v___x_4182_; lean_object* v_mctx_4183_; lean_object* v_lctx_4184_; lean_object* v_options_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4180_ = lean_st_ref_get(v___y_4178_);
v_env_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc_ref(v_env_4181_);
lean_dec(v___x_4180_);
v___x_4182_ = lean_st_ref_get(v___y_4176_);
v_mctx_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc_ref(v_mctx_4183_);
lean_dec(v___x_4182_);
v_lctx_4184_ = lean_ctor_get(v___y_4175_, 2);
v_options_4185_ = lean_ctor_get(v___y_4177_, 1);
lean_inc_ref(v_options_4185_);
lean_inc_ref(v_lctx_4184_);
v___x_4186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4186_, 0, v_env_4181_);
lean_ctor_set(v___x_4186_, 1, v_mctx_4183_);
lean_ctor_set(v___x_4186_, 2, v_lctx_4184_);
lean_ctor_set(v___x_4186_, 3, v_options_4185_);
v___x_4187_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
lean_ctor_set(v___x_4187_, 1, v_msgData_4174_);
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_ref_4202_; lean_object* v___x_4203_; lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4212_; 
v_ref_4202_ = lean_ctor_get(v___y_4199_, 4);
v___x_4203_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4210_; 
lean_inc(v_ref_4202_);
v___x_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4208_, 0, v_ref_4202_);
lean_ctor_set(v___x_4208_, 1, v_a_4204_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set_tag(v___x_4206_, 1);
lean_ctor_set(v___x_4206_, 0, v___x_4208_);
v___x_4210_ = v___x_4206_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4226_, size_t v_i_4227_, size_t v_stop_4228_, lean_object* v_b_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_a_4240_; lean_object* v_a_4245_; uint8_t v___x_4247_; 
v___x_4247_ = lean_usize_dec_eq(v_i_4227_, v_stop_4228_);
if (v___x_4247_ == 0)
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4231_, v___y_4233_, v___y_4235_, v___y_4237_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4250_; lean_object* v___y_4252_; uint8_t v___y_4253_; lean_object* v___y_4268_; lean_object* v_a_4269_; lean_object* v___x_4272_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4248_, 1);
v___x_4250_ = lean_array_uget_borrowed(v_as_4226_, v_i_4227_);
lean_inc(v___x_4250_);
v___x_4272_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4250_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v_ref_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___x_4272_, 1);
v_ref_4274_ = lean_ctor_get(v___y_4236_, 4);
v___x_4275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
v___x_4277_ = l_Lean_SourceInfo_fromRef(v_ref_4274_, v___x_4247_);
lean_inc(v___x_4277_);
v___x_4278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
lean_ctor_set(v___x_4278_, 1, v___x_4275_);
v___x_4279_ = l_Lean_Syntax_node1(v___x_4277_, v___x_4276_, v___x_4278_);
v___x_4280_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4279_, v_a_4273_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4282_; 
lean_dec(v_a_4249_);
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v___x_4280_, 1);
v___x_4282_ = lean_array_mk(v_a_4281_);
v_a_4245_ = v___x_4282_;
goto v___jp_4244_;
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
v_a_4283_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4280_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4280_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
lean_inc(v_a_4283_);
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
v___y_4268_ = v___x_4288_;
v_a_4269_ = v_a_4283_;
goto v___jp_4267_;
}
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
v_a_4291_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4272_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4272_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
lean_inc(v_a_4291_);
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
v___y_4268_ = v___x_4296_;
v_a_4269_ = v_a_4291_;
goto v___jp_4267_;
}
}
}
v___jp_4251_:
{
if (v___y_4253_ == 0)
{
lean_object* v___x_4254_; 
lean_dec_ref(v___y_4252_);
v___x_4254_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4249_, v___y_4253_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
lean_dec_ref_known(v___x_4254_, 1);
v___x_4255_ = lean_unsigned_to_nat(1u);
v___x_4256_ = lean_mk_empty_array_with_capacity(v___x_4255_);
lean_inc(v___x_4250_);
v___x_4257_ = lean_array_push(v___x_4256_, v___x_4250_);
v_a_4245_ = v___x_4257_;
goto v___jp_4244_;
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
lean_dec_ref(v_b_4229_);
v_a_4258_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4254_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4254_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
else
{
lean_dec(v_a_4249_);
lean_dec_ref(v_b_4229_);
if (lean_obj_tag(v___y_4252_) == 0)
{
lean_object* v_a_4266_; 
v_a_4266_ = lean_ctor_get(v___y_4252_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___y_4252_, 1);
v_a_4240_ = v_a_4266_;
goto v___jp_4239_;
}
else
{
return v___y_4252_;
}
}
}
v___jp_4267_:
{
uint8_t v___x_4270_; 
v___x_4270_ = l_Lean_Exception_isInterrupt(v_a_4269_);
if (v___x_4270_ == 0)
{
uint8_t v___x_4271_; 
v___x_4271_ = l_Lean_Exception_isRuntime(v_a_4269_);
v___y_4252_ = v___y_4268_;
v___y_4253_ = v___x_4271_;
goto v___jp_4251_;
}
else
{
lean_dec_ref(v_a_4269_);
v___y_4252_ = v___y_4268_;
v___y_4253_ = v___x_4270_;
goto v___jp_4251_;
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec_ref(v_b_4229_);
v_a_4299_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4248_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4248_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
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
return v___x_4304_;
}
}
}
}
else
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v_b_4229_);
return v___x_4307_;
}
v___jp_4239_:
{
size_t v___x_4241_; size_t v___x_4242_; 
v___x_4241_ = ((size_t)1ULL);
v___x_4242_ = lean_usize_add(v_i_4227_, v___x_4241_);
v_i_4227_ = v___x_4242_;
v_b_4229_ = v_a_4240_;
goto _start;
}
v___jp_4244_:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Array_append___redArg(v_b_4229_, v_a_4245_);
lean_dec_ref(v_a_4245_);
v_a_4240_ = v___x_4246_;
goto v___jp_4239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4308_, lean_object* v_i_4309_, lean_object* v_stop_4310_, lean_object* v_b_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
size_t v_i_boxed_4321_; size_t v_stop_boxed_4322_; lean_object* v_res_4323_; 
v_i_boxed_4321_ = lean_unbox_usize(v_i_4309_);
lean_dec(v_i_4309_);
v_stop_boxed_4322_ = lean_unbox_usize(v_stop_4310_);
lean_dec(v_stop_4310_);
v_res_4323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4308_, v_i_boxed_4321_, v_stop_boxed_4322_, v_b_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec_ref(v_as_4308_);
return v_res_4323_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4325_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4326_ = l_Lean_stringToMessageData(v___x_4325_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4342_, lean_object* v_inv_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v___x_4353_; 
lean_inc(v_inv_4343_);
v___x_4353_ = l_Lean_MVarId_getType(v_inv_4343_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; lean_object* v_a_4356_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4355_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4354_, v_a_4349_);
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc_n(v_a_4356_, 2);
lean_dec_ref(v___x_4355_);
v___x_4370_ = l_Lean_Expr_cleanupAnnotations(v_a_4356_);
v___x_4371_ = l_Lean_Expr_isApp(v___x_4370_);
if (v___x_4371_ == 0)
{
lean_dec_ref(v___x_4370_);
lean_dec(v_inv_4343_);
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
goto v___jp_4357_;
}
else
{
lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4370_);
v___x_4373_ = l_Lean_Expr_isApp(v___x_4372_);
if (v___x_4373_ == 0)
{
lean_dec_ref(v___x_4372_);
lean_dec(v_inv_4343_);
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
goto v___jp_4357_;
}
else
{
lean_object* v_arg_4374_; lean_object* v___x_4375_; uint8_t v___x_4376_; 
v_arg_4374_ = lean_ctor_get(v___x_4372_, 1);
lean_inc_ref(v_arg_4374_);
v___x_4375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4372_);
v___x_4376_ = l_Lean_Expr_isApp(v___x_4375_);
if (v___x_4376_ == 0)
{
lean_dec_ref(v___x_4375_);
lean_dec_ref(v_arg_4374_);
lean_dec(v_inv_4343_);
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
goto v___jp_4357_;
}
else
{
lean_object* v_arg_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v_arg_4377_ = lean_ctor_get(v___x_4375_, 1);
lean_inc_ref(v_arg_4377_);
v___x_4378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4375_);
v___x_4379_ = l_Lean_Expr_isApp(v___x_4378_);
if (v___x_4379_ == 0)
{
lean_dec_ref(v___x_4378_);
lean_dec_ref(v_arg_4377_);
lean_dec_ref(v_arg_4374_);
lean_dec(v_inv_4343_);
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
goto v___jp_4357_;
}
else
{
lean_object* v_arg_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v_arg_4380_ = lean_ctor_get(v___x_4378_, 1);
lean_inc_ref(v_arg_4380_);
v___x_4381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4378_);
v___x_4382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4385_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4386_ = l_Lean_Expr_isConstOf(v___x_4381_, v___x_4385_);
if (v___x_4386_ == 0)
{
lean_dec_ref(v___x_4381_);
lean_dec_ref(v_arg_4380_);
lean_dec_ref(v_arg_4377_);
lean_dec_ref(v_arg_4374_);
lean_dec(v_inv_4343_);
v___y_4358_ = v_a_4344_;
v___y_4359_ = v_a_4345_;
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
goto v___jp_4357_;
}
else
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v_a_4393_; lean_object* v___x_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; 
lean_dec(v_a_4356_);
v___x_4387_ = lean_unsigned_to_nat(1u);
v___x_4388_ = l_Lean_Expr_constLevels_x21(v___x_4381_);
lean_dec_ref(v___x_4381_);
v___x_4389_ = lean_unsigned_to_nat(0u);
v___x_4390_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4388_);
v___x_4391_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4388_, v___x_4388_, v___x_4387_, v___x_4390_);
lean_dec(v___x_4388_);
v___x_4404_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4405_ = lean_array_get_size(v_vcs_4342_);
v___x_4406_ = lean_nat_dec_lt(v___x_4389_, v___x_4405_);
if (v___x_4406_ == 0)
{
v_a_4393_ = v___x_4404_;
goto v___jp_4392_;
}
else
{
size_t v___x_4407_; size_t v___x_4408_; lean_object* v___x_4409_; 
v___x_4407_ = ((size_t)0ULL);
v___x_4408_ = lean_usize_of_nat(v___x_4405_);
v___x_4409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4342_, v___x_4407_, v___x_4408_, v___x_4404_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v_a_4393_ = v_a_4410_;
goto v___jp_4392_;
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v___x_4391_);
lean_dec_ref(v_arg_4380_);
lean_dec_ref(v_arg_4377_);
lean_dec_ref(v_arg_4374_);
lean_dec(v_inv_4343_);
v_a_4411_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4409_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4409_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
v___jp_4392_:
{
lean_object* v___x_4394_; lean_object* v___f_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___f_4402_; lean_object* v___x_4403_; 
v___x_4394_ = lean_box(v___x_4386_);
lean_inc_ref(v_arg_4374_);
lean_inc_n(v_inv_4343_, 2);
lean_inc_ref(v_a_4393_);
v___f_4395_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4395_, 0, v_a_4393_);
lean_closure_set(v___f_4395_, 1, v_inv_4343_);
lean_closure_set(v___f_4395_, 2, v___x_4394_);
lean_closure_set(v___f_4395_, 3, v___x_4387_);
lean_closure_set(v___f_4395_, 4, v_arg_4374_);
v___x_4396_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4397_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4398_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4399_ = l_Lean_mkConst(v___x_4398_, v___x_4391_);
v___x_4400_ = l_Lean_mkAppB(v___x_4399_, v_arg_4380_, v_arg_4377_);
v___x_4401_ = lean_box(v___x_4386_);
v___f_4402_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4402_, 0, v___x_4397_);
lean_closure_set(v___f_4402_, 1, v___x_4400_);
lean_closure_set(v___f_4402_, 2, v___f_4395_);
lean_closure_set(v___f_4402_, 3, v_a_4393_);
lean_closure_set(v___f_4402_, 4, v_inv_4343_);
lean_closure_set(v___f_4402_, 5, v_arg_4374_);
lean_closure_set(v___f_4402_, 6, v___x_4401_);
lean_closure_set(v___f_4402_, 7, v___x_4387_);
lean_closure_set(v___f_4402_, 8, v___x_4389_);
lean_closure_set(v___f_4402_, 9, v___x_4384_);
lean_closure_set(v___f_4402_, 10, v___x_4382_);
lean_closure_set(v___f_4402_, 11, v___x_4383_);
lean_closure_set(v___f_4402_, 12, v___x_4396_);
v___x_4403_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4343_, v___f_4402_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
return v___x_4403_;
}
}
}
}
}
}
v___jp_4357_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4366_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4367_ = l_Lean_MessageData_ofExpr(v_a_4356_);
v___x_4368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4366_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4368_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
return v___x_4369_;
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec(v_inv_4343_);
v_a_4419_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4353_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4353_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4427_, lean_object* v_inv_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4427_, v_inv_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_);
lean_dec(v_a_4436_);
lean_dec_ref(v_a_4435_);
lean_dec(v_a_4434_);
lean_dec_ref(v_a_4433_);
lean_dec(v_a_4432_);
lean_dec_ref(v_a_4431_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
lean_dec_ref(v_vcs_4427_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4439_, lean_object* v_msg_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v___x_4450_; 
v___x_4450_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4440_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4451_, lean_object* v_msg_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4451_, v_msg_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4463_, lean_object* v_name_4464_, uint8_t v_bi_4465_, lean_object* v_type_4466_, lean_object* v_k_4467_, uint8_t v_kind_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4464_, v_bi_4465_, v_type_4466_, v_k_4467_, v_kind_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4479_, lean_object* v_name_4480_, lean_object* v_bi_4481_, lean_object* v_type_4482_, lean_object* v_k_4483_, lean_object* v_kind_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
uint8_t v_bi_boxed_4494_; uint8_t v_kind_boxed_4495_; lean_object* v_res_4496_; 
v_bi_boxed_4494_ = lean_unbox(v_bi_4481_);
v_kind_boxed_4495_ = lean_unbox(v_kind_4484_);
v_res_4496_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4479_, v_name_4480_, v_bi_boxed_4494_, v_type_4482_, v_k_4483_, v_kind_boxed_4495_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4497_, lean_object* v_name_4498_, lean_object* v_type_4499_, lean_object* v_k_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4498_, v_type_4499_, v_k_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4511_, lean_object* v_name_4512_, lean_object* v_type_4513_, lean_object* v_k_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4511_, v_name_4512_, v_type_4513_, v_k_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4525_, size_t v_sz_4526_, size_t v_i_4527_, lean_object* v_b_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4525_, v_sz_4526_, v_i_4527_, v_b_4528_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4539_, lean_object* v_sz_4540_, lean_object* v_i_4541_, lean_object* v_b_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
size_t v_sz_boxed_4552_; size_t v_i_boxed_4553_; lean_object* v_res_4554_; 
v_sz_boxed_4552_ = lean_unbox_usize(v_sz_4540_);
lean_dec(v_sz_4540_);
v_i_boxed_4553_ = lean_unbox_usize(v_i_4541_);
lean_dec(v_i_4541_);
v_res_4554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4539_, v_sz_boxed_4552_, v_i_boxed_4553_, v_b_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec_ref(v_as_4539_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4555_, size_t v_sz_4556_, size_t v_i_4557_, lean_object* v_b_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v___x_4568_; 
v___x_4568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4555_, v_sz_4556_, v_i_4557_, v_b_4558_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4569_, lean_object* v_sz_4570_, lean_object* v_i_4571_, lean_object* v_b_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
size_t v_sz_boxed_4582_; size_t v_i_boxed_4583_; lean_object* v_res_4584_; 
v_sz_boxed_4582_ = lean_unbox_usize(v_sz_4570_);
lean_dec(v_sz_4570_);
v_i_boxed_4583_ = lean_unbox_usize(v_i_4571_);
lean_dec(v_i_4571_);
v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4569_, v_sz_boxed_4582_, v_i_boxed_4583_, v_b_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec_ref(v_as_4569_);
return v_res_4584_;
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
