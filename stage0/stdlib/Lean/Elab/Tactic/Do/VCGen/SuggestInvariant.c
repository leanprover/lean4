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
lean_object* lean_erase_macro_scopes(lean_object*);
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
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "snd"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(35, 40, 163, 84, 60, 49, 151, 224)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Cursor"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(171, 26, 51, 126, 183, 221, 138, 175)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 108, 132, 55, 147, 41, 48, 106)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__4_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__1;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___y_63_);
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
lean_dec_ref(v___x_68_);
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
lean_dec_ref(v_t_134_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0(lean_object* v_inv_181_, lean_object* v_b_182_){
_start:
{
lean_object* v_snd_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_222_; 
v_snd_183_ = lean_ctor_get(v_b_182_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_b_182_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v_b_182_, 0);
lean_dec(v_unused_223_);
v___x_185_ = v_b_182_;
v_isShared_186_ = v_isSharedCheck_222_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_snd_183_);
lean_dec(v_b_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_222_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_fst_187_; lean_object* v_snd_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_221_; 
v_fst_187_ = lean_ctor_get(v_snd_183_, 0);
v_snd_188_ = lean_ctor_get(v_snd_183_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_snd_183_);
if (v_isSharedCheck_221_ == 0)
{
v___x_190_ = v_snd_183_;
v_isShared_191_ = v_isSharedCheck_221_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_snd_188_);
lean_inc(v_fst_187_);
lean_dec(v_snd_183_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_221_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_192_ = lean_box(0);
lean_inc(v_inv_181_);
v___x_193_ = l_Lean_mkMVar(v_inv_181_);
v___x_194_ = lean_expr_eqv(v_fst_187_, v___x_193_);
lean_dec_ref(v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__2));
v___x_196_ = lean_unsigned_to_nat(4u);
v___x_197_ = l_Lean_Expr_isAppOfArity(v_fst_187_, v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_200_; 
lean_dec(v_inv_181_);
v___x_198_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__3));
if (v_isShared_191_ == 0)
{
v___x_200_ = v___x_190_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_fst_187_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_snd_188_);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_200_);
lean_ctor_set(v___x_185_, 0, v___x_198_);
v___x_202_ = v___x_185_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_object* v___x_205_; lean_object* v_conditionIdx_206_; lean_object* v_head_207_; lean_object* v___x_209_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v_conditionIdx_206_ = lean_nat_add(v_snd_188_, v___x_205_);
lean_dec(v_snd_188_);
v_head_207_ = l_Lean_Expr_getRevArg_x21(v_fst_187_, v___x_205_);
lean_dec(v_fst_187_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v_conditionIdx_206_);
lean_ctor_set(v___x_190_, 0, v_head_207_);
v___x_209_ = v___x_190_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_head_207_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_conditionIdx_206_);
v___x_209_ = v_reuseFailAlloc_214_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_209_);
lean_ctor_set(v___x_185_, 0, v___x_192_);
v___x_211_ = v___x_185_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_213_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
v_b_182_ = v___x_211_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v_inv_181_);
if (v_isShared_191_ == 0)
{
v___x_216_ = v___x_190_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fst_187_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_snd_188_);
v___x_216_ = v_reuseFailAlloc_220_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_216_);
lean_ctor_set(v___x_185_, 0, v___x_192_);
v___x_218_ = v___x_185_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1(lean_object* v_b_228_){
_start:
{
lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_255_; 
v_fst_229_ = lean_ctor_get(v_b_228_, 0);
v_snd_230_ = lean_ctor_get(v_b_228_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_b_228_);
if (v_isSharedCheck_255_ == 0)
{
v___x_232_ = v_b_228_;
v_isShared_233_ = v_isSharedCheck_255_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_snd_230_);
lean_inc(v_fst_229_);
lean_dec(v_b_228_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_255_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(4u);
v___x_235_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1));
v___x_236_ = l_Lean_Expr_isAppOfArity(v_fst_229_, v___x_235_, v___x_234_);
if (v___x_236_ == 0)
{
lean_object* v___x_238_; 
if (v_isShared_233_ == 0)
{
v___x_238_ = v___x_232_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_snd_230_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_240_ = lean_unsigned_to_nat(2u);
v___x_241_ = lean_unsigned_to_nat(3u);
v___x_242_ = l_Lean_Expr_getAppNumArgs(v_fst_229_);
v___x_243_ = lean_nat_sub(v___x_242_, v___x_240_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_sub(v___x_243_, v___x_244_);
lean_dec(v___x_243_);
v___x_246_ = l_Lean_Expr_getRevArg_x21(v_fst_229_, v___x_245_);
v___x_247_ = lean_array_push(v_snd_230_, v___x_246_);
v___x_248_ = lean_nat_sub(v___x_242_, v___x_241_);
lean_dec(v___x_242_);
v___x_249_ = lean_nat_sub(v___x_248_, v___x_244_);
lean_dec(v___x_248_);
v___x_250_ = l_Lean_Expr_getRevArg_x21(v_fst_229_, v___x_249_);
lean_dec(v_fst_229_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v___x_247_);
lean_ctor_set(v___x_232_, 0, v___x_250_);
v___x_252_ = v___x_232_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_247_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v_b_228_ = v___x_252_;
goto _start;
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
v___x_284_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0(v_inv_269_, v___x_283_);
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
v___x_312_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1));
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
v___x_343_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1(v___x_342_);
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
lean_dec_ref(v_fst_285_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(lean_object* v_mvarId_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_359_, v_x_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
v_a_375_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_366_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_366_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg___boxed(lean_object* v_mvarId_383_, lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_383_, v_x_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(lean_object* v_00_u03b1_391_, lean_object* v_mvarId_392_, lean_object* v_x_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_mvarId_392_, v_x_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___boxed(lean_object* v_00_u03b1_400_, lean_object* v_mvarId_401_, lean_object* v_x_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0(v_00_u03b1_400_, v_mvarId_401_, v_x_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(lean_object* v_e_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = l_Lean_Expr_hasMVar(v_e_409_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v_e_409_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v_mctx_415_; lean_object* v___x_416_; lean_object* v_fst_417_; lean_object* v_snd_418_; lean_object* v___x_419_; lean_object* v_cache_420_; lean_object* v_zetaDeltaFVarIds_421_; lean_object* v_postponed_422_; lean_object* v_diag_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_432_; 
v___x_414_ = lean_st_ref_get(v___y_410_);
v_mctx_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_mctx_415_);
lean_dec(v___x_414_);
v___x_416_ = l_Lean_instantiateMVarsCore(v_mctx_415_, v_e_409_);
v_fst_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_fst_417_);
v_snd_418_ = lean_ctor_get(v___x_416_, 1);
lean_inc(v_snd_418_);
lean_dec_ref(v___x_416_);
v___x_419_ = lean_st_ref_take(v___y_410_);
v_cache_420_ = lean_ctor_get(v___x_419_, 1);
v_zetaDeltaFVarIds_421_ = lean_ctor_get(v___x_419_, 2);
v_postponed_422_ = lean_ctor_get(v___x_419_, 3);
v_diag_423_ = lean_ctor_get(v___x_419_, 4);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v___x_419_, 0);
lean_dec(v_unused_433_);
v___x_425_ = v___x_419_;
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_diag_423_);
lean_inc(v_postponed_422_);
lean_inc(v_zetaDeltaFVarIds_421_);
lean_inc(v_cache_420_);
lean_dec(v___x_419_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v_snd_418_);
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_snd_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_cache_420_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_zetaDeltaFVarIds_421_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_postponed_422_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_diag_423_);
v___x_428_ = v_reuseFailAlloc_431_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_st_ref_set(v___y_410_, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_fst_417_);
return v___x_430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg___boxed(lean_object* v_e_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_434_, v___y_435_);
lean_dec(v___y_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(lean_object* v_e_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_e_438_, v___y_440_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___boxed(lean_object* v_e_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1(v_e_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(lean_object* v_inv_469_, uint8_t v___x_470_, lean_object* v___x_471_, lean_object* v_as_472_, size_t v_sz_473_, size_t v_i_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_a_482_; uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec(v_inv_469_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_b_475_);
return v___x_487_;
}
else
{
lean_object* v_a_488_; lean_object* v___x_489_; 
lean_dec_ref(v_b_475_);
v_a_488_ = lean_array_uget_borrowed(v_as_472_, v_i_474_);
lean_inc(v_a_488_);
v___x_489_ = l_Lean_MVarId_getType(v_a_488_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_551_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_551_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_551_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_551_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___y_496_; uint8_t v___y_497_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v_a_511_; lean_object* v___x_539_; 
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v___x_508_ = lean_unsigned_to_nat(2u);
v___x_509_ = lean_nat_dec_lt(v___x_471_, v___x_508_);
v___x_539_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_490_, v___y_477_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_539_);
v___x_541_ = l_Lean_Expr_consumeMData(v_a_540_);
lean_dec(v_a_540_);
v_a_511_ = v___x_541_;
goto v___jp_510_;
}
else
{
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_542_);
lean_dec_ref(v___x_539_);
v_a_511_ = v_a_542_;
goto v___jp_510_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_del_object(v___x_492_);
lean_dec(v_inv_469_);
v_a_543_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_539_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_539_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
v___jp_495_:
{
if (v___y_497_ == 0)
{
lean_dec_ref(v___y_496_);
lean_del_object(v___x_492_);
v_a_482_ = v___x_494_;
goto v___jp_481_;
}
else
{
lean_object* v_letMuts_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_letMuts_498_ = lean_ctor_get(v___y_496_, 3);
lean_inc_ref(v_letMuts_498_);
lean_dec_ref(v___y_496_);
v___x_499_ = l_Lean_instInhabitedExpr;
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_array_get(v___x_499_, v_letMuts_498_, v___x_500_);
lean_dec_ref(v_letMuts_498_);
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__3));
v___x_503_ = l_Lean_Expr_isAppOf(v___x_501_, v___x_502_);
lean_dec(v___x_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec(v_inv_469_);
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5));
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_504_);
v___x_506_ = v___x_492_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
lean_del_object(v___x_492_);
v_a_482_ = v___x_494_;
goto v___jp_481_;
}
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_512_, 0, v_a_511_);
lean_inc(v_a_488_);
v___x_513_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_488_, v___x_512_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_530_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_530_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_530_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_530_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
if (lean_obj_tag(v_a_514_) == 1)
{
lean_object* v_val_518_; lean_object* v_snd_519_; lean_object* v_snd_520_; lean_object* v___x_521_; 
v_val_518_ = lean_ctor_get(v_a_514_, 0);
lean_inc(v_val_518_);
lean_dec_ref(v_a_514_);
v_snd_519_ = lean_ctor_get(v_val_518_, 1);
lean_inc(v_snd_519_);
lean_dec(v_val_518_);
v_snd_520_ = lean_ctor_get(v_snd_519_, 1);
lean_inc(v_snd_520_);
lean_dec(v_snd_519_);
lean_inc(v_inv_469_);
v___x_521_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_520_, v_inv_469_);
lean_dec(v_snd_520_);
switch(lean_obj_tag(v___x_521_))
{
case 0:
{
lean_object* v_invariantUse_522_; lean_object* v_cursorSuffix_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
lean_del_object(v___x_516_);
v_invariantUse_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_invariantUse_522_);
lean_dec_ref(v___x_521_);
v_cursorSuffix_523_ = lean_ctor_get(v_invariantUse_522_, 2);
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_525_ = l_Lean_Expr_isAppOf(v_cursorSuffix_523_, v___x_524_);
if (v___x_525_ == 0)
{
v___y_496_ = v_invariantUse_522_;
v___y_497_ = v___x_470_;
goto v___jp_495_;
}
else
{
v___y_496_ = v_invariantUse_522_;
v___y_497_ = v___x_509_;
goto v___jp_495_;
}
}
case 1:
{
lean_del_object(v___x_516_);
lean_del_object(v___x_492_);
v_a_482_ = v___x_494_;
goto v___jp_481_;
}
default: 
{
lean_object* v___x_526_; lean_object* v___x_528_; 
lean_del_object(v___x_492_);
lean_dec(v_inv_469_);
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__5));
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_528_ = v___x_516_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_del_object(v___x_492_);
v_a_482_ = v___x_494_;
goto v___jp_481_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_492_);
lean_dec(v_inv_469_);
v_a_531_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_513_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_513_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
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
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_inv_469_);
v_a_552_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_489_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_489_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object* v_inv_560_, lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v_as_563_, lean_object* v_sz_564_, lean_object* v_i_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___x_5242__boxed_572_; size_t v_sz_boxed_573_; size_t v_i_boxed_574_; lean_object* v_res_575_; 
v___x_5242__boxed_572_ = lean_unbox(v___x_561_);
v_sz_boxed_573_ = lean_unbox_usize(v_sz_564_);
lean_dec(v_sz_564_);
v_i_boxed_574_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_560_, v___x_5242__boxed_572_, v___x_562_, v_as_563_, v_sz_boxed_573_, v_i_boxed_574_, v_b_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_as_563_);
lean_dec(v___x_562_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(lean_object* v_vcs_580_, lean_object* v_inv_581_, lean_object* v_letMutsTy_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__0));
v___x_595_ = l_Lean_Expr_isAppOf(v_letMutsTy_582_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec(v_inv_581_);
goto v___jp_588_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = l_Lean_Expr_getAppNumArgs(v_letMutsTy_582_);
v___x_597_ = lean_unsigned_to_nat(2u);
v___x_598_ = lean_nat_dec_lt(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_sub(v___x_596_, v___x_599_);
lean_inc(v___x_600_);
v___x_601_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_582_, v___x_600_);
v___x_602_ = l_Lean_Expr_cleanupAnnotations(v___x_601_);
v___x_603_ = l_Lean_Expr_isApp(v___x_602_);
if (v___x_603_ == 0)
{
lean_dec_ref(v___x_602_);
lean_dec(v___x_600_);
lean_dec(v___x_596_);
lean_dec(v_inv_581_);
goto v___jp_591_;
}
else
{
lean_object* v_arg_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_arg_604_ = lean_ctor_get(v___x_602_, 1);
lean_inc_ref(v_arg_604_);
v___x_605_ = l_Lean_Expr_appFnCleanup___redArg(v___x_602_);
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___closed__1));
v___x_607_ = l_Lean_Expr_isConstOf(v___x_605_, v___x_606_);
lean_dec_ref(v___x_605_);
if (v___x_607_ == 0)
{
lean_dec_ref(v_arg_604_);
lean_dec(v___x_600_);
lean_dec(v___x_596_);
lean_dec(v_inv_581_);
goto v___jp_591_;
}
else
{
lean_object* v___x_608_; size_t v_sz_609_; size_t v___x_610_; lean_object* v___x_611_; 
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__0));
v_sz_609_ = lean_array_size(v_vcs_580_);
v___x_610_ = ((size_t)0ULL);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_581_, v___x_607_, v___x_596_, v_vcs_580_, v_sz_609_, v___x_610_, v___x_608_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v___x_596_);
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
v_00_u03c3_621_ = l_Lean_Expr_getRevArg_x21(v_letMutsTy_582_, v___x_620_);
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
lean_dec_ref(v_fst_616_);
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
lean_dec(v___x_596_);
lean_dec(v_inv_581_);
goto v___jp_588_;
}
}
v___jp_588_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_box(0);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
v___jp_591_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn___boxed(lean_object* v_vcs_644_, lean_object* v_inv_645_, lean_object* v_letMutsTy_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_vcs_644_, v_inv_645_, v_letMutsTy_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_letMutsTy_646_);
lean_dec_ref(v_vcs_644_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(size_t v_sz_653_, size_t v_i_654_, lean_object* v_bs_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = lean_usize_dec_lt(v_i_654_, v_sz_653_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v_bs_655_);
return v___x_662_;
}
else
{
lean_object* v_v_663_; lean_object* v___x_664_; 
v_v_663_ = lean_array_uget_borrowed(v_bs_655_, v_i_654_);
lean_inc(v___y_659_);
lean_inc_ref(v___y_658_);
lean_inc(v___y_657_);
lean_inc_ref(v___y_656_);
lean_inc(v_v_663_);
v___x_664_ = lean_infer_type(v_v_663_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_666_; lean_object* v_bs_x27_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = lean_unsigned_to_nat(0u);
v_bs_x27_667_ = lean_array_uset(v_bs_655_, v_i_654_, v___x_666_);
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_add(v_i_654_, v___x_668_);
v___x_670_ = lean_array_uset(v_bs_x27_667_, v_i_654_, v_a_665_);
v_i_654_ = v___x_669_;
v_bs_655_ = v___x_670_;
goto _start;
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_bs_655_);
v_a_672_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_664_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_664_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0___boxed(lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_bs_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
size_t v_sz_boxed_688_; size_t v_i_boxed_689_; lean_object* v_res_690_; 
v_sz_boxed_688_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_689_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_boxed_688_, v_i_boxed_689_, v_bs_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_dontRevert_691_, lean_object* v_as_692_, size_t v_i_693_, size_t v_stop_694_, lean_object* v_b_695_){
_start:
{
lean_object* v___y_697_; uint8_t v___x_701_; 
v___x_701_ = lean_usize_dec_eq(v_i_693_, v_stop_694_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_702_ = lean_array_uget_borrowed(v_as_692_, v_i_693_);
v___x_703_ = l_Lean_Expr_fvarId_x21(v___x_702_);
lean_inc_ref(v_dontRevert_691_);
v___x_704_ = lean_apply_1(v_dontRevert_691_, v___x_703_);
v___x_705_ = lean_unbox(v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_inc(v___x_702_);
v___x_706_ = lean_array_push(v_b_695_, v___x_702_);
v___y_697_ = v___x_706_;
goto v___jp_696_;
}
else
{
v___y_697_ = v_b_695_;
goto v___jp_696_;
}
}
else
{
lean_dec_ref(v_dontRevert_691_);
return v_b_695_;
}
v___jp_696_:
{
size_t v___x_698_; size_t v___x_699_; 
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_693_, v___x_698_);
v_i_693_ = v___x_699_;
v_b_695_ = v___y_697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_dontRevert_707_, lean_object* v_as_708_, lean_object* v_i_709_, lean_object* v_stop_710_, lean_object* v_b_711_){
_start:
{
size_t v_i_boxed_712_; size_t v_stop_boxed_713_; lean_object* v_res_714_; 
v_i_boxed_712_ = lean_unbox_usize(v_i_709_);
lean_dec(v_i_709_);
v_stop_boxed_713_ = lean_unbox_usize(v_stop_710_);
lean_dec(v_stop_710_);
v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_707_, v_as_708_, v_i_boxed_712_, v_stop_boxed_713_, v_b_711_);
lean_dec_ref(v_as_708_);
return v_res_714_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object* v_a_715_, lean_object* v_x_716_){
_start:
{
if (lean_obj_tag(v_x_716_) == 0)
{
uint8_t v___x_717_; 
v___x_717_ = 0;
return v___x_717_;
}
else
{
lean_object* v_key_718_; lean_object* v_tail_719_; uint8_t v___x_720_; 
v_key_718_ = lean_ctor_get(v_x_716_, 0);
v_tail_719_ = lean_ctor_get(v_x_716_, 2);
v___x_720_ = lean_expr_eqv(v_key_718_, v_a_715_);
if (v___x_720_ == 0)
{
v_x_716_ = v_tail_719_;
goto _start;
}
else
{
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_a_722_, lean_object* v_x_723_){
_start:
{
uint8_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_722_, v_x_723_);
lean_dec(v_x_723_);
lean_dec_ref(v_a_722_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
return v_x_726_;
}
else
{
lean_object* v_key_728_; lean_object* v_value_729_; lean_object* v_tail_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_753_; 
v_key_728_ = lean_ctor_get(v_x_727_, 0);
v_value_729_ = lean_ctor_get(v_x_727_, 1);
v_tail_730_ = lean_ctor_get(v_x_727_, 2);
v_isSharedCheck_753_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_753_ == 0)
{
v___x_732_ = v_x_727_;
v_isShared_733_ = v_isSharedCheck_753_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_tail_730_);
lean_inc(v_value_729_);
lean_inc(v_key_728_);
lean_dec(v_x_727_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_753_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v___x_737_; uint64_t v_fold_738_; uint64_t v___x_739_; uint64_t v___x_740_; uint64_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_734_ = lean_array_get_size(v_x_726_);
v___x_735_ = l_Lean_Expr_hash(v_key_728_);
v___x_736_ = 32ULL;
v___x_737_ = lean_uint64_shift_right(v___x_735_, v___x_736_);
v_fold_738_ = lean_uint64_xor(v___x_735_, v___x_737_);
v___x_739_ = 16ULL;
v___x_740_ = lean_uint64_shift_right(v_fold_738_, v___x_739_);
v___x_741_ = lean_uint64_xor(v_fold_738_, v___x_740_);
v___x_742_ = lean_uint64_to_usize(v___x_741_);
v___x_743_ = lean_usize_of_nat(v___x_734_);
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_sub(v___x_743_, v___x_744_);
v___x_746_ = lean_usize_land(v___x_742_, v___x_745_);
v___x_747_ = lean_array_uget_borrowed(v_x_726_, v___x_746_);
lean_inc(v___x_747_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 2, v___x_747_);
v___x_749_ = v___x_732_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_key_728_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_value_729_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v___x_747_);
v___x_749_ = v_reuseFailAlloc_752_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_array_uset(v_x_726_, v___x_746_, v___x_749_);
v_x_726_ = v___x_750_;
v_x_727_ = v_tail_730_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_i_754_, lean_object* v_source_755_, lean_object* v_target_756_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_array_get_size(v_source_755_);
v___x_758_ = lean_nat_dec_lt(v_i_754_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec_ref(v_source_755_);
lean_dec(v_i_754_);
return v_target_756_;
}
else
{
lean_object* v_es_759_; lean_object* v___x_760_; lean_object* v_source_761_; lean_object* v_target_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_es_759_ = lean_array_fget(v_source_755_, v_i_754_);
v___x_760_ = lean_box(0);
v_source_761_ = lean_array_fset(v_source_755_, v_i_754_, v___x_760_);
v_target_762_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_target_756_, v_es_759_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_i_754_, v___x_763_);
lean_dec(v_i_754_);
v_i_754_ = v___x_764_;
v_source_755_ = v_source_761_;
v_target_756_ = v_target_762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(lean_object* v_data_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_nbuckets_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_767_ = lean_array_get_size(v_data_766_);
v___x_768_ = lean_unsigned_to_nat(2u);
v_nbuckets_769_ = lean_nat_mul(v___x_767_, v___x_768_);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_box(0);
v___x_772_ = lean_mk_array(v_nbuckets_769_, v___x_771_);
v___x_773_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v___x_770_, v_data_766_, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_774_, lean_object* v_a_775_, lean_object* v_b_776_){
_start:
{
lean_object* v_size_777_; lean_object* v_buckets_778_; lean_object* v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v_fold_783_; uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v_bkt_792_; uint8_t v___x_793_; 
v_size_777_ = lean_ctor_get(v_m_774_, 0);
v_buckets_778_ = lean_ctor_get(v_m_774_, 1);
v___x_779_ = lean_array_get_size(v_buckets_778_);
v___x_780_ = l_Lean_Expr_hash(v_a_775_);
v___x_781_ = 32ULL;
v___x_782_ = lean_uint64_shift_right(v___x_780_, v___x_781_);
v_fold_783_ = lean_uint64_xor(v___x_780_, v___x_782_);
v___x_784_ = 16ULL;
v___x_785_ = lean_uint64_shift_right(v_fold_783_, v___x_784_);
v___x_786_ = lean_uint64_xor(v_fold_783_, v___x_785_);
v___x_787_ = lean_uint64_to_usize(v___x_786_);
v___x_788_ = lean_usize_of_nat(v___x_779_);
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_sub(v___x_788_, v___x_789_);
v___x_791_ = lean_usize_land(v___x_787_, v___x_790_);
v_bkt_792_ = lean_array_uget_borrowed(v_buckets_778_, v___x_791_);
v___x_793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_775_, v_bkt_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_814_; 
lean_inc_ref(v_buckets_778_);
lean_inc(v_size_777_);
v_isSharedCheck_814_ = !lean_is_exclusive(v_m_774_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; lean_object* v_unused_816_; 
v_unused_815_ = lean_ctor_get(v_m_774_, 1);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_m_774_, 0);
lean_dec(v_unused_816_);
v___x_795_ = v_m_774_;
v_isShared_796_ = v_isSharedCheck_814_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_m_774_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_814_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v_size_x27_798_; lean_object* v___x_799_; lean_object* v_buckets_x27_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v_size_x27_798_ = lean_nat_add(v_size_777_, v___x_797_);
lean_dec(v_size_777_);
lean_inc(v_bkt_792_);
v___x_799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_799_, 0, v_a_775_);
lean_ctor_set(v___x_799_, 1, v_b_776_);
lean_ctor_set(v___x_799_, 2, v_bkt_792_);
v_buckets_x27_800_ = lean_array_uset(v_buckets_778_, v___x_791_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(4u);
v___x_802_ = lean_nat_mul(v_size_x27_798_, v___x_801_);
v___x_803_ = lean_unsigned_to_nat(3u);
v___x_804_ = lean_nat_div(v___x_802_, v___x_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_array_get_size(v_buckets_x27_800_);
v___x_806_ = lean_nat_dec_le(v___x_804_, v___x_805_);
lean_dec(v___x_804_);
if (v___x_806_ == 0)
{
lean_object* v_val_807_; lean_object* v___x_809_; 
v_val_807_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_buckets_x27_800_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_val_807_);
lean_ctor_set(v___x_795_, 0, v_size_x27_798_);
v___x_809_ = v___x_795_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_size_x27_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_val_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v___x_812_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_buckets_x27_800_);
lean_ctor_set(v___x_795_, 0, v_size_x27_798_);
v___x_812_ = v___x_795_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_size_x27_798_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_buckets_x27_800_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_dec(v_b_776_);
lean_dec_ref(v_a_775_);
return v_m_774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_as_817_, size_t v_sz_818_, size_t v_i_819_, lean_object* v_b_820_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = lean_usize_dec_lt(v_i_819_, v_sz_818_);
if (v___x_821_ == 0)
{
return v_b_820_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_823_; lean_object* v_r_824_; size_t v___x_825_; size_t v___x_826_; 
v_a_822_ = lean_array_uget_borrowed(v_as_817_, v_i_819_);
v___x_823_ = lean_box(0);
lean_inc(v_a_822_);
v_r_824_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_820_, v_a_822_, v___x_823_);
v___x_825_ = ((size_t)1ULL);
v___x_826_ = lean_usize_add(v_i_819_, v___x_825_);
v_i_819_ = v___x_826_;
v_b_820_ = v_r_824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_as_828_, lean_object* v_sz_829_, lean_object* v_i_830_, lean_object* v_b_831_){
_start:
{
size_t v_sz_boxed_832_; size_t v_i_boxed_833_; lean_object* v_res_834_; 
v_sz_boxed_832_ = lean_unbox_usize(v_sz_829_);
lean_dec(v_sz_829_);
v_i_boxed_833_ = lean_unbox_usize(v_i_830_);
lean_dec(v_i_830_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_828_, v_sz_boxed_832_, v_i_boxed_833_, v_b_831_);
lean_dec_ref(v_as_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_835_, lean_object* v_l_836_){
_start:
{
size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; 
v_sz_837_ = lean_array_size(v_l_836_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_l_836_, v_sz_837_, v___x_838_, v_m_835_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_840_, lean_object* v_l_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_840_, v_l_841_);
lean_dec_ref(v_l_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(lean_object* v_dontRevert_843_, lean_object* v_as_844_, size_t v_i_845_, size_t v_stop_846_, lean_object* v_b_847_){
_start:
{
lean_object* v___y_849_; uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_eq(v_i_845_, v_stop_846_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_854_ = lean_array_uget_borrowed(v_as_844_, v_i_845_);
lean_inc_ref(v_dontRevert_843_);
lean_inc(v___x_854_);
v___x_855_ = lean_apply_1(v_dontRevert_843_, v___x_854_);
v___x_856_ = lean_unbox(v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_inc(v___x_854_);
v___x_857_ = lean_array_push(v_b_847_, v___x_854_);
v___y_849_ = v___x_857_;
goto v___jp_848_;
}
else
{
v___y_849_ = v_b_847_;
goto v___jp_848_;
}
}
else
{
lean_dec_ref(v_dontRevert_843_);
return v_b_847_;
}
v___jp_848_:
{
size_t v___x_850_; size_t v___x_851_; 
v___x_850_ = ((size_t)1ULL);
v___x_851_ = lean_usize_add(v_i_845_, v___x_850_);
v_i_845_ = v___x_851_;
v_b_847_ = v___y_849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2___boxed(lean_object* v_dontRevert_858_, lean_object* v_as_859_, lean_object* v_i_860_, lean_object* v_stop_861_, lean_object* v_b_862_){
_start:
{
size_t v_i_boxed_863_; size_t v_stop_boxed_864_; lean_object* v_res_865_; 
v_i_boxed_863_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_stop_boxed_864_ = lean_unbox_usize(v_stop_861_);
lean_dec(v_stop_861_);
v_res_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_858_, v_as_859_, v_i_boxed_863_, v_stop_boxed_864_, v_b_862_);
lean_dec_ref(v_as_859_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_866_, size_t v_i_867_, size_t v_stop_868_, lean_object* v_b_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_eq(v_i_867_, v_stop_868_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; size_t v___x_873_; size_t v___x_874_; 
v___x_871_ = lean_array_uget_borrowed(v_as_866_, v_i_867_);
lean_inc(v___x_871_);
v___x_872_ = l_Lean_collectFVars(v_b_869_, v___x_871_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_867_, v___x_873_);
v_i_867_ = v___x_874_;
v_b_869_ = v___x_872_;
goto _start;
}
else
{
return v_b_869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_876_, lean_object* v_i_877_, lean_object* v_stop_878_, lean_object* v_b_879_){
_start:
{
size_t v_i_boxed_880_; size_t v_stop_boxed_881_; lean_object* v_res_882_; 
v_i_boxed_880_ = lean_unbox_usize(v_i_877_);
lean_dec(v_i_877_);
v_stop_boxed_881_ = lean_unbox_usize(v_stop_878_);
lean_dec(v_stop_878_);
v_res_882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_876_, v_i_boxed_880_, v_stop_boxed_881_, v_b_879_);
lean_dec_ref(v_as_876_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(size_t v_sz_883_, size_t v_i_884_, lean_object* v_bs_885_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = lean_usize_dec_lt(v_i_884_, v_sz_883_);
if (v___x_886_ == 0)
{
return v_bs_885_;
}
else
{
lean_object* v_v_887_; lean_object* v___x_888_; lean_object* v_bs_x27_889_; lean_object* v___x_890_; size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
v_v_887_ = lean_array_uget(v_bs_885_, v_i_884_);
v___x_888_ = lean_unsigned_to_nat(0u);
v_bs_x27_889_ = lean_array_uset(v_bs_885_, v_i_884_, v___x_888_);
v___x_890_ = l_Lean_mkFVar(v_v_887_);
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_i_884_, v___x_891_);
v___x_893_ = lean_array_uset(v_bs_x27_889_, v_i_884_, v___x_890_);
v_i_884_ = v___x_892_;
v_bs_885_ = v___x_893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1___boxed(lean_object* v_sz_895_, lean_object* v_i_896_, lean_object* v_bs_897_){
_start:
{
size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_895_);
lean_dec(v_sz_895_);
v_i_boxed_899_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_boxed_898_, v_i_boxed_899_, v_bs_897_);
return v_res_900_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_box(0);
v___x_904_ = lean_unsigned_to_nat(16u);
v___x_905_ = lean_mk_array(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__1);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_909_, lean_object* v_b_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
uint8_t v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; 
v___x_916_ = 0;
v___x_917_ = 1;
lean_inc_ref(v_b_910_);
v___x_918_ = l_Lean_Meta_collectForwardDeps(v_b_910_, v___x_916_, v___x_917_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_992_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_992_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_992_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_992_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; size_t v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___x_937_; lean_object* v___x_938_; size_t v___y_940_; lean_object* v___y_941_; lean_object* v_fvarIds_942_; size_t v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_956_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_box(1);
v___x_938_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__0));
v___x_983_ = lean_array_get_size(v_a_919_);
v___x_984_ = lean_nat_dec_lt(v___x_923_, v___x_983_);
if (v___x_984_ == 0)
{
lean_dec(v_a_919_);
v___y_956_ = v___x_938_;
goto v___jp_955_;
}
else
{
uint8_t v___x_985_; 
v___x_985_ = lean_nat_dec_le(v___x_983_, v___x_983_);
if (v___x_985_ == 0)
{
if (v___x_984_ == 0)
{
lean_dec(v_a_919_);
v___y_956_ = v___x_938_;
goto v___jp_955_;
}
else
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_983_);
lean_inc_ref(v_dontRevert_909_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_909_, v_a_919_, v___x_986_, v___x_987_, v___x_938_);
lean_dec(v_a_919_);
v___y_956_ = v___x_988_;
goto v___jp_955_;
}
}
else
{
size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_989_ = ((size_t)0ULL);
v___x_990_ = lean_usize_of_nat(v___x_983_);
lean_inc_ref(v_dontRevert_909_);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_909_, v_a_919_, v___x_989_, v___x_990_, v___x_938_);
lean_dec(v_a_919_);
v___y_956_ = v___x_991_;
goto v___jp_955_;
}
}
v___jp_924_:
{
size_t v_sz_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_sz_928_ = lean_array_size(v___y_927_);
lean_inc_ref(v___y_927_);
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_928_, v___y_925_, v___y_927_);
v___x_930_ = l_Array_append___redArg(v___y_926_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = lean_array_get_size(v___y_927_);
lean_dec_ref(v___y_927_);
v___x_932_ = lean_nat_dec_eq(v___x_931_, v___x_923_);
if (v___x_932_ == 0)
{
lean_del_object(v___x_921_);
v_b_910_ = v___x_930_;
goto _start;
}
else
{
lean_object* v___x_935_; 
lean_dec_ref(v_dontRevert_909_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_930_);
v___x_935_ = v___x_921_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
v___jp_939_:
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_array_get_size(v_fvarIds_942_);
v___x_944_ = lean_nat_dec_lt(v___x_923_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_fvarIds_942_);
v___y_925_ = v___y_940_;
v___y_926_ = v___y_941_;
v___y_927_ = v___x_938_;
goto v___jp_924_;
}
else
{
uint8_t v___x_945_; 
v___x_945_ = lean_nat_dec_le(v___x_943_, v___x_943_);
if (v___x_945_ == 0)
{
if (v___x_944_ == 0)
{
lean_dec_ref(v_fvarIds_942_);
v___y_925_ = v___y_940_;
v___y_926_ = v___y_941_;
v___y_927_ = v___x_938_;
goto v___jp_924_;
}
else
{
size_t v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_usize_of_nat(v___x_943_);
lean_inc_ref(v_dontRevert_909_);
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_909_, v_fvarIds_942_, v___y_940_, v___x_946_, v___x_938_);
lean_dec_ref(v_fvarIds_942_);
v___y_925_ = v___y_940_;
v___y_926_ = v___y_941_;
v___y_927_ = v___x_947_;
goto v___jp_924_;
}
}
else
{
size_t v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_usize_of_nat(v___x_943_);
lean_inc_ref(v_dontRevert_909_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_909_, v_fvarIds_942_, v___y_940_, v___x_948_, v___x_938_);
lean_dec_ref(v_fvarIds_942_);
v___y_925_ = v___y_940_;
v___y_926_ = v___y_941_;
v___y_927_ = v___x_949_;
goto v___jp_924_;
}
}
}
v___jp_950_:
{
lean_object* v_fvarIds_954_; 
v_fvarIds_954_ = lean_ctor_get(v___y_953_, 2);
lean_inc_ref(v_fvarIds_954_);
lean_dec_ref(v___y_953_);
v___y_940_ = v___y_951_;
v___y_941_ = v___y_952_;
v_fvarIds_942_ = v_fvarIds_954_;
goto v___jp_939_;
}
v___jp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = lean_array_get_size(v___y_956_);
v___x_958_ = lean_array_get_size(v_b_910_);
lean_dec_ref(v_b_910_);
v___x_959_ = lean_nat_dec_eq(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
size_t v_sz_960_; size_t v___x_961_; lean_object* v___x_962_; 
v_sz_960_ = lean_array_size(v___y_956_);
v___x_961_ = ((size_t)0ULL);
lean_inc_ref(v___y_956_);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_960_, v___x_961_, v___y_956_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_962_);
v___x_964_ = lean_array_get_size(v_a_963_);
v___x_965_ = lean_nat_dec_lt(v___x_923_, v___x_964_);
if (v___x_965_ == 0)
{
lean_dec(v_a_963_);
v___y_940_ = v___x_961_;
v___y_941_ = v___y_956_;
v_fvarIds_942_ = v___x_938_;
goto v___jp_939_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_966_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2);
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_966_, v___y_956_);
v___x_968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_937_);
lean_ctor_set(v___x_968_, 2, v___x_938_);
v___x_969_ = lean_nat_dec_le(v___x_964_, v___x_964_);
if (v___x_969_ == 0)
{
if (v___x_965_ == 0)
{
lean_dec_ref(v___x_968_);
lean_dec(v_a_963_);
v___y_940_ = v___x_961_;
v___y_941_ = v___y_956_;
v_fvarIds_942_ = v___x_938_;
goto v___jp_939_;
}
else
{
size_t v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_usize_of_nat(v___x_964_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_963_, v___x_961_, v___x_970_, v___x_968_);
lean_dec(v_a_963_);
v___y_951_ = v___x_961_;
v___y_952_ = v___y_956_;
v___y_953_ = v___x_971_;
goto v___jp_950_;
}
}
else
{
size_t v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_usize_of_nat(v___x_964_);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_963_, v___x_961_, v___x_972_, v___x_968_);
lean_dec(v_a_963_);
v___y_951_ = v___x_961_;
v___y_952_ = v___y_956_;
v___y_953_ = v___x_973_;
goto v___jp_950_;
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___y_956_);
lean_del_object(v___x_921_);
lean_dec_ref(v_dontRevert_909_);
v_a_974_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_962_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_962_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v___x_982_; 
lean_del_object(v___x_921_);
lean_dec_ref(v_dontRevert_909_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___y_956_);
return v___x_982_;
}
}
}
}
else
{
lean_dec_ref(v_b_910_);
lean_dec_ref(v_dontRevert_909_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_993_, v_b_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1000_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__0));
v___x_1002_ = lean_box(1);
v___x_1003_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__2);
v___x_1004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
lean_ctor_set(v___x_1004_, 2, v___x_1001_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_1005_, lean_object* v_dontRevert_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___y_1013_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_fvarIds_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___closed__0));
v___x_1020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_1021_ = l_Lean_collectFVars(v___x_1020_, v_e_1005_);
v_fvarIds_1022_ = lean_ctor_get(v___x_1021_, 2);
lean_inc_ref(v_fvarIds_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = lean_array_get_size(v_fvarIds_1022_);
v___x_1024_ = lean_nat_dec_lt(v___x_1018_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec_ref(v_fvarIds_1022_);
v___y_1013_ = v___x_1019_;
goto v___jp_1012_;
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_le(v___x_1023_, v___x_1023_);
if (v___x_1025_ == 0)
{
if (v___x_1024_ == 0)
{
lean_dec_ref(v_fvarIds_1022_);
v___y_1013_ = v___x_1019_;
goto v___jp_1012_;
}
else
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = lean_usize_of_nat(v___x_1023_);
lean_inc_ref(v_dontRevert_1006_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1006_, v_fvarIds_1022_, v___x_1026_, v___x_1027_, v___x_1019_);
lean_dec_ref(v_fvarIds_1022_);
v___y_1013_ = v___x_1028_;
goto v___jp_1012_;
}
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = lean_usize_of_nat(v___x_1023_);
lean_inc_ref(v_dontRevert_1006_);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1006_, v_fvarIds_1022_, v___x_1029_, v___x_1030_, v___x_1019_);
lean_dec_ref(v_fvarIds_1022_);
v___y_1013_ = v___x_1031_;
goto v___jp_1012_;
}
}
v___jp_1012_:
{
size_t v_sz_1014_; size_t v___x_1015_; lean_object* v_xs_1016_; lean_object* v___x_1017_; 
v_sz_1014_ = lean_array_size(v___y_1013_);
v___x_1015_ = ((size_t)0ULL);
v_xs_1016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1014_, v___x_1015_, v___y_1013_);
v___x_1017_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1006_, v_xs_1016_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1032_, lean_object* v_dontRevert_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1032_, v_dontRevert_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1040_, lean_object* v_m_1041_, lean_object* v_a_1042_, lean_object* v_b_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1041_, v_a_1042_, v_b_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1045_, lean_object* v_a_1046_, lean_object* v_x_1047_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_1046_, v_x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_a_1050_, lean_object* v_x_1051_){
_start:
{
uint8_t v_res_1052_; lean_object* v_r_1053_; 
v_res_1052_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1049_, v_a_1050_, v_x_1051_);
lean_dec(v_x_1051_);
lean_dec_ref(v_a_1050_);
v_r_1053_ = lean_box(v_res_1052_);
return v_r_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1054_, lean_object* v_data_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_data_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1057_, lean_object* v_i_1058_, lean_object* v_source_1059_, lean_object* v_target_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v_i_1058_, v_source_1059_, v_target_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1072_, lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v_i_1075_, lean_object* v_a_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_zero_1082_; uint8_t v_isZero_1083_; 
v_zero_1082_ = lean_unsigned_to_nat(0u);
v_isZero_1083_ = lean_nat_dec_eq(v_i_1075_, v_zero_1082_);
if (v_isZero_1083_ == 1)
{
lean_object* v___x_1084_; 
lean_dec(v_i_1075_);
lean_dec(v___x_1074_);
lean_dec_ref(v___x_1073_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_a_1076_);
return v___x_1084_;
}
else
{
lean_object* v_one_1085_; lean_object* v_n_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_one_1085_ = lean_unsigned_to_nat(1u);
v_n_1086_ = lean_nat_sub(v_i_1075_, v_one_1085_);
lean_dec(v_i_1075_);
v___x_1087_ = lean_array_fget_borrowed(v_a_1072_, v_n_1086_);
lean_inc_ref(v___x_1073_);
v___x_1088_ = l_Lean_LocalContext_getFVar_x21(v___x_1073_, v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_userName_1089_; lean_object* v_type_1090_; uint8_t v_bi_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_userName_1089_ = lean_ctor_get(v___x_1088_, 2);
lean_inc(v_userName_1089_);
v_type_1090_ = lean_ctor_get(v___x_1088_, 3);
lean_inc_ref(v_type_1090_);
v_bi_1091_ = lean_ctor_get_uint8(v___x_1088_, sizeof(void*)*4);
lean_dec_ref(v___x_1088_);
v___x_1092_ = l_Lean_Expr_headBeta(v_type_1090_);
v___x_1093_ = lean_expr_abstract_range(v___x_1092_, v_n_1086_, v_a_1072_);
lean_dec_ref(v___x_1092_);
lean_inc_ref(v___x_1093_);
v___x_1094_ = l_Lean_Meta_getLevel(v___x_1093_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref(v___x_1094_);
v___x_1096_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1097_ = lean_box(0);
lean_inc_n(v___x_1074_, 2);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1074_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1095_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_mkConst(v___x_1096_, v___x_1099_);
v___x_1101_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1074_);
lean_inc_ref(v___x_1093_);
v___x_1102_ = l_Lean_mkLambda(v_userName_1089_, v_bi_1091_, v___x_1093_, v_a_1076_);
v___x_1103_ = l_Lean_mkApp3(v___x_1100_, v___x_1093_, v___x_1101_, v___x_1102_);
v_i_1075_ = v_n_1086_;
v_a_1076_ = v___x_1103_;
goto _start;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___x_1093_);
lean_dec(v_userName_1089_);
lean_dec(v_n_1086_);
lean_dec_ref(v_a_1076_);
lean_dec(v___x_1074_);
lean_dec_ref(v___x_1073_);
v_a_1105_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1094_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1094_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
uint8_t v_nondep_1113_; 
v_nondep_1113_ = lean_ctor_get_uint8(v___x_1088_, sizeof(void*)*5);
if (v_nondep_1113_ == 0)
{
lean_object* v_userName_1114_; lean_object* v_type_1115_; lean_object* v_value_1116_; uint8_t v___x_1117_; 
v_userName_1114_ = lean_ctor_get(v___x_1088_, 2);
lean_inc(v_userName_1114_);
v_type_1115_ = lean_ctor_get(v___x_1088_, 3);
lean_inc_ref(v_type_1115_);
v_value_1116_ = lean_ctor_get(v___x_1088_, 4);
lean_inc_ref(v_value_1116_);
lean_dec_ref(v___x_1088_);
v___x_1117_ = lean_expr_has_loose_bvar(v_a_1076_, v_zero_1082_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v_value_1116_);
lean_dec_ref(v_type_1115_);
lean_dec(v_userName_1114_);
v___x_1118_ = lean_expr_lower_loose_bvars(v_a_1076_, v_one_1085_, v_one_1085_);
lean_dec_ref(v_a_1076_);
v_i_1075_ = v_n_1086_;
v_a_1076_ = v___x_1118_;
goto _start;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1120_ = l_Lean_Expr_headBeta(v_type_1115_);
v___x_1121_ = lean_expr_abstract_range(v___x_1120_, v_n_1086_, v_a_1072_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = lean_expr_abstract_range(v_value_1116_, v_n_1086_, v_a_1072_);
lean_dec_ref(v_value_1116_);
v___x_1123_ = l_Lean_Expr_letE___override(v_userName_1114_, v___x_1121_, v___x_1122_, v_a_1076_, v_nondep_1113_);
v_i_1075_ = v_n_1086_;
v_a_1076_ = v___x_1123_;
goto _start;
}
}
else
{
lean_object* v_userName_1125_; lean_object* v_type_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_userName_1125_ = lean_ctor_get(v___x_1088_, 2);
lean_inc(v_userName_1125_);
v_type_1126_ = lean_ctor_get(v___x_1088_, 3);
lean_inc_ref(v_type_1126_);
lean_dec_ref(v___x_1088_);
v___x_1127_ = l_Lean_Expr_headBeta(v_type_1126_);
v___x_1128_ = lean_expr_abstract_range(v___x_1127_, v_n_1086_, v_a_1072_);
lean_dec_ref(v___x_1127_);
lean_inc_ref(v___x_1128_);
v___x_1129_ = l_Lean_Meta_getLevel(v___x_1128_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1132_ = lean_box(0);
lean_inc_n(v___x_1074_, 2);
v___x_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1074_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_a_1130_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_mkConst(v___x_1131_, v___x_1134_);
v___x_1136_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1074_);
v___x_1137_ = 0;
lean_inc_ref(v___x_1128_);
v___x_1138_ = l_Lean_mkLambda(v_userName_1125_, v___x_1137_, v___x_1128_, v_a_1076_);
v___x_1139_ = l_Lean_mkApp3(v___x_1135_, v___x_1128_, v___x_1136_, v___x_1138_);
v_i_1075_ = v_n_1086_;
v_a_1076_ = v___x_1139_;
goto _start;
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v___x_1128_);
lean_dec(v_userName_1125_);
lean_dec(v_n_1086_);
lean_dec_ref(v_a_1076_);
lean_dec(v___x_1074_);
lean_dec_ref(v___x_1073_);
v_a_1141_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1129_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1129_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1149_, lean_object* v___x_1150_, lean_object* v___x_1151_, lean_object* v_i_1152_, lean_object* v_a_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1149_, v___x_1150_, v___x_1151_, v_i_1152_, v_a_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_a_1149_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1164_, lean_object* v_dontRevert_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; 
lean_inc_ref(v_e_1164_);
v___x_1171_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1164_, v_dontRevert_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_lctx_1173_; lean_object* v___x_1174_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
v_lctx_1173_ = lean_ctor_get(v_a_1166_, 2);
lean_inc(v_a_1169_);
lean_inc_ref(v_a_1168_);
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
lean_inc_ref(v_e_1164_);
v___x_1174_ = lean_infer_type(v_e_1164_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1197_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1197_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1197_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = l_Lean_Expr_cleanupAnnotations(v_a_1175_);
v___x_1180_ = l_Lean_Expr_isApp(v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1182_; 
lean_dec_ref(v___x_1179_);
lean_dec(v_a_1172_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_e_1164_);
v___x_1182_ = v___x_1177_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_e_1164_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1179_);
v___x_1185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1186_ = l_Lean_Expr_isConstOf(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1188_; 
lean_dec_ref(v___x_1184_);
lean_dec(v_a_1172_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_e_1164_);
v___x_1188_ = v___x_1177_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_e_1164_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_del_object(v___x_1177_);
v___x_1190_ = lean_box(0);
v___x_1191_ = l_Lean_Expr_constLevels_x21(v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = l_List_get_x21Internal___redArg(v___x_1190_, v___x_1191_, v___x_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_array_get_size(v_a_1172_);
v___x_1195_ = lean_expr_abstract(v_e_1164_, v_a_1172_);
lean_dec_ref(v_e_1164_);
lean_inc_ref(v_lctx_1173_);
v___x_1196_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1172_, v_lctx_1173_, v___x_1193_, v___x_1194_, v___x_1195_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1172_);
return v___x_1196_;
}
}
}
}
else
{
lean_dec(v_a_1172_);
lean_dec_ref(v_e_1164_);
return v___x_1174_;
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_e_1164_);
v_a_1198_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1171_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1171_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1206_, lean_object* v_dontRevert_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1206_, v_dontRevert_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v_n_1217_, lean_object* v_i_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1214_, v___x_1215_, v___x_1216_, v_i_1218_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1227_, lean_object* v___x_1228_, lean_object* v___x_1229_, lean_object* v_n_1230_, lean_object* v_i_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1227_, v___x_1228_, v___x_1229_, v_n_1230_, v_i_1231_, v_a_1232_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v_n_1230_);
lean_dec_ref(v_a_1227_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1246_, lean_object* v_lhs_1247_, lean_object* v_rhs_1248_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1250_ = lean_box(0);
lean_inc(v_lvl_1246_);
v___x_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_lvl_1246_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_mkConst(v___x_1249_, v___x_1251_);
v___x_1253_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1246_);
v___x_1254_ = l_Lean_mkApp3(v___x_1252_, v___x_1253_, v_lhs_1247_, v_rhs_1248_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1261_, lean_object* v_lhs_1262_, lean_object* v_rhs_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1265_ = lean_box(0);
lean_inc(v_lvl_1261_);
v___x_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_lvl_1261_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_mkConst(v___x_1264_, v___x_1266_);
v___x_1268_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1261_);
v___x_1269_ = l_Lean_mkApp3(v___x_1267_, v___x_1268_, v_lhs_1262_, v_rhs_1263_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1270_){
_start:
{
lean_object* v_lvl_1271_; lean_object* v_cursorPred_1272_; lean_object* v_letMutsPred_1273_; lean_object* v___x_1274_; 
v_lvl_1271_ = lean_ctor_get(v_p_1270_, 0);
lean_inc(v_lvl_1271_);
v_cursorPred_1272_ = lean_ctor_get(v_p_1270_, 1);
lean_inc_ref(v_cursorPred_1272_);
v_letMutsPred_1273_ = lean_ctor_get(v_p_1270_, 2);
lean_inc_ref(v_letMutsPred_1273_);
lean_dec_ref(v_p_1270_);
v___x_1274_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1271_, v_cursorPred_1272_, v_letMutsPred_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(lean_object* v_x_1275_){
_start:
{
switch(lean_obj_tag(v_x_1275_))
{
case 0:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_unsigned_to_nat(0u);
return v___x_1276_;
}
case 1:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_unsigned_to_nat(1u);
return v___x_1277_;
}
case 2:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_unsigned_to_nat(2u);
return v___x_1278_;
}
default: 
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_unsigned_to_nat(3u);
return v___x_1279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___boxed(lean_object* v_x_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(v_x_1280_);
lean_dec(v_x_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1282_, lean_object* v_k_1283_){
_start:
{
if (lean_obj_tag(v_t_1282_) == 3)
{
lean_object* v_e_1284_; lean_object* v___x_1285_; 
v_e_1284_ = lean_ctor_get(v_t_1282_, 0);
lean_inc_ref(v_e_1284_);
lean_dec_ref(v_t_1282_);
v___x_1285_ = lean_apply_1(v_k_1283_, v_e_1284_);
return v___x_1285_;
}
else
{
lean_dec(v_t_1282_);
return v_k_1283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1286_, lean_object* v_ctorIdx_1287_, lean_object* v_t_1288_, lean_object* v_h_1289_, lean_object* v_k_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1288_, v_k_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1292_, lean_object* v_ctorIdx_1293_, lean_object* v_t_1294_, lean_object* v_h_1295_, lean_object* v_k_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1292_, v_ctorIdx_1293_, v_t_1294_, v_h_1295_, v_k_1296_);
lean_dec(v_ctorIdx_1293_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1298_, lean_object* v_punit_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1298_, v_punit_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1301_, lean_object* v_t_1302_, lean_object* v_h_1303_, lean_object* v_punit_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1302_, v_punit_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1306_, lean_object* v_false_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1306_, v_false_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1309_, lean_object* v_t_1310_, lean_object* v_h_1311_, lean_object* v_false_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1310_, v_false_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1314_, lean_object* v_true_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1314_, v_true_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1317_, lean_object* v_t_1318_, lean_object* v_h_1319_, lean_object* v_true_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1318_, v_true_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1322_, lean_object* v_other_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1322_, v_other_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1325_, lean_object* v_t_1326_, lean_object* v_h_1327_, lean_object* v_other_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1326_, v_other_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_fst_1330_, lean_object* v_p_1331_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_inc(v_fst_1330_);
v___x_1332_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1330_);
v___x_1333_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1330_, v___x_1332_, v_p_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_letMutsTuple_1334_, lean_object* v___x_1335_, uint8_t v___x_1336_, lean_object* v_fvarId_1337_){
_start:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1334_);
v___x_1339_ = l_Lean_instBEqFVarId_beq(v_fvarId_1337_, v___x_1338_);
lean_dec(v___x_1338_);
if (v___x_1339_ == 0)
{
uint8_t v___x_1340_; 
v___x_1340_ = l_Lean_LocalContext_contains(v___x_1335_, v_fvarId_1337_);
return v___x_1340_;
}
else
{
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1341_, lean_object* v___x_1342_, lean_object* v___x_1343_, lean_object* v_fvarId_1344_){
_start:
{
uint8_t v___x_10779__boxed_1345_; uint8_t v_res_1346_; lean_object* v_r_1347_; 
v___x_10779__boxed_1345_ = lean_unbox(v___x_1343_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1341_, v___x_1342_, v___x_10779__boxed_1345_, v_fvarId_1344_);
lean_dec(v_fvarId_1344_);
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_letMutsTuple_1341_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_b_1348_){
_start:
{
lean_object* v_snd_1350_; lean_object* v_fst_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1390_; 
v_snd_1350_ = lean_ctor_get(v_b_1348_, 1);
v_fst_1351_ = lean_ctor_get(v_b_1348_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_b_1348_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1353_ = v_b_1348_;
v_isShared_1354_ = v_isSharedCheck_1390_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_snd_1350_);
lean_inc(v_fst_1351_);
lean_dec(v_b_1348_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1390_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1389_; 
v_fst_1355_ = lean_ctor_get(v_snd_1350_, 0);
v_snd_1356_ = lean_ctor_get(v_snd_1350_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_snd_1350_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1358_ = v_snd_1350_;
v_isShared_1359_ = v_isSharedCheck_1389_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_snd_1356_);
lean_inc(v_fst_1355_);
lean_dec(v_snd_1350_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1389_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1360_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1));
v___x_1361_ = lean_unsigned_to_nat(4u);
v___x_1362_ = l_Lean_Expr_isAppOfArity(v_fst_1355_, v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1364_; 
if (v_isShared_1359_ == 0)
{
v___x_1364_ = v___x_1358_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_fst_1355_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_snd_1356_);
v___x_1364_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1366_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1364_);
v___x_1366_ = v___x_1353_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1351_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1370_ = lean_unsigned_to_nat(3u);
v___x_1371_ = lean_unsigned_to_nat(2u);
v___x_1372_ = l_Lean_Expr_getAppNumArgs(v_fst_1355_);
v___x_1373_ = lean_nat_sub(v___x_1372_, v___x_1371_);
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_sub(v___x_1373_, v___x_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = l_Lean_Expr_getRevArg_x21(v_fst_1355_, v___x_1375_);
v___x_1377_ = lean_array_push(v_snd_1356_, v___x_1376_);
v___x_1378_ = lean_nat_add(v_fst_1351_, v___x_1374_);
lean_dec(v_fst_1351_);
v___x_1379_ = lean_nat_sub(v___x_1372_, v___x_1370_);
lean_dec(v___x_1372_);
v___x_1380_ = lean_nat_sub(v___x_1379_, v___x_1374_);
lean_dec(v___x_1379_);
v___x_1381_ = l_Lean_Expr_getRevArg_x21(v_fst_1355_, v___x_1380_);
lean_dec(v_fst_1355_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1377_);
lean_ctor_set(v___x_1358_, 0, v___x_1381_);
v___x_1383_ = v___x_1358_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1377_);
v___x_1383_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1385_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1383_);
lean_ctor_set(v___x_1353_, 0, v___x_1378_);
v___x_1385_ = v___x_1353_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
v_b_1348_ = v___x_1385_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_b_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_b_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1413_, lean_object* v___x_1414_, lean_object* v_xs_1415_, lean_object* v_letMuts_1416_, lean_object* v_as_1417_, size_t v_sz_1418_, size_t v_i_1419_, lean_object* v_b_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_a_1427_; uint8_t v___x_1431_; 
v___x_1431_ = lean_usize_dec_lt(v_i_1419_, v_sz_1418_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_b_1420_);
return v___x_1432_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_array_uget_borrowed(v_as_1417_, v_i_1419_);
lean_inc(v_a_1433_);
v___x_1434_ = l_Lean_MVarId_getType(v_a_1433_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_snd_1435_; lean_object* v_a_1436_; lean_object* v_fst_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1779_; 
v_snd_1435_ = lean_ctor_get(v_b_1420_, 1);
lean_inc(v_snd_1435_);
v_a_1436_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1436_);
lean_dec_ref(v___x_1434_);
v_fst_1437_ = lean_ctor_get(v_b_1420_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_b_1420_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_b_1420_, 1);
lean_dec(v_unused_1780_);
v___x_1439_ = v_b_1420_;
v_isShared_1440_ = v_isSharedCheck_1779_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_fst_1437_);
lean_dec(v_b_1420_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1779_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_fst_1441_; lean_object* v_snd_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1778_; 
v_fst_1441_ = lean_ctor_get(v_snd_1435_, 0);
v_snd_1442_ = lean_ctor_get(v_snd_1435_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_snd_1435_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1444_ = v_snd_1435_;
v_isShared_1445_ = v_isSharedCheck_1778_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_snd_1442_);
lean_inc(v_fst_1441_);
lean_dec(v_snd_1435_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1778_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; uint8_t v___y_1460_; lean_object* v___y_1560_; lean_object* v_prefixPoint_x3f_1561_; lean_object* v_suffixPoint_x3f_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; uint8_t v___y_1601_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v_prefixPoint_x3f_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v_a_1688_; lean_object* v_a_1693_; lean_object* v___x_1766_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1448_ = lean_box(0);
v___x_1766_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1436_, v___y_1422_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = l_Lean_Expr_consumeMData(v_a_1767_);
lean_dec(v_a_1767_);
v_a_1693_ = v___x_1768_;
goto v___jp_1692_;
}
else
{
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1769_; 
v_a_1769_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1766_);
v_a_1693_ = v_a_1769_;
goto v___jp_1692_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec(v_fst_1437_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1770_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1766_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
v___jp_1449_:
{
if (v___y_1460_ == 0)
{
lean_object* v___x_1462_; 
lean_dec_ref(v___y_1454_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___y_1455_);
v___x_1462_ = v___x_1444_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___y_1455_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_snd_1442_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1462_);
lean_ctor_set(v___x_1439_, 0, v___y_1456_);
v___x_1464_ = v___x_1439_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___y_1456_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
v_a_1427_ = v___x_1464_;
goto v___jp_1426_;
}
}
}
else
{
lean_object* v___x_1468_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1447_);
lean_ctor_set(v___x_1444_, 0, v___y_1454_);
v___x_1468_ = v___x_1444_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___y_1454_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1447_);
v___x_1468_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1468_);
lean_ctor_set(v___x_1439_, 0, v___x_1446_);
v___x_1470_ = v___x_1439_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; 
v___x_1471_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1470_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v_snd_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1547_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
v_snd_1473_ = lean_ctor_get(v_a_1472_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_a_1472_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_a_1472_, 0);
lean_dec(v_unused_1548_);
v___x_1475_ = v_a_1472_;
v_isShared_1476_ = v_isSharedCheck_1547_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_snd_1473_);
lean_dec(v_a_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1547_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_fst_1477_; lean_object* v_snd_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1546_; 
v_fst_1477_ = lean_ctor_get(v_snd_1473_, 0);
v_snd_1478_ = lean_ctor_get(v_snd_1473_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_snd_1473_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1480_ = v_snd_1473_;
v_isShared_1481_ = v_isSharedCheck_1546_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_snd_1478_);
lean_inc(v_fst_1477_);
lean_dec(v_snd_1473_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1546_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_points_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_points_1482_ = lean_ctor_get(v_snd_1442_, 0);
v___x_1483_ = lean_array_get_size(v_points_1482_);
v___x_1484_ = lean_array_get_size(v_snd_1478_);
v___x_1485_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1487_; 
lean_dec(v_snd_1478_);
lean_dec(v_fst_1477_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_snd_1442_);
lean_ctor_set(v___x_1480_, 0, v___y_1455_);
v___x_1487_ = v___x_1480_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___y_1455_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_snd_1442_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1487_);
lean_ctor_set(v___x_1475_, 0, v___y_1456_);
v___x_1489_ = v___x_1475_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___y_1456_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
v_a_1427_ = v___x_1489_;
goto v___jp_1426_;
}
}
}
else
{
lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1543_; 
v_isSharedCheck_1543_ = !lean_is_exclusive(v_snd_1442_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; lean_object* v_unused_1545_; 
v_unused_1544_ = lean_ctor_get(v_snd_1442_, 1);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_snd_1442_, 0);
lean_dec(v_unused_1545_);
v___x_1493_ = v_snd_1442_;
v_isShared_1494_ = v_isSharedCheck_1543_;
goto v_resetjp_1492_;
}
else
{
lean_dec(v_snd_1442_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1543_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2));
v___x_1496_ = l_Lean_Expr_isConstOf(v_fst_1477_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3));
lean_inc_ref(v___y_1450_);
lean_inc_ref(v___y_1452_);
lean_inc_ref(v___y_1453_);
v___x_1498_ = l_Lean_Name_mkStr4(v___y_1453_, v___y_1452_, v___y_1450_, v___x_1497_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = l_Lean_Expr_isAppOfArity(v_fst_1477_, v___x_1498_, v___x_1499_);
lean_dec(v___x_1498_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
lean_inc_ref(v___y_1450_);
lean_inc_ref(v___y_1452_);
lean_inc_ref(v___y_1453_);
v___x_1502_ = l_Lean_Name_mkStr4(v___y_1453_, v___y_1452_, v___y_1450_, v___x_1501_);
v___x_1503_ = l_Lean_Expr_isAppOfArity(v_fst_1477_, v___x_1502_, v___x_1499_);
lean_dec(v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_fst_1477_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1504_);
lean_ctor_set(v___x_1493_, 0, v_snd_1478_);
v___x_1506_ = v___x_1493_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_snd_1478_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1506_);
lean_ctor_set(v___x_1480_, 0, v___y_1455_);
v___x_1508_ = v___x_1480_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___y_1455_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1510_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1508_);
lean_ctor_set(v___x_1475_, 0, v___y_1456_);
v___x_1510_ = v___x_1475_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___y_1456_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
v_a_1427_ = v___x_1510_;
goto v___jp_1426_;
}
}
}
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
lean_dec(v_fst_1477_);
v___x_1514_ = lean_box(2);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1514_);
lean_ctor_set(v___x_1493_, 0, v_snd_1478_);
v___x_1516_ = v___x_1493_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_snd_1478_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1516_);
lean_ctor_set(v___x_1480_, 0, v___y_1455_);
v___x_1518_ = v___x_1480_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___y_1455_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1518_);
lean_ctor_set(v___x_1475_, 0, v___y_1456_);
v___x_1520_ = v___x_1475_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___y_1456_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
v_a_1427_ = v___x_1520_;
goto v___jp_1426_;
}
}
}
}
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
lean_dec(v_fst_1477_);
v___x_1524_ = lean_box(1);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1524_);
lean_ctor_set(v___x_1493_, 0, v_snd_1478_);
v___x_1526_ = v___x_1493_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_snd_1478_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1528_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1526_);
lean_ctor_set(v___x_1480_, 0, v___y_1455_);
v___x_1528_ = v___x_1480_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___y_1455_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1528_);
lean_ctor_set(v___x_1475_, 0, v___y_1456_);
v___x_1530_ = v___x_1475_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___y_1456_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
v_a_1427_ = v___x_1530_;
goto v___jp_1426_;
}
}
}
}
}
else
{
lean_object* v___x_1535_; 
lean_dec(v_fst_1477_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1448_);
lean_ctor_set(v___x_1493_, 0, v_snd_1478_);
v___x_1535_ = v___x_1493_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_snd_1478_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v___x_1448_);
v___x_1535_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1535_);
lean_ctor_set(v___x_1480_, 0, v___y_1455_);
v___x_1537_ = v___x_1480_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___y_1455_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1537_);
lean_ctor_set(v___x_1475_, 0, v___y_1456_);
v___x_1539_ = v___x_1475_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___y_1456_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v_a_1427_ = v___x_1539_;
goto v___jp_1426_;
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
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec(v_snd_1442_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1549_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1471_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1471_);
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
}
}
}
v___jp_1559_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_1568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_1569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_1570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1571_ = lean_unsigned_to_nat(3u);
v___x_1572_ = l_Lean_Expr_isAppOfArity(v___y_1560_, v___x_1570_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec_ref(v___y_1560_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_suffixPoint_x3f_1562_);
lean_ctor_set(v___x_1573_, 1, v_snd_1442_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_prefixPoint_x3f_1561_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v_a_1427_ = v___x_1574_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1575_ = l_Lean_Expr_appFn_x21(v___y_1560_);
v___x_1576_ = l_Lean_Expr_appArg_x21(v___x_1575_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = l_Lean_Expr_appArg_x21(v___y_1560_);
lean_dec_ref(v___y_1560_);
v___x_1578_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___closed__2));
v___x_1579_ = l_Lean_Expr_isAppOfArity(v___x_1576_, v___x_1578_, v___x_1571_);
if (v___x_1579_ == 0)
{
lean_dec_ref(v___x_1576_);
v___y_1450_ = v___x_1569_;
v___y_1451_ = v___y_1566_;
v___y_1452_ = v___x_1568_;
v___y_1453_ = v___x_1567_;
v___y_1454_ = v___x_1577_;
v___y_1455_ = v_suffixPoint_x3f_1562_;
v___y_1456_ = v_prefixPoint_x3f_1561_;
v___y_1457_ = v___y_1565_;
v___y_1458_ = v___y_1564_;
v___y_1459_ = v___y_1563_;
v___y_1460_ = v___x_1579_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1580_ = lean_unsigned_to_nat(2u);
v___x_1581_ = l_Lean_Expr_getAppNumArgs(v___x_1576_);
v___x_1582_ = lean_nat_sub(v___x_1581_, v___x_1580_);
lean_dec(v___x_1581_);
v___x_1583_ = lean_unsigned_to_nat(1u);
v___x_1584_ = lean_nat_sub(v___x_1582_, v___x_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = l_Lean_Expr_getRevArg_x21(v___x_1576_, v___x_1584_);
lean_dec_ref(v___x_1576_);
lean_inc(v_inv_1413_);
v___x_1586_ = l_Lean_mkMVar(v_inv_1413_);
v___x_1587_ = lean_expr_eqv(v___x_1585_, v___x_1586_);
lean_dec_ref(v___x_1586_);
lean_dec_ref(v___x_1585_);
v___y_1450_ = v___x_1569_;
v___y_1451_ = v___y_1566_;
v___y_1452_ = v___x_1568_;
v___y_1453_ = v___x_1567_;
v___y_1454_ = v___x_1577_;
v___y_1455_ = v_suffixPoint_x3f_1562_;
v___y_1456_ = v_prefixPoint_x3f_1561_;
v___y_1457_ = v___y_1565_;
v___y_1458_ = v___y_1564_;
v___y_1459_ = v___y_1563_;
v___y_1460_ = v___x_1587_;
goto v___jp_1449_;
}
}
}
v___jp_1588_:
{
if (v___y_1601_ == 0)
{
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v___y_1589_);
v___y_1560_ = v___y_1590_;
v_prefixPoint_x3f_1561_ = v___y_1599_;
v_suffixPoint_x3f_1562_ = v_fst_1441_;
v___y_1563_ = v___y_1598_;
v___y_1564_ = v___y_1594_;
v___y_1565_ = v___y_1596_;
v___y_1566_ = v___y_1595_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc_ref(v_xs_1415_);
v___x_1603_ = l_Lean_Meta_mkProjection(v_xs_1415_, v___x_1602_, v___y_1598_, v___y_1594_, v___y_1596_, v___y_1595_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = l_Lean_Meta_mkEq(v_a_1604_, v___y_1597_, v___y_1598_, v___y_1594_, v___y_1596_, v___y_1595_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1607_, 0, v___y_1591_);
lean_closure_set(v___x_1607_, 1, v___y_1589_);
lean_inc(v_a_1433_);
v___x_1608_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1433_, v___x_1607_, v___y_1598_, v___y_1594_, v___y_1596_, v___y_1595_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref(v___x_1608_);
v___x_1610_ = l_Lean_Expr_replaceFVar(v_a_1609_, v___y_1600_, v_letMuts_1416_);
lean_dec(v_a_1609_);
if (lean_obj_tag(v_fst_1441_) == 1)
{
lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1606_);
lean_dec_ref(v___y_1592_);
v_val_1611_ = lean_ctor_get(v_fst_1441_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_fst_1441_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1613_ = v_fst_1441_;
v_isShared_1614_ = v_isSharedCheck_1629_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_dec(v_fst_1441_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1629_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_lvl_1615_; lean_object* v_cursorPred_1616_; lean_object* v_letMutsPred_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1628_; 
v_lvl_1615_ = lean_ctor_get(v_val_1611_, 0);
v_cursorPred_1616_ = lean_ctor_get(v_val_1611_, 1);
v_letMutsPred_1617_ = lean_ctor_get(v_val_1611_, 2);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_val_1611_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1619_ = v_val_1611_;
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_letMutsPred_1617_);
lean_inc(v_cursorPred_1616_);
lean_inc(v_lvl_1615_);
lean_dec(v_val_1611_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1593_, v_letMutsPred_1617_, v___x_1610_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 2, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_lvl_1615_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_cursorPred_1616_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1623_);
v___x_1625_ = v___x_1613_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
v___y_1560_ = v___y_1590_;
v_prefixPoint_x3f_1561_ = v___y_1599_;
v_suffixPoint_x3f_1562_ = v___x_1625_;
v___y_1563_ = v___y_1598_;
v___y_1564_ = v___y_1594_;
v___y_1565_ = v___y_1596_;
v___y_1566_ = v___y_1595_;
goto v___jp_1559_;
}
}
}
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec(v_fst_1441_);
v___x_1630_ = lean_apply_1(v___y_1592_, v_a_1606_);
v___x_1631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1631_, 0, v___y_1593_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
lean_ctor_set(v___x_1631_, 2, v___x_1610_);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
v___y_1560_ = v___y_1590_;
v_prefixPoint_x3f_1561_ = v___y_1599_;
v_suffixPoint_x3f_1562_ = v___x_1632_;
v___y_1563_ = v___y_1598_;
v___y_1564_ = v___y_1594_;
v___y_1565_ = v___y_1596_;
v___y_1566_ = v___y_1595_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_a_1606_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v___y_1590_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1633_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1608_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1608_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1641_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1605_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1605_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1649_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1603_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1603_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
v___jp_1657_:
{
lean_object* v___x_1668_; 
lean_inc(v_inv_1413_);
v___x_1668_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v___y_1662_, v_inv_1413_);
lean_dec_ref(v___y_1662_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_invariantUse_1669_; lean_object* v_conditionIdx_1670_; lean_object* v_cursorSuffix_1671_; lean_object* v_letMutsTuple_1672_; uint8_t v___x_1673_; 
v_invariantUse_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc_ref(v_invariantUse_1669_);
lean_dec_ref(v___x_1668_);
v_conditionIdx_1670_ = lean_ctor_get(v_invariantUse_1669_, 0);
lean_inc(v_conditionIdx_1670_);
v_cursorSuffix_1671_ = lean_ctor_get(v_invariantUse_1669_, 2);
lean_inc_ref(v_cursorSuffix_1671_);
v_letMutsTuple_1672_ = lean_ctor_get(v_invariantUse_1669_, 4);
lean_inc_ref(v_letMutsTuple_1672_);
lean_dec_ref(v_invariantUse_1669_);
v___x_1673_ = lean_nat_dec_eq(v_conditionIdx_1670_, v___x_1446_);
lean_dec(v_conditionIdx_1670_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref(v_letMutsTuple_1672_);
lean_dec_ref(v_cursorSuffix_1671_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v_fst_1441_);
lean_ctor_set(v___x_1674_, 1, v_snd_1442_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_prefixPoint_x3f_1663_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v_a_1427_ = v___x_1675_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1676_; lean_object* v___f_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1676_ = lean_box(v___x_1673_);
lean_inc_ref(v___x_1414_);
lean_inc_ref(v_letMutsTuple_1672_);
v___f_1677_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1677_, 0, v_letMutsTuple_1672_);
lean_closure_set(v___f_1677_, 1, v___x_1414_);
lean_closure_set(v___f_1677_, 2, v___x_1676_);
v___x_1678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_1679_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1671_, v___x_1678_);
if (v___x_1679_ == 0)
{
v___y_1589_ = v___f_1677_;
v___y_1590_ = v___y_1658_;
v___y_1591_ = v___y_1659_;
v___y_1592_ = v___y_1660_;
v___y_1593_ = v___y_1661_;
v___y_1594_ = v___y_1665_;
v___y_1595_ = v___y_1667_;
v___y_1596_ = v___y_1666_;
v___y_1597_ = v_cursorSuffix_1671_;
v___y_1598_ = v___y_1664_;
v___y_1599_ = v_prefixPoint_x3f_1663_;
v___y_1600_ = v_letMutsTuple_1672_;
v___y_1601_ = v___x_1679_;
goto v___jp_1588_;
}
else
{
uint8_t v___x_1680_; 
v___x_1680_ = l_Lean_Expr_isFVar(v_letMutsTuple_1672_);
v___y_1589_ = v___f_1677_;
v___y_1590_ = v___y_1658_;
v___y_1591_ = v___y_1659_;
v___y_1592_ = v___y_1660_;
v___y_1593_ = v___y_1661_;
v___y_1594_ = v___y_1665_;
v___y_1595_ = v___y_1667_;
v___y_1596_ = v___y_1666_;
v___y_1597_ = v_cursorSuffix_1671_;
v___y_1598_ = v___y_1664_;
v___y_1599_ = v_prefixPoint_x3f_1663_;
v___y_1600_ = v_letMutsTuple_1672_;
v___y_1601_ = v___x_1680_;
goto v___jp_1588_;
}
}
}
else
{
lean_dec(v___x_1668_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
v___y_1560_ = v___y_1658_;
v_prefixPoint_x3f_1561_ = v_prefixPoint_x3f_1663_;
v_suffixPoint_x3f_1562_ = v_fst_1441_;
v___y_1563_ = v___y_1664_;
v___y_1564_ = v___y_1665_;
v___y_1565_ = v___y_1666_;
v___y_1566_ = v___y_1667_;
goto v___jp_1559_;
}
}
v___jp_1681_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_inc_ref(v___y_1684_);
v___x_1689_ = lean_apply_1(v___y_1684_, v___y_1686_);
lean_inc(v___y_1685_);
v___x_1690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1690_, 0, v___y_1685_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_ctor_set(v___x_1690_, 2, v_a_1688_);
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
v___y_1658_ = v___y_1682_;
v___y_1659_ = v___y_1683_;
v___y_1660_ = v___y_1684_;
v___y_1661_ = v___y_1685_;
v___y_1662_ = v___y_1687_;
v_prefixPoint_x3f_1663_ = v___x_1691_;
v___y_1664_ = v___y_1421_;
v___y_1665_ = v___y_1422_;
v___y_1666_ = v___y_1423_;
v___y_1667_ = v___y_1424_;
goto v___jp_1657_;
}
v___jp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc_ref(v_a_1693_);
v___x_1694_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1694_, 0, v_a_1693_);
lean_inc(v_a_1433_);
v___x_1695_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1433_, v___x_1694_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
if (lean_obj_tag(v_a_1696_) == 1)
{
lean_object* v_val_1697_; lean_object* v_snd_1698_; lean_object* v_fst_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1757_; 
v_val_1697_ = lean_ctor_get(v_a_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref(v_a_1696_);
v_snd_1698_ = lean_ctor_get(v_val_1697_, 1);
v_fst_1699_ = lean_ctor_get(v_val_1697_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_val_1697_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1701_ = v_val_1697_;
v_isShared_1702_ = v_isSharedCheck_1757_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_snd_1698_);
lean_inc(v_fst_1699_);
lean_dec(v_val_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1757_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_fst_1703_; lean_object* v_snd_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1756_; 
v_fst_1703_ = lean_ctor_get(v_snd_1698_, 0);
v_snd_1704_ = lean_ctor_get(v_snd_1698_, 1);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_snd_1698_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1706_ = v_snd_1698_;
v_isShared_1707_ = v_isSharedCheck_1756_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_snd_1704_);
lean_inc(v_fst_1703_);
lean_dec(v_snd_1698_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1756_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___f_1708_; lean_object* v___x_1709_; 
lean_inc(v_fst_1699_);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_1708_, 0, v_fst_1699_);
lean_inc(v_inv_1413_);
v___x_1709_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1704_, v_inv_1413_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_invariantUse_1710_; lean_object* v_conditionIdx_1711_; lean_object* v_cursorPrefix_1712_; lean_object* v_letMutsTuple_1713_; uint8_t v___x_1714_; 
v_invariantUse_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_invariantUse_1710_);
lean_dec_ref(v___x_1709_);
v_conditionIdx_1711_ = lean_ctor_get(v_invariantUse_1710_, 0);
lean_inc(v_conditionIdx_1711_);
v_cursorPrefix_1712_ = lean_ctor_get(v_invariantUse_1710_, 1);
lean_inc_ref(v_cursorPrefix_1712_);
v_letMutsTuple_1713_ = lean_ctor_get(v_invariantUse_1710_, 4);
lean_inc_ref(v_letMutsTuple_1713_);
lean_dec_ref(v_invariantUse_1710_);
v___x_1714_ = lean_nat_dec_eq(v_conditionIdx_1711_, v___x_1446_);
lean_dec(v_conditionIdx_1711_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref(v_letMutsTuple_1713_);
lean_dec_ref(v_cursorPrefix_1712_);
lean_dec_ref(v___f_1708_);
lean_dec(v_snd_1704_);
lean_dec(v_fst_1703_);
lean_dec(v_fst_1699_);
lean_dec_ref(v_a_1693_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v_snd_1442_);
lean_ctor_set(v___x_1706_, 0, v_fst_1441_);
v___x_1716_ = v___x_1706_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_fst_1441_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_snd_1442_);
v___x_1716_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1716_);
lean_ctor_set(v___x_1701_, 0, v_fst_1437_);
v___x_1718_ = v___x_1701_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_fst_1437_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v_a_1427_ = v___x_1718_;
goto v___jp_1426_;
}
}
}
else
{
lean_object* v___x_1721_; uint8_t v___x_1722_; 
lean_del_object(v___x_1706_);
lean_del_object(v___x_1701_);
v___x_1721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_1722_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1712_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_dec_ref(v_letMutsTuple_1713_);
lean_dec_ref(v_cursorPrefix_1712_);
v___y_1658_ = v_a_1693_;
v___y_1659_ = v_snd_1704_;
v___y_1660_ = v___f_1708_;
v___y_1661_ = v_fst_1699_;
v___y_1662_ = v_fst_1703_;
v_prefixPoint_x3f_1663_ = v_fst_1437_;
v___y_1664_ = v___y_1421_;
v___y_1665_ = v___y_1422_;
v___y_1666_ = v___y_1423_;
v___y_1667_ = v___y_1424_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_fst_1437_);
v___x_1723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1415_);
v___x_1724_ = l_Lean_Meta_mkProjection(v_xs_1415_, v___x_1723_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = l_Lean_Meta_mkEq(v_a_1725_, v_cursorPrefix_1712_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1726_);
lean_inc_ref(v_letMuts_1416_);
v___x_1728_ = l_Lean_Meta_mkEq(v_letMuts_1416_, v_letMutsTuple_1713_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
lean_inc(v_fst_1699_);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_fst_1699_, v_a_1729_);
v___y_1682_ = v_a_1693_;
v___y_1683_ = v_snd_1704_;
v___y_1684_ = v___f_1708_;
v___y_1685_ = v_fst_1699_;
v___y_1686_ = v_a_1727_;
v___y_1687_ = v_fst_1703_;
v_a_1688_ = v___x_1730_;
goto v___jp_1681_;
}
else
{
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1731_; 
v_a_1731_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1728_);
v___y_1682_ = v_a_1693_;
v___y_1683_ = v_snd_1704_;
v___y_1684_ = v___f_1708_;
v___y_1685_ = v_fst_1699_;
v___y_1686_ = v_a_1727_;
v___y_1687_ = v_fst_1703_;
v_a_1688_ = v_a_1731_;
goto v___jp_1681_;
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_a_1727_);
lean_dec_ref(v___f_1708_);
lean_dec(v_snd_1704_);
lean_dec(v_fst_1703_);
lean_dec(v_fst_1699_);
lean_dec_ref(v_a_1693_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1732_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1728_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_letMutsTuple_1713_);
lean_dec_ref(v___f_1708_);
lean_dec(v_snd_1704_);
lean_dec(v_fst_1703_);
lean_dec(v_fst_1699_);
lean_dec_ref(v_a_1693_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1740_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1726_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1726_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec_ref(v_letMutsTuple_1713_);
lean_dec_ref(v_cursorPrefix_1712_);
lean_dec_ref(v___f_1708_);
lean_dec(v_snd_1704_);
lean_dec(v_fst_1703_);
lean_dec(v_fst_1699_);
lean_dec_ref(v_a_1693_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1748_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1724_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1724_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1709_);
lean_del_object(v___x_1706_);
lean_del_object(v___x_1701_);
v___y_1658_ = v_a_1693_;
v___y_1659_ = v_snd_1704_;
v___y_1660_ = v___f_1708_;
v___y_1661_ = v_fst_1699_;
v___y_1662_ = v_fst_1703_;
v_prefixPoint_x3f_1663_ = v_fst_1437_;
v___y_1664_ = v___y_1421_;
v___y_1665_ = v___y_1422_;
v___y_1666_ = v___y_1423_;
v___y_1667_ = v___y_1424_;
goto v___jp_1657_;
}
}
}
}
else
{
lean_dec(v_a_1696_);
v___y_1560_ = v_a_1693_;
v_prefixPoint_x3f_1561_ = v_fst_1437_;
v_suffixPoint_x3f_1562_ = v_fst_1441_;
v___y_1563_ = v___y_1421_;
v___y_1564_ = v___y_1422_;
v___y_1565_ = v___y_1423_;
v___y_1566_ = v___y_1424_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v_a_1693_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec(v_fst_1437_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1758_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1695_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1695_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v_b_1420_);
lean_dec_ref(v_letMuts_1416_);
lean_dec_ref(v_xs_1415_);
lean_dec_ref(v___x_1414_);
lean_dec(v_inv_1413_);
v_a_1781_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1434_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1434_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
v___jp_1426_:
{
size_t v___x_1428_; size_t v___x_1429_; 
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_add(v_i_1419_, v___x_1428_);
v_i_1419_ = v___x_1429_;
v_b_1420_ = v_a_1427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1789_, lean_object* v___x_1790_, lean_object* v_xs_1791_, lean_object* v_letMuts_1792_, lean_object* v_as_1793_, lean_object* v_sz_1794_, lean_object* v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
size_t v_sz_boxed_1802_; size_t v_i_boxed_1803_; lean_object* v_res_1804_; 
v_sz_boxed_1802_ = lean_unbox_usize(v_sz_1794_);
lean_dec(v_sz_1794_);
v_i_boxed_1803_ = lean_unbox_usize(v_i_1795_);
lean_dec(v_i_1795_);
v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1789_, v___x_1790_, v_xs_1791_, v_letMuts_1792_, v_as_1793_, v_sz_boxed_1802_, v_i_boxed_1803_, v_b_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v_as_1793_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1814_, lean_object* v_inv_1815_, lean_object* v_xs_1816_, lean_object* v_letMuts_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_lctx_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; size_t v_sz_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v_lctx_1823_ = lean_ctor_get(v_a_1818_, 2);
v___x_1824_ = lean_box(0);
v___x_1825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1826_ = lean_array_size(v_vcs_1814_);
v___x_1827_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1823_);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1815_, v_lctx_1823_, v_xs_1816_, v_letMuts_1817_, v_vcs_1814_, v_sz_1826_, v___x_1827_, v___x_1825_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1872_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1872_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1872_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_snd_1837_; lean_object* v_fst_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1871_; 
v_snd_1837_ = lean_ctor_get(v_a_1829_, 1);
v_fst_1838_ = lean_ctor_get(v_a_1829_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_a_1829_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1840_ = v_a_1829_;
v_isShared_1841_ = v_isSharedCheck_1871_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_snd_1837_);
lean_inc(v_fst_1838_);
lean_dec(v_a_1829_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1871_;
goto v_resetjp_1839_;
}
v___jp_1833_:
{
lean_object* v___x_1835_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1824_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1824_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
v_resetjp_1839_:
{
if (lean_obj_tag(v_fst_1838_) == 0)
{
lean_del_object(v___x_1840_);
lean_dec(v_snd_1837_);
goto v___jp_1833_;
}
else
{
lean_object* v_fst_1842_; 
v_fst_1842_ = lean_ctor_get(v_snd_1837_, 0);
lean_inc(v_fst_1842_);
if (lean_obj_tag(v_fst_1842_) == 0)
{
lean_dec_ref(v_fst_1838_);
lean_del_object(v___x_1840_);
lean_dec(v_snd_1837_);
goto v___jp_1833_;
}
else
{
lean_object* v_snd_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1869_; 
lean_del_object(v___x_1831_);
v_snd_1843_ = lean_ctor_get(v_snd_1837_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_snd_1837_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v_snd_1837_, 0);
lean_dec(v_unused_1870_);
v___x_1845_ = v_snd_1837_;
v_isShared_1846_ = v_isSharedCheck_1869_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_snd_1843_);
lean_dec(v_snd_1837_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1869_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_val_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1868_; 
v_val_1847_ = lean_ctor_get(v_fst_1838_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_fst_1838_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1849_ = v_fst_1838_;
v_isShared_1850_ = v_isSharedCheck_1868_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_val_1847_);
lean_dec(v_fst_1838_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1868_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_val_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1867_; 
v_val_1851_ = lean_ctor_get(v_fst_1842_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_fst_1842_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1853_ = v_fst_1842_;
v_isShared_1854_ = v_isSharedCheck_1867_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_val_1851_);
lean_dec(v_fst_1842_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1867_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v_val_1851_);
v___x_1856_ = v___x_1845_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_val_1851_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_snd_1843_);
v___x_1856_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1858_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 1, v___x_1856_);
lean_ctor_set(v___x_1840_, 0, v_val_1847_);
v___x_1858_ = v___x_1840_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_val_1847_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1860_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1858_);
v___x_1860_ = v___x_1853_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1862_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1860_);
v___x_1862_ = v___x_1849_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
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
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1828_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1828_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1881_, lean_object* v_inv_1882_, lean_object* v_xs_1883_, lean_object* v_letMuts_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1881_, v_inv_1882_, v_xs_1883_, v_letMuts_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec_ref(v_vcs_1881_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_b_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_b_1891_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_b_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_b_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_MVarId_getDecl(v_m_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v_userName_1913_; lean_object* v_lctx_1914_; lean_object* v_type_1915_; lean_object* v_localInstances_1916_; uint8_t v_kind_1917_; lean_object* v_numScopeArgs_1918_; lean_object* v___x_1919_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v_userName_1913_ = lean_ctor_get(v_a_1912_, 0);
lean_inc(v_userName_1913_);
v_lctx_1914_ = lean_ctor_get(v_a_1912_, 1);
lean_inc_ref(v_lctx_1914_);
v_type_1915_ = lean_ctor_get(v_a_1912_, 2);
lean_inc_ref(v_type_1915_);
v_localInstances_1916_ = lean_ctor_get(v_a_1912_, 4);
lean_inc_ref(v_localInstances_1916_);
v_kind_1917_ = lean_ctor_get_uint8(v_a_1912_, sizeof(void*)*7);
v_numScopeArgs_1918_ = lean_ctor_get(v_a_1912_, 5);
lean_inc(v_numScopeArgs_1918_);
lean_dec(v_a_1912_);
v___x_1919_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1914_, v_localInstances_1916_, v_type_1915_, v_kind_1917_, v_userName_1913_, v_numScopeArgs_1918_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = l_Lean_Expr_mvarId_x21(v_a_1920_);
lean_dec(v_a_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_a_1929_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1919_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1919_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1911_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1911_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_1952_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = l_String_instInhabitedSlice;
v___x_1954_ = lean_panic_fn_borrowed(v___x_1953_, v_msg_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_1955_, lean_object* v_a_1956_, uint8_t v_b_1957_){
_start:
{
lean_object* v_str_1958_; lean_object* v_startInclusive_1959_; lean_object* v_endExclusive_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_str_1958_ = lean_ctor_get(v_s_1955_, 0);
v_startInclusive_1959_ = lean_ctor_get(v_s_1955_, 1);
v_endExclusive_1960_ = lean_ctor_get(v_s_1955_, 2);
v___x_1961_ = lean_nat_sub(v_endExclusive_1960_, v_startInclusive_1959_);
v___x_1962_ = lean_nat_dec_eq(v_a_1956_, v___x_1961_);
lean_dec(v___x_1961_);
if (v___x_1962_ == 0)
{
uint32_t v___x_1963_; lean_object* v___x_1964_; uint32_t v___x_1965_; uint8_t v___x_1966_; 
v___x_1963_ = 64;
v___x_1964_ = lean_nat_add(v_startInclusive_1959_, v_a_1956_);
lean_dec(v_a_1956_);
v___x_1965_ = lean_string_utf8_get_fast(v_str_1958_, v___x_1964_);
v___x_1966_ = lean_uint32_dec_eq(v___x_1965_, v___x_1963_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_string_utf8_next_fast(v_str_1958_, v___x_1964_);
lean_dec(v___x_1964_);
v___x_1968_ = lean_nat_sub(v___x_1967_, v_startInclusive_1959_);
v_a_1956_ = v___x_1968_;
v_b_1957_ = v___x_1966_;
goto _start;
}
else
{
lean_dec(v___x_1964_);
return v___x_1966_;
}
}
else
{
lean_dec(v_a_1956_);
return v_b_1957_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object* v_s_1970_, lean_object* v_a_1971_, lean_object* v_b_1972_){
_start:
{
uint8_t v_b_boxed_1973_; uint8_t v_res_1974_; lean_object* v_r_1975_; 
v_b_boxed_1973_ = lean_unbox(v_b_1972_);
v_res_1974_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1970_, v_a_1971_, v_b_boxed_1973_);
lean_dec_ref(v_s_1970_);
v_r_1975_ = lean_box(v_res_1974_);
return v_r_1975_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_1976_){
_start:
{
lean_object* v_searcher_1977_; uint8_t v___x_1978_; uint8_t v___x_1979_; 
v_searcher_1977_ = lean_unsigned_to_nat(0u);
v___x_1978_ = 0;
v___x_1979_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1976_, v_searcher_1977_, v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_1980_){
_start:
{
uint8_t v_res_1981_; lean_object* v_r_1982_; 
v_res_1981_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_1980_);
lean_dec_ref(v_s_1980_);
v_r_1982_ = lean_box(v_res_1981_);
return v_r_1982_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_1987_ = lean_unsigned_to_nat(14u);
v___x_1988_ = lean_unsigned_to_nat(22u);
v___x_1989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_1990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_1991_ = l_mkPanicMessageWithDecl(v___x_1990_, v___x_1989_, v___x_1988_, v___x_1987_, v___x_1986_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_1992_){
_start:
{
switch(lean_obj_tag(v_x_1992_))
{
case 1:
{
lean_object* v_info_1993_; lean_object* v_kind_1994_; lean_object* v_args_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_info_1993_ = lean_ctor_get(v_x_1992_, 0);
v_kind_1994_ = lean_ctor_get(v_x_1992_, 1);
v_args_1995_ = lean_ctor_get(v_x_1992_, 2);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1997_ = v_x_1992_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_args_1995_);
lean_inc(v_kind_1994_);
lean_inc(v_info_1993_);
lean_dec(v_x_1992_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
size_t v_sz_1999_; size_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v_sz_1999_ = lean_array_size(v_args_1995_);
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_1999_, v___x_2000_, v_args_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 2, v___x_2001_);
v___x_2003_ = v___x_1997_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_info_1993_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_kind_1994_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
case 3:
{
lean_object* v_info_2006_; lean_object* v_rawVal_2007_; lean_object* v_val_2008_; lean_object* v_preresolved_2009_; uint8_t v___y_2011_; lean_object* v_str_2028_; lean_object* v_startPos_2029_; lean_object* v_stopPos_2030_; uint8_t v___x_2031_; 
v_info_2006_ = lean_ctor_get(v_x_1992_, 0);
v_rawVal_2007_ = lean_ctor_get(v_x_1992_, 1);
v_val_2008_ = lean_ctor_get(v_x_1992_, 2);
v_preresolved_2009_ = lean_ctor_get(v_x_1992_, 3);
v_str_2028_ = lean_ctor_get(v_rawVal_2007_, 0);
v_startPos_2029_ = lean_ctor_get(v_rawVal_2007_, 1);
v_stopPos_2030_ = lean_ctor_get(v_rawVal_2007_, 2);
v___x_2031_ = lean_string_is_valid_pos(v_str_2028_, v_startPos_2029_);
if (v___x_2031_ == 0)
{
goto v___jp_2024_;
}
else
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_string_is_valid_pos(v_str_2028_, v_stopPos_2030_);
if (v___x_2032_ == 0)
{
goto v___jp_2024_;
}
else
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_nat_dec_le(v_startPos_2029_, v_stopPos_2030_);
if (v___x_2033_ == 0)
{
goto v___jp_2024_;
}
else
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
lean_inc(v_stopPos_2030_);
lean_inc(v_startPos_2029_);
lean_inc_ref(v_str_2028_);
v___x_2034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2034_, 0, v_str_2028_);
lean_ctor_set(v___x_2034_, 1, v_startPos_2029_);
lean_ctor_set(v___x_2034_, 2, v_stopPos_2030_);
v___x_2035_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2034_);
lean_dec_ref(v___x_2034_);
v___y_2011_ = v___x_2035_;
goto v___jp_2010_;
}
}
}
v___jp_2010_:
{
if (v___y_2011_ == 0)
{
lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
lean_inc(v_preresolved_2009_);
lean_inc(v_val_2008_);
lean_inc_ref(v_rawVal_2007_);
lean_inc(v_info_2006_);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; lean_object* v_unused_2023_; 
v_unused_2020_ = lean_ctor_get(v_x_1992_, 3);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_x_1992_, 2);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_x_1992_, 1);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_x_1992_, 0);
lean_dec(v_unused_2023_);
v___x_2013_ = v_x_1992_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_dec(v_x_1992_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_erase_macro_scopes(v_val_2008_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 2, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_info_2006_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_rawVal_2007_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_preresolved_2009_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
else
{
return v_x_1992_;
}
}
v___jp_2024_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_2026_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_2025_);
v___x_2027_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2026_);
lean_dec_ref(v___x_2026_);
v___y_2011_ = v___x_2027_;
goto v___jp_2010_;
}
}
default: 
{
return v_x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_2036_, size_t v_i_2037_, lean_object* v_bs_2038_){
_start:
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_usize_dec_lt(v_i_2037_, v_sz_2036_);
if (v___x_2039_ == 0)
{
return v_bs_2038_;
}
else
{
lean_object* v_v_2040_; lean_object* v___x_2041_; lean_object* v_bs_x27_2042_; lean_object* v___x_2043_; size_t v___x_2044_; size_t v___x_2045_; lean_object* v___x_2046_; 
v_v_2040_ = lean_array_uget(v_bs_2038_, v_i_2037_);
v___x_2041_ = lean_unsigned_to_nat(0u);
v_bs_x27_2042_ = lean_array_uset(v_bs_2038_, v_i_2037_, v___x_2041_);
v___x_2043_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_2040_);
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = lean_usize_add(v_i_2037_, v___x_2044_);
v___x_2046_ = lean_array_uset(v_bs_x27_2042_, v_i_2037_, v___x_2043_);
v_i_2037_ = v___x_2045_;
v_bs_2038_ = v___x_2046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2048_, lean_object* v_i_2049_, lean_object* v_bs_2050_){
_start:
{
size_t v_sz_boxed_2051_; size_t v_i_boxed_2052_; lean_object* v_res_2053_; 
v_sz_boxed_2051_ = lean_unbox_usize(v_sz_2048_);
lean_dec(v_sz_2048_);
v_i_boxed_2052_ = lean_unbox_usize(v_i_2049_);
lean_dec(v_i_2049_);
v_res_2053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2051_, v_i_boxed_2052_, v_bs_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2054_, lean_object* v_inst_2055_, lean_object* v_R_2056_, lean_object* v_a_2057_, uint8_t v_b_2058_, lean_object* v_c_2059_){
_start:
{
uint8_t v___x_2060_; 
v___x_2060_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2054_, v_a_2057_, v_b_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2061_, lean_object* v_inst_2062_, lean_object* v_R_2063_, lean_object* v_a_2064_, lean_object* v_b_2065_, lean_object* v_c_2066_){
_start:
{
uint8_t v_b_boxed_2067_; uint8_t v_res_2068_; lean_object* v_r_2069_; 
v_b_boxed_2067_ = lean_unbox(v_b_2065_);
v_res_2068_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2061_, v_inst_2062_, v_R_2063_, v_a_2064_, v_b_boxed_2067_, v_c_2066_);
lean_dec_ref(v_s_2061_);
v_r_2069_ = lean_box(v_res_2068_);
return v_r_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2070_, lean_object* v_h__1_2071_, lean_object* v_h__2_2072_, lean_object* v_h__3_2073_, lean_object* v_h__4_2074_){
_start:
{
switch(lean_obj_tag(v_x_2070_))
{
case 0:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v_h__3_2073_);
lean_dec(v_h__2_2072_);
lean_dec(v_h__1_2071_);
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_apply_1(v_h__4_2074_, v___x_2075_);
return v___x_2076_;
}
case 1:
{
lean_object* v_info_2077_; lean_object* v_kind_2078_; lean_object* v_args_2079_; lean_object* v___x_2080_; 
lean_dec(v_h__4_2074_);
lean_dec(v_h__3_2073_);
lean_dec(v_h__1_2071_);
v_info_2077_ = lean_ctor_get(v_x_2070_, 0);
lean_inc(v_info_2077_);
v_kind_2078_ = lean_ctor_get(v_x_2070_, 1);
lean_inc(v_kind_2078_);
v_args_2079_ = lean_ctor_get(v_x_2070_, 2);
lean_inc_ref(v_args_2079_);
lean_dec_ref(v_x_2070_);
v___x_2080_ = lean_apply_3(v_h__2_2072_, v_info_2077_, v_kind_2078_, v_args_2079_);
return v___x_2080_;
}
case 2:
{
lean_object* v_info_2081_; lean_object* v_val_2082_; lean_object* v___x_2083_; 
lean_dec(v_h__4_2074_);
lean_dec(v_h__2_2072_);
lean_dec(v_h__1_2071_);
v_info_2081_ = lean_ctor_get(v_x_2070_, 0);
lean_inc(v_info_2081_);
v_val_2082_ = lean_ctor_get(v_x_2070_, 1);
lean_inc_ref(v_val_2082_);
lean_dec_ref(v_x_2070_);
v___x_2083_ = lean_apply_2(v_h__3_2073_, v_info_2081_, v_val_2082_);
return v___x_2083_;
}
default: 
{
lean_object* v_info_2084_; lean_object* v_rawVal_2085_; lean_object* v_val_2086_; lean_object* v_preresolved_2087_; lean_object* v___x_2088_; 
lean_dec(v_h__4_2074_);
lean_dec(v_h__3_2073_);
lean_dec(v_h__2_2072_);
v_info_2084_ = lean_ctor_get(v_x_2070_, 0);
lean_inc(v_info_2084_);
v_rawVal_2085_ = lean_ctor_get(v_x_2070_, 1);
lean_inc_ref(v_rawVal_2085_);
v_val_2086_ = lean_ctor_get(v_x_2070_, 2);
lean_inc(v_val_2086_);
v_preresolved_2087_ = lean_ctor_get(v_x_2070_, 3);
lean_inc(v_preresolved_2087_);
lean_dec_ref(v_x_2070_);
v___x_2088_ = lean_apply_4(v_h__1_2071_, v_info_2084_, v_rawVal_2085_, v_val_2086_, v_preresolved_2087_);
return v___x_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2089_, lean_object* v_x_2090_, lean_object* v_h__1_2091_, lean_object* v_h__2_2092_, lean_object* v_h__3_2093_, lean_object* v_h__4_2094_){
_start:
{
switch(lean_obj_tag(v_x_2090_))
{
case 0:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec(v_h__3_2093_);
lean_dec(v_h__2_2092_);
lean_dec(v_h__1_2091_);
v___x_2095_ = lean_box(0);
v___x_2096_ = lean_apply_1(v_h__4_2094_, v___x_2095_);
return v___x_2096_;
}
case 1:
{
lean_object* v_info_2097_; lean_object* v_kind_2098_; lean_object* v_args_2099_; lean_object* v___x_2100_; 
lean_dec(v_h__4_2094_);
lean_dec(v_h__3_2093_);
lean_dec(v_h__1_2091_);
v_info_2097_ = lean_ctor_get(v_x_2090_, 0);
lean_inc(v_info_2097_);
v_kind_2098_ = lean_ctor_get(v_x_2090_, 1);
lean_inc(v_kind_2098_);
v_args_2099_ = lean_ctor_get(v_x_2090_, 2);
lean_inc_ref(v_args_2099_);
lean_dec_ref(v_x_2090_);
v___x_2100_ = lean_apply_3(v_h__2_2092_, v_info_2097_, v_kind_2098_, v_args_2099_);
return v___x_2100_;
}
case 2:
{
lean_object* v_info_2101_; lean_object* v_val_2102_; lean_object* v___x_2103_; 
lean_dec(v_h__4_2094_);
lean_dec(v_h__2_2092_);
lean_dec(v_h__1_2091_);
v_info_2101_ = lean_ctor_get(v_x_2090_, 0);
lean_inc(v_info_2101_);
v_val_2102_ = lean_ctor_get(v_x_2090_, 1);
lean_inc_ref(v_val_2102_);
lean_dec_ref(v_x_2090_);
v___x_2103_ = lean_apply_2(v_h__3_2093_, v_info_2101_, v_val_2102_);
return v___x_2103_;
}
default: 
{
lean_object* v_info_2104_; lean_object* v_rawVal_2105_; lean_object* v_val_2106_; lean_object* v_preresolved_2107_; lean_object* v___x_2108_; 
lean_dec(v_h__4_2094_);
lean_dec(v_h__3_2093_);
lean_dec(v_h__2_2092_);
v_info_2104_ = lean_ctor_get(v_x_2090_, 0);
lean_inc(v_info_2104_);
v_rawVal_2105_ = lean_ctor_get(v_x_2090_, 1);
lean_inc_ref(v_rawVal_2105_);
v_val_2106_ = lean_ctor_get(v_x_2090_, 2);
lean_inc(v_val_2106_);
v_preresolved_2107_ = lean_ctor_get(v_x_2090_, 3);
lean_inc(v_preresolved_2107_);
lean_dec_ref(v_x_2090_);
v___x_2108_ = lean_apply_4(v_h__1_2091_, v_info_2104_, v_rawVal_2105_, v_val_2106_, v_preresolved_2107_);
return v___x_2108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2109_, lean_object* v_h__1_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_apply_2(v_h__1_2110_, v_x_2109_, lean_box(0));
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2112_, lean_object* v_P_2113_, lean_object* v_motive_2114_, lean_object* v_x_2115_, lean_object* v_h__1_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_apply_2(v_h__1_2116_, v_x_2115_, lean_box(0));
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2120_, lean_object* v_syn_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2123_, lean_object* v_syn_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2123_, v_syn_2124_);
lean_dec(v_name_2123_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2132_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2160_ = lean_unsigned_to_nat(2u);
v___x_2161_ = l_Lean_Expr_isAppOfArity(v_e_2132_, v___x_2159_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2163_ = lean_unsigned_to_nat(3u);
v___x_2164_ = l_Lean_Expr_isAppOfArity(v_e_2132_, v___x_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2166_ = l_Lean_Expr_isAppOfArity(v_e_2132_, v___x_2165_, v___x_2163_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2168_ = l_Lean_Expr_isAppOfArity(v_e_2132_, v___x_2167_, v___x_2163_);
if (v___x_2168_ == 0)
{
goto v___jp_2133_;
}
else
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Expr_appArg_x21(v_e_2132_);
if (lean_obj_tag(v___x_2169_) == 6)
{
lean_object* v_binderName_2170_; lean_object* v_binderType_2171_; lean_object* v_body_2172_; uint8_t v_binderInfo_2173_; lean_object* v___x_2174_; 
lean_dec_ref(v_e_2132_);
v_binderName_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_binderName_2170_);
v_binderType_2171_ = lean_ctor_get(v___x_2169_, 1);
lean_inc_ref(v_binderType_2171_);
v_body_2172_ = lean_ctor_get(v___x_2169_, 2);
lean_inc_ref(v_body_2172_);
v_binderInfo_2173_ = lean_ctor_get_uint8(v___x_2169_, sizeof(void*)*3 + 8);
lean_dec_ref(v___x_2169_);
v___x_2174_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2172_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_dec_ref(v_binderType_2171_);
lean_dec(v_binderName_2170_);
return v___x_2174_;
}
else
{
lean_object* v_val_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2192_; 
v_val_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2192_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_val_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2192_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v_fst_2179_; lean_object* v_snd_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2191_; 
v_fst_2179_ = lean_ctor_get(v_val_2175_, 0);
v_snd_2180_ = lean_ctor_get(v_val_2175_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_val_2175_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2182_ = v_val_2175_;
v_isShared_2183_ = v_isSharedCheck_2191_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_snd_2180_);
lean_inc(v_fst_2179_);
lean_dec(v_val_2175_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2191_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2184_ = l_Lean_mkForall(v_binderName_2170_, v_binderInfo_2173_, v_binderType_2171_, v_snd_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 1, v___x_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_fst_2179_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2188_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2186_);
v___x_2188_ = v___x_2177_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2169_);
goto v___jp_2133_;
}
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = l_Lean_Expr_appFn_x21(v_e_2132_);
v___x_2194_ = l_Lean_Expr_appArg_x21(v___x_2193_);
lean_dec_ref(v___x_2193_);
v___x_2195_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2194_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_dec_ref(v_e_2132_);
return v___x_2195_;
}
else
{
lean_object* v_val_2196_; lean_object* v_snd_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_val_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_val_2196_);
lean_dec_ref(v___x_2195_);
v_snd_2197_ = lean_ctor_get(v_val_2196_, 1);
lean_inc(v_snd_2197_);
lean_dec(v_val_2196_);
v___x_2198_ = l_Lean_Expr_appArg_x21(v_e_2132_);
lean_dec_ref(v_e_2132_);
v___x_2199_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2198_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_dec(v_snd_2197_);
return v___x_2199_;
}
else
{
lean_object* v_val_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2217_; 
v_val_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2217_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_val_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2217_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_fst_2204_; lean_object* v_snd_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2216_; 
v_fst_2204_ = lean_ctor_get(v_val_2200_, 0);
v_snd_2205_ = lean_ctor_get(v_val_2200_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_val_2200_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2207_ = v_val_2200_;
v_isShared_2208_ = v_isSharedCheck_2216_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_snd_2205_);
lean_inc(v_fst_2204_);
lean_dec(v_val_2200_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2216_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = l_Lean_mkOr(v_snd_2197_, v_snd_2205_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_fst_2204_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2211_);
v___x_2213_ = v___x_2202_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
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
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = l_Lean_Expr_appFn_x21(v_e_2132_);
v___x_2219_ = l_Lean_Expr_appArg_x21(v___x_2218_);
lean_dec_ref(v___x_2218_);
v___x_2220_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2219_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_dec_ref(v_e_2132_);
return v___x_2220_;
}
else
{
lean_object* v_val_2221_; lean_object* v_snd_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_val_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_val_2221_);
lean_dec_ref(v___x_2220_);
v_snd_2222_ = lean_ctor_get(v_val_2221_, 1);
lean_inc(v_snd_2222_);
lean_dec(v_val_2221_);
v___x_2223_ = l_Lean_Expr_appArg_x21(v_e_2132_);
lean_dec_ref(v_e_2132_);
v___x_2224_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2223_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_dec(v_snd_2222_);
return v___x_2224_;
}
else
{
lean_object* v_val_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2242_; 
v_val_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2242_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_val_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2242_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_fst_2229_; lean_object* v_snd_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2241_; 
v_fst_2229_ = lean_ctor_get(v_val_2225_, 0);
v_snd_2230_ = lean_ctor_get(v_val_2225_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_val_2225_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2232_ = v_val_2225_;
v_isShared_2233_ = v_isSharedCheck_2241_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_snd_2230_);
lean_inc(v_fst_2229_);
lean_dec(v_val_2225_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2241_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = l_Lean_mkAnd(v_snd_2222_, v_snd_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_fst_2229_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2238_; 
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2236_);
v___x_2238_ = v___x_2227_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
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
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = l_Lean_Expr_getAppFn(v_e_2132_);
v___x_2245_ = l_Lean_Expr_constLevels_x21(v___x_2244_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = l_List_get_x21Internal___redArg(v___x_2243_, v___x_2245_, v___x_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = l_Lean_Expr_getAppNumArgs(v_e_2132_);
v___x_2250_ = lean_nat_sub(v___x_2249_, v___x_2248_);
lean_dec(v___x_2249_);
v___x_2251_ = lean_nat_sub(v___x_2250_, v___x_2248_);
lean_dec(v___x_2250_);
v___x_2252_ = l_Lean_Expr_getRevArg_x21(v_e_2132_, v___x_2251_);
lean_dec_ref(v_e_2132_);
v___x_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2247_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
return v___x_2254_;
}
v___jp_2133_:
{
if (lean_obj_tag(v_e_2132_) == 8)
{
lean_object* v_declName_2134_; lean_object* v_type_2135_; lean_object* v_value_2136_; lean_object* v_body_2137_; uint8_t v_nondep_2138_; lean_object* v___x_2139_; 
v_declName_2134_ = lean_ctor_get(v_e_2132_, 0);
lean_inc(v_declName_2134_);
v_type_2135_ = lean_ctor_get(v_e_2132_, 1);
lean_inc_ref(v_type_2135_);
v_value_2136_ = lean_ctor_get(v_e_2132_, 2);
lean_inc_ref(v_value_2136_);
v_body_2137_ = lean_ctor_get(v_e_2132_, 3);
lean_inc_ref(v_body_2137_);
v_nondep_2138_ = lean_ctor_get_uint8(v_e_2132_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2132_);
v___x_2139_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2137_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_dec_ref(v_value_2136_);
lean_dec_ref(v_type_2135_);
lean_dec(v_declName_2134_);
return v___x_2139_;
}
else
{
lean_object* v_val_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2157_; 
v_val_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2157_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_val_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2157_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_fst_2144_; lean_object* v_snd_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2156_; 
v_fst_2144_ = lean_ctor_get(v_val_2140_, 0);
v_snd_2145_ = lean_ctor_get(v_val_2140_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_val_2140_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2147_ = v_val_2140_;
v_isShared_2148_ = v_isSharedCheck_2156_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_snd_2145_);
lean_inc(v_fst_2144_);
lean_dec(v_val_2140_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2156_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = l_Lean_Expr_letE___override(v_declName_2134_, v_type_2135_, v_value_2136_, v_snd_2145_, v_nondep_2138_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 1, v___x_2149_);
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_fst_2144_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2153_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2151_);
v___x_2153_ = v___x_2142_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
}
else
{
lean_object* v___x_2158_; 
lean_dec_ref(v_e_2132_);
v___x_2158_ = lean_box(0);
return v___x_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2255_){
_start:
{
lean_object* v___x_2256_; 
lean_inc_ref(v_e_2255_);
v___x_2256_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2255_);
if (lean_obj_tag(v___x_2256_) == 0)
{
return v_e_2255_;
}
else
{
lean_object* v_val_2257_; lean_object* v_fst_2258_; lean_object* v_snd_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v_e_2255_);
v_val_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_val_2257_);
lean_dec_ref(v___x_2256_);
v_fst_2258_ = lean_ctor_get(v_val_2257_, 0);
lean_inc_n(v_fst_2258_, 2);
v_snd_2259_ = lean_ctor_get(v_val_2257_, 1);
lean_inc(v_snd_2259_);
lean_dec(v_val_2257_);
v___x_2260_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2258_);
v___x_2261_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2258_, v___x_2260_, v_snd_2259_);
return v___x_2261_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Array_mkArray0(lean_box(0));
return v___x_2272_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2311_ = l_String_toRawSubstring_x27(v___x_2310_);
return v___x_2311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2328_ = l_String_toRawSubstring_x27(v___x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2343_, lean_object* v_default_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v_handlers_2351_; 
v___x_2350_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2351_ = l_Lean_Syntax_SepArray_ofElems(v___x_2350_, v_handlers_2343_);
switch(lean_obj_tag(v_default_2344_))
{
case 0:
{
lean_object* v_ref_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_ref_2352_ = lean_ctor_get(v_a_2347_, 5);
v___x_2353_ = 0;
v___x_2354_ = l_Lean_SourceInfo_fromRef(v_ref_2352_, v___x_2353_);
v___x_2355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2356_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2354_, 3);
v___x_2357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2354_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2359_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2360_ = l_Array_append___redArg(v___x_2359_, v_handlers_2351_);
lean_dec_ref(v_handlers_2351_);
v___x_2361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2354_);
lean_ctor_set(v___x_2361_, 1, v___x_2358_);
lean_ctor_set(v___x_2361_, 2, v___x_2360_);
v___x_2362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2354_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = l_Lean_Syntax_node3(v___x_2354_, v___x_2355_, v___x_2357_, v___x_2361_, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
case 1:
{
lean_object* v_ref_2366_; lean_object* v_quotContext_2367_; lean_object* v_currMacroScope_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_ref_2366_ = lean_ctor_get(v_a_2347_, 5);
v_quotContext_2367_ = lean_ctor_get(v_a_2347_, 10);
v_currMacroScope_2368_ = lean_ctor_get(v_a_2347_, 11);
v___x_2369_ = 0;
v___x_2370_ = l_Lean_SourceInfo_fromRef(v_ref_2366_, v___x_2369_);
v___x_2371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2370_, 12);
v___x_2373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2370_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2370_);
lean_ctor_set(v___x_2379_, 1, v___x_2377_);
v___x_2380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2370_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2384_ = l_Array_append___redArg(v___x_2383_, v_handlers_2351_);
lean_dec_ref(v_handlers_2351_);
v___x_2385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2370_);
lean_ctor_set(v___x_2385_, 1, v___x_2350_);
v___x_2386_ = lean_array_push(v___x_2384_, v___x_2385_);
v___x_2387_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2368_);
lean_inc(v_quotContext_2367_);
v___x_2389_ = l_Lean_addMacroScope(v_quotContext_2367_, v___x_2388_, v_currMacroScope_2368_);
v___x_2390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2391_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2370_);
lean_ctor_set(v___x_2391_, 1, v___x_2387_);
lean_ctor_set(v___x_2391_, 2, v___x_2389_);
lean_ctor_set(v___x_2391_, 3, v___x_2390_);
v___x_2392_ = lean_array_push(v___x_2386_, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2370_);
lean_ctor_set(v___x_2393_, 1, v___x_2376_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
v___x_2394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2370_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Lean_Syntax_node3(v___x_2370_, v___x_2380_, v___x_2382_, v___x_2393_, v___x_2395_);
v___x_2397_ = l_Lean_Syntax_node2(v___x_2370_, v___x_2378_, v___x_2379_, v___x_2396_);
v___x_2398_ = l_Lean_Syntax_node1(v___x_2370_, v___x_2376_, v___x_2397_);
v___x_2399_ = l_Lean_Syntax_node1(v___x_2370_, v___x_2375_, v___x_2398_);
v___x_2400_ = l_Lean_Syntax_node1(v___x_2370_, v___x_2374_, v___x_2399_);
v___x_2401_ = l_Lean_Syntax_node2(v___x_2370_, v___x_2371_, v___x_2373_, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
return v___x_2402_;
}
case 2:
{
lean_object* v_ref_2403_; lean_object* v_quotContext_2404_; lean_object* v_currMacroScope_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_ref_2403_ = lean_ctor_get(v_a_2347_, 5);
v_quotContext_2404_ = lean_ctor_get(v_a_2347_, 10);
v_currMacroScope_2405_ = lean_ctor_get(v_a_2347_, 11);
v___x_2406_ = 0;
v___x_2407_ = l_Lean_SourceInfo_fromRef(v_ref_2403_, v___x_2406_);
v___x_2408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2407_, 12);
v___x_2410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2407_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2407_);
lean_ctor_set(v___x_2416_, 1, v___x_2414_);
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2419_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2407_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2421_ = l_Array_append___redArg(v___x_2420_, v_handlers_2351_);
lean_dec_ref(v_handlers_2351_);
v___x_2422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2407_);
lean_ctor_set(v___x_2422_, 1, v___x_2350_);
v___x_2423_ = lean_array_push(v___x_2421_, v___x_2422_);
v___x_2424_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
lean_inc(v_currMacroScope_2405_);
lean_inc(v_quotContext_2404_);
v___x_2426_ = l_Lean_addMacroScope(v_quotContext_2404_, v___x_2425_, v_currMacroScope_2405_);
v___x_2427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
v___x_2428_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2407_);
lean_ctor_set(v___x_2428_, 1, v___x_2424_);
lean_ctor_set(v___x_2428_, 2, v___x_2426_);
lean_ctor_set(v___x_2428_, 3, v___x_2427_);
v___x_2429_ = lean_array_push(v___x_2423_, v___x_2428_);
v___x_2430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2407_);
lean_ctor_set(v___x_2430_, 1, v___x_2413_);
lean_ctor_set(v___x_2430_, 2, v___x_2429_);
v___x_2431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2407_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = l_Lean_Syntax_node3(v___x_2407_, v___x_2417_, v___x_2419_, v___x_2430_, v___x_2432_);
v___x_2434_ = l_Lean_Syntax_node2(v___x_2407_, v___x_2415_, v___x_2416_, v___x_2433_);
v___x_2435_ = l_Lean_Syntax_node1(v___x_2407_, v___x_2413_, v___x_2434_);
v___x_2436_ = l_Lean_Syntax_node1(v___x_2407_, v___x_2412_, v___x_2435_);
v___x_2437_ = l_Lean_Syntax_node1(v___x_2407_, v___x_2411_, v___x_2436_);
v___x_2438_ = l_Lean_Syntax_node2(v___x_2407_, v___x_2408_, v___x_2410_, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
default: 
{
lean_object* v_e_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_e_2440_ = lean_ctor_get(v_default_2344_, 0);
lean_inc_ref(v_e_2440_);
lean_dec_ref(v_default_2344_);
v___x_2441_ = lean_box(1);
v___x_2442_ = l_Lean_PrettyPrinter_delab(v_e_2440_, v___x_2441_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2479_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2479_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2479_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_ref_2447_; uint8_t v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v_ref_2447_ = lean_ctor_get(v_a_2347_, 5);
v___x_2448_ = 0;
v___x_2449_ = l_Lean_SourceInfo_fromRef(v_ref_2447_, v___x_2448_);
v___x_2450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2449_, 11);
v___x_2452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2449_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2449_);
lean_ctor_set(v___x_2458_, 1, v___x_2456_);
v___x_2459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2449_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2463_ = l_Array_append___redArg(v___x_2462_, v_handlers_2351_);
lean_dec_ref(v_handlers_2351_);
v___x_2464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2449_);
lean_ctor_set(v___x_2464_, 1, v___x_2350_);
v___x_2465_ = lean_array_push(v___x_2463_, v___x_2464_);
v___x_2466_ = lean_array_push(v___x_2465_, v_a_2443_);
v___x_2467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2449_);
lean_ctor_set(v___x_2467_, 1, v___x_2455_);
lean_ctor_set(v___x_2467_, 2, v___x_2466_);
v___x_2468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2449_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = l_Lean_Syntax_node3(v___x_2449_, v___x_2459_, v___x_2461_, v___x_2467_, v___x_2469_);
v___x_2471_ = l_Lean_Syntax_node2(v___x_2449_, v___x_2457_, v___x_2458_, v___x_2470_);
v___x_2472_ = l_Lean_Syntax_node1(v___x_2449_, v___x_2455_, v___x_2471_);
v___x_2473_ = l_Lean_Syntax_node1(v___x_2449_, v___x_2454_, v___x_2472_);
v___x_2474_ = l_Lean_Syntax_node1(v___x_2449_, v___x_2453_, v___x_2473_);
v___x_2475_ = l_Lean_Syntax_node2(v___x_2449_, v___x_2450_, v___x_2452_, v___x_2474_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2475_);
v___x_2477_ = v___x_2445_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
else
{
lean_dec_ref(v_handlers_2351_);
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2480_, lean_object* v_default_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2480_, v_default_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec_ref(v_handlers_2480_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v___x_2491_; 
v___x_2491_ = l_Lean_Expr_hasMVar(v_e_2488_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_e_2488_);
return v___x_2492_;
}
else
{
lean_object* v___x_2493_; lean_object* v_mctx_2494_; lean_object* v___x_2495_; lean_object* v_fst_2496_; lean_object* v_snd_2497_; lean_object* v___x_2498_; lean_object* v_cache_2499_; lean_object* v_zetaDeltaFVarIds_2500_; lean_object* v_postponed_2501_; lean_object* v_diag_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2511_; 
v___x_2493_ = lean_st_ref_get(v___y_2489_);
v_mctx_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc_ref(v_mctx_2494_);
lean_dec(v___x_2493_);
v___x_2495_ = l_Lean_instantiateMVarsCore(v_mctx_2494_, v_e_2488_);
v_fst_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_fst_2496_);
v_snd_2497_ = lean_ctor_get(v___x_2495_, 1);
lean_inc(v_snd_2497_);
lean_dec_ref(v___x_2495_);
v___x_2498_ = lean_st_ref_take(v___y_2489_);
v_cache_2499_ = lean_ctor_get(v___x_2498_, 1);
v_zetaDeltaFVarIds_2500_ = lean_ctor_get(v___x_2498_, 2);
v_postponed_2501_ = lean_ctor_get(v___x_2498_, 3);
v_diag_2502_ = lean_ctor_get(v___x_2498_, 4);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v___x_2498_, 0);
lean_dec(v_unused_2512_);
v___x_2504_ = v___x_2498_;
v_isShared_2505_ = v_isSharedCheck_2511_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_diag_2502_);
lean_inc(v_postponed_2501_);
lean_inc(v_zetaDeltaFVarIds_2500_);
lean_inc(v_cache_2499_);
lean_dec(v___x_2498_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2511_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v_snd_2497_);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_snd_2497_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_cache_2499_);
lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_zetaDeltaFVarIds_2500_);
lean_ctor_set(v_reuseFailAlloc_2510_, 3, v_postponed_2501_);
lean_ctor_set(v_reuseFailAlloc_2510_, 4, v_diag_2502_);
v___x_2507_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_st_ref_set(v___y_2489_, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_fst_2496_);
return v___x_2509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2513_, v___y_2514_);
lean_dec(v___y_2514_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2517_, v___y_2523_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___x_2549_; 
lean_inc(v___y_2543_);
lean_inc_ref(v___y_2542_);
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
v___x_2549_ = lean_apply_9(v_x_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, lean_box(0));
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2561_, lean_object* v_x_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___f_2572_; lean_object* v___x_2573_; 
lean_inc(v___y_2566_);
lean_inc_ref(v___y_2565_);
lean_inc(v___y_2564_);
lean_inc_ref(v___y_2563_);
v___f_2572_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2572_, 0, v_x_2562_);
lean_closure_set(v___f_2572_, 1, v___y_2563_);
lean_closure_set(v___f_2572_, 2, v___y_2564_);
lean_closure_set(v___f_2572_, 3, v___y_2565_);
lean_closure_set(v___f_2572_, 4, v___y_2566_);
v___x_2573_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2561_, v___f_2572_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2573_) == 0)
{
return v___x_2573_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2582_, lean_object* v_x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2582_, v_x_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2594_, lean_object* v_mvarId_2595_, lean_object* v_x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2595_, v_x_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2607_, lean_object* v_mvarId_2608_, lean_object* v_x_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2607_, v_mvarId_2608_, v_x_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2620_, lean_object* v_inv_2621_, lean_object* v_xs_2622_, uint8_t v___x_2623_, lean_object* v___x_2624_, lean_object* v_letMuts_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
lean_inc_ref(v_letMuts_2625_);
lean_inc_ref(v_xs_2622_);
v___x_2635_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2620_, v_inv_2621_, v_xs_2622_, v_letMuts_2625_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2712_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2712_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2712_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
if (lean_obj_tag(v_a_2636_) == 1)
{
lean_object* v_val_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2707_; 
lean_del_object(v___x_2638_);
v_val_2640_ = lean_ctor_get(v_a_2636_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_a_2636_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2642_ = v_a_2636_;
v_isShared_2643_ = v_isSharedCheck_2707_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_val_2640_);
lean_dec(v_a_2636_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2707_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_snd_2644_; lean_object* v_fst_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2706_; 
v_snd_2644_ = lean_ctor_get(v_val_2640_, 1);
v_fst_2645_ = lean_ctor_get(v_val_2640_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_val_2640_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2647_ = v_val_2640_;
v_isShared_2648_ = v_isSharedCheck_2706_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_snd_2644_);
lean_inc(v_fst_2645_);
lean_dec(v_val_2640_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2706_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_fst_2649_; lean_object* v_snd_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2705_; 
v_fst_2649_ = lean_ctor_get(v_snd_2644_, 0);
v_snd_2650_ = lean_ctor_get(v_snd_2644_, 1);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_snd_2644_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2652_ = v_snd_2644_;
v_isShared_2653_ = v_isSharedCheck_2705_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_snd_2650_);
lean_inc(v_fst_2649_);
lean_dec(v_snd_2644_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2705_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v_lvl_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; uint8_t v___x_2664_; lean_object* v___x_2665_; 
v_lvl_2654_ = lean_ctor_get(v_fst_2645_, 0);
lean_inc(v_lvl_2654_);
v___x_2655_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2645_);
lean_inc(v_fst_2649_);
v___x_2656_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2649_);
v___x_2657_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2654_, v___x_2655_, v___x_2656_);
v___x_2658_ = lean_unsigned_to_nat(2u);
v___x_2659_ = lean_mk_empty_array_with_capacity(v___x_2658_);
v___x_2660_ = lean_array_push(v___x_2659_, v_xs_2622_);
lean_inc_ref(v_letMuts_2625_);
v___x_2661_ = lean_array_push(v___x_2660_, v_letMuts_2625_);
v___x_2662_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2657_);
v___x_2663_ = 0;
v___x_2664_ = 1;
v___x_2665_ = l_Lean_Meta_mkLambdaFVars(v___x_2661_, v___x_2662_, v___x_2663_, v___x_2623_, v___x_2663_, v___x_2623_, v___x_2664_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec_ref(v___x_2661_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v_letMutsPred_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref(v___x_2665_);
v_letMutsPred_2667_ = lean_ctor_get(v_fst_2649_, 2);
lean_inc_ref(v_letMutsPred_2667_);
lean_dec(v_fst_2649_);
v___x_2668_ = lean_mk_empty_array_with_capacity(v___x_2624_);
v___x_2669_ = lean_array_push(v___x_2668_, v_letMuts_2625_);
v___x_2670_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2667_);
v___x_2671_ = l_Lean_Meta_mkLambdaFVars(v___x_2669_, v___x_2670_, v___x_2663_, v___x_2623_, v___x_2663_, v___x_2623_, v___x_2664_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec_ref(v___x_2669_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2688_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2688_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2688_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v_a_2672_);
v___x_2677_ = v___x_2652_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2672_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_snd_2650_);
v___x_2677_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2677_);
lean_ctor_set(v___x_2647_, 0, v_a_2666_);
v___x_2679_ = v___x_2647_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2666_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2681_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2679_);
v___x_2681_ = v___x_2642_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2683_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2681_);
v___x_2683_ = v___x_2674_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_a_2666_);
lean_del_object(v___x_2652_);
lean_dec(v_snd_2650_);
lean_del_object(v___x_2647_);
lean_del_object(v___x_2642_);
v_a_2689_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2671_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2671_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_del_object(v___x_2652_);
lean_dec(v_snd_2650_);
lean_dec(v_fst_2649_);
lean_del_object(v___x_2647_);
lean_del_object(v___x_2642_);
lean_dec_ref(v_letMuts_2625_);
v_a_2697_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2665_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2665_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
lean_dec(v_a_2636_);
lean_dec_ref(v_letMuts_2625_);
lean_dec_ref(v_xs_2622_);
v___x_2708_ = lean_box(0);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2708_);
v___x_2710_ = v___x_2638_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_letMuts_2625_);
lean_dec_ref(v_xs_2622_);
v_a_2713_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2635_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2635_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2721_, lean_object* v_inv_2722_, lean_object* v_xs_2723_, lean_object* v___x_2724_, lean_object* v___x_2725_, lean_object* v_letMuts_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
uint8_t v___x_91951__boxed_2736_; lean_object* v_res_2737_; 
v___x_91951__boxed_2736_ = lean_unbox(v___x_2724_);
v_res_2737_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2721_, v_inv_2722_, v_xs_2723_, v___x_91951__boxed_2736_, v___x_2725_, v_letMuts_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___x_2725_);
lean_dec_ref(v_a_2721_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v_b_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2749_; 
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2742_);
lean_inc_ref(v___y_2741_);
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2739_);
v___x_2749_ = lean_apply_10(v_k_2738_, v_b_2743_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, lean_box(0));
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v_b_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v_b_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2762_, uint8_t v_bi_2763_, lean_object* v_type_2764_, lean_object* v_k_2765_, uint8_t v_kind_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___f_2776_; lean_object* v___x_2777_; 
lean_inc(v___y_2770_);
lean_inc_ref(v___y_2769_);
lean_inc(v___y_2768_);
lean_inc_ref(v___y_2767_);
v___f_2776_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2776_, 0, v_k_2765_);
lean_closure_set(v___f_2776_, 1, v___y_2767_);
lean_closure_set(v___f_2776_, 2, v___y_2768_);
lean_closure_set(v___f_2776_, 3, v___y_2769_);
lean_closure_set(v___f_2776_, 4, v___y_2770_);
v___x_2777_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2762_, v_bi_2763_, v_type_2764_, v___f_2776_, v_kind_2766_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2777_) == 0)
{
return v___x_2777_;
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2786_, lean_object* v_bi_2787_, lean_object* v_type_2788_, lean_object* v_k_2789_, lean_object* v_kind_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
uint8_t v_bi_boxed_2800_; uint8_t v_kind_boxed_2801_; lean_object* v_res_2802_; 
v_bi_boxed_2800_ = lean_unbox(v_bi_2787_);
v_kind_boxed_2801_ = lean_unbox(v_kind_2790_);
v_res_2802_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2786_, v_bi_boxed_2800_, v_type_2788_, v_k_2789_, v_kind_boxed_2801_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2803_, lean_object* v_type_2804_, lean_object* v_k_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v___x_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; 
v___x_2815_ = 0;
v___x_2816_ = 0;
v___x_2817_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2803_, v___x_2815_, v_type_2804_, v_k_2805_, v___x_2816_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2818_, lean_object* v_type_2819_, lean_object* v_k_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2818_, v_type_2819_, v_k_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2834_, lean_object* v_inv_2835_, uint8_t v___x_2836_, lean_object* v___x_2837_, lean_object* v_arg_2838_, lean_object* v_xs_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v___f_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2849_ = lean_box(v___x_2836_);
v___f_2850_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2850_, 0, v_a_2834_);
lean_closure_set(v___f_2850_, 1, v_inv_2835_);
lean_closure_set(v___f_2850_, 2, v_xs_2839_);
lean_closure_set(v___f_2850_, 3, v___x_2849_);
lean_closure_set(v___f_2850_, 4, v___x_2837_);
v___x_2851_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2852_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2851_, v_arg_2838_, v___f_2850_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2853_, lean_object* v_inv_2854_, lean_object* v___x_2855_, lean_object* v___x_2856_, lean_object* v_arg_2857_, lean_object* v_xs_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
uint8_t v___x_92271__boxed_2868_; lean_object* v_res_2869_; 
v___x_92271__boxed_2868_ = lean_unbox(v___x_2855_);
v_res_2869_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2853_, v_inv_2854_, v___x_92271__boxed_2868_, v___x_2856_, v_arg_2857_, v_xs_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2869_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2873_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
return v___x_2875_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = lean_unsigned_to_nat(32u);
v___x_2877_ = lean_mk_empty_array_with_capacity(v___x_2876_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2879_, lean_object* v_r_2880_, uint8_t v___x_2881_, lean_object* v___x_2882_, lean_object* v___x_2883_, lean_object* v_xs_2884_, lean_object* v_fst_2885_, lean_object* v_fst_2886_, lean_object* v_letMuts_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
lean_inc_ref(v_fst_2879_);
v___x_2897_ = l_Lean_Meta_mkNone(v_fst_2879_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1));
v___x_2900_ = lean_unsigned_to_nat(2u);
v___x_2901_ = lean_mk_empty_array_with_capacity(v___x_2900_);
lean_inc_ref(v___x_2901_);
v___x_2902_ = lean_array_push(v___x_2901_, v_a_2898_);
lean_inc_ref(v_letMuts_2887_);
v___x_2903_ = lean_array_push(v___x_2902_, v_letMuts_2887_);
v___x_2904_ = l_Lean_Meta_mkAppM(v___x_2899_, v___x_2903_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = l_Lean_Meta_mkSome(v_fst_2879_, v_r_2880_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref(v___x_2906_);
lean_inc_ref(v___x_2901_);
v___x_2908_ = lean_array_push(v___x_2901_, v_a_2907_);
v___x_2909_ = lean_array_push(v___x_2908_, v_letMuts_2887_);
v___x_2910_ = l_Lean_Meta_mkAppM(v___x_2899_, v___x_2909_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
v___x_2912_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2895_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
v___x_2914_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2895_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; uint8_t v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
v___x_2916_ = lean_unsigned_to_nat(100000u);
v___x_2917_ = 0;
v___x_2918_ = 0;
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2920_, 0, v___x_2916_);
lean_ctor_set(v___x_2920_, 1, v___x_2900_);
lean_ctor_set(v___x_2920_, 2, v___x_2919_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 1, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 2, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 3, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 4, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 5, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 6, v___x_2918_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 7, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 8, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 9, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 10, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 11, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 12, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 13, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 14, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 15, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 16, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 17, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 18, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 19, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 20, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 21, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 22, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 23, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 24, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 25, v___x_2881_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 26, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 27, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 28, v___x_2917_);
v___x_2921_ = lean_mk_empty_array_with_capacity(v___x_2882_);
lean_inc_ref(v___x_2921_);
v___x_2922_ = lean_array_push(v___x_2921_, v_a_2913_);
v___x_2923_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2920_, v___x_2922_, v_a_2915_, v___y_2892_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref(v___x_2923_);
v___x_2925_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2926_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2927_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2925_, v___x_2926_, v___x_2917_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; size_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc_n(v_a_2928_, 2);
lean_dec_ref(v___x_2927_);
v___x_2929_ = lean_array_push(v___x_2901_, v_xs_2884_);
v___x_2930_ = lean_array_push(v___x_2929_, v_a_2905_);
v___x_2931_ = l_Lean_Expr_beta(v_fst_2885_, v___x_2930_);
v___x_2932_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2883_, 2);
v___x_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v___x_2883_);
v___x_2934_ = lean_unsigned_to_nat(32u);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_2936_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2937_ = ((size_t)5ULL);
v___x_2938_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2935_);
lean_ctor_set(v___x_2938_, 2, v___x_2883_);
lean_ctor_set(v___x_2938_, 3, v___x_2883_);
lean_ctor_set_usize(v___x_2938_, 4, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2932_);
lean_ctor_set(v___x_2939_, 1, v___x_2932_);
lean_ctor_set(v___x_2939_, 2, v___x_2932_);
lean_ctor_set(v___x_2939_, 3, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2933_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
lean_inc(v_a_2924_);
v___x_2941_ = l_Lean_Meta_simp(v___x_2931_, v_a_2924_, v_a_2928_, v___x_2919_, v___x_2940_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v_fst_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
v_fst_2943_ = lean_ctor_get(v_a_2942_, 0);
lean_inc(v_fst_2943_);
lean_dec(v_a_2942_);
v___x_2944_ = lean_array_push(v___x_2921_, v_a_2911_);
v___x_2945_ = l_Lean_Expr_beta(v_fst_2886_, v___x_2944_);
v___x_2946_ = l_Lean_Meta_simp(v___x_2945_, v_a_2924_, v_a_2928_, v___x_2919_, v___x_2940_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec_ref(v___x_2940_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v_fst_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2985_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref(v___x_2946_);
v_fst_2948_ = lean_ctor_get(v_a_2947_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v_a_2947_, 1);
lean_dec(v_unused_2986_);
v___x_2950_ = v_a_2947_;
v_isShared_2951_ = v_isSharedCheck_2985_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_fst_2948_);
lean_dec(v_a_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2985_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v_expr_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_expr_2952_ = lean_ctor_get(v_fst_2943_, 0);
lean_inc_ref(v_expr_2952_);
lean_dec(v_fst_2943_);
v___x_2953_ = lean_box(1);
v___x_2954_ = l_Lean_PrettyPrinter_delab(v_expr_2952_, v___x_2953_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v_expr_2956_; lean_object* v___x_2957_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref(v___x_2954_);
v_expr_2956_ = lean_ctor_get(v_fst_2948_, 0);
lean_inc_ref(v_expr_2956_);
lean_dec(v_fst_2948_);
v___x_2957_ = l_Lean_PrettyPrinter_delab(v_expr_2956_, v___x_2953_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2968_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2968_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2968_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v_a_2958_);
lean_ctor_set(v___x_2950_, 0, v_a_2955_);
v___x_2963_ = v___x_2950_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2955_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2965_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2963_);
v___x_2965_ = v___x_2960_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_a_2955_);
lean_del_object(v___x_2950_);
v_a_2969_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2957_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2957_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_del_object(v___x_2950_);
lean_dec(v_fst_2948_);
v_a_2977_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2954_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2954_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec(v_fst_2943_);
v_a_2987_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2946_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2946_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref(v___x_2940_);
lean_dec(v_a_2928_);
lean_dec(v_a_2924_);
lean_dec_ref(v___x_2921_);
lean_dec(v_a_2911_);
lean_dec_ref(v_fst_2886_);
v_a_2995_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2941_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2941_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2924_);
lean_dec_ref(v___x_2921_);
lean_dec(v_a_2911_);
lean_dec(v_a_2905_);
lean_dec_ref(v___x_2901_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v_fst_2885_);
lean_dec_ref(v_xs_2884_);
lean_dec(v___x_2883_);
v_a_3003_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2927_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2927_);
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
lean_dec_ref(v___x_2921_);
lean_dec(v_a_2911_);
lean_dec(v_a_2905_);
lean_dec_ref(v___x_2901_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v_fst_2885_);
lean_dec_ref(v_xs_2884_);
lean_dec(v___x_2883_);
v_a_3011_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2923_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2923_);
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
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_a_2913_);
lean_dec(v_a_2911_);
lean_dec(v_a_2905_);
lean_dec_ref(v___x_2901_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v_fst_2885_);
lean_dec_ref(v_xs_2884_);
lean_dec(v___x_2883_);
v_a_3019_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2914_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2914_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_a_2911_);
lean_dec(v_a_2905_);
lean_dec_ref(v___x_2901_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v_fst_2885_);
lean_dec_ref(v_xs_2884_);
lean_dec(v___x_2883_);
v_a_3027_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2912_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2912_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_a_2905_);
lean_dec_ref(v___x_2901_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v_fst_2885_);
lean_dec_ref(v_xs_2884_);
lean_dec(v___x_2883_);
v_a_3035_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_2910_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_2910_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_a_2905_);
lean_dec_ref(v___x_2901_);
lean_dec_ref(v_letMuts_2887_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v_fst_2885_);
lean_dec_ref(v_xs_2884_);
lean_dec(v___x_2883_);
v_a_3043_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2906_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2906_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v___x_2901_);
lean_dec_ref(v_letMuts_2887_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v_fst_2885_);
lean_dec_ref(v_xs_2884_);
lean_dec(v___x_2883_);
lean_dec_ref(v_r_2880_);
lean_dec_ref(v_fst_2879_);
v_a_3051_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_2904_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_2904_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v_letMuts_2887_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v_fst_2885_);
lean_dec_ref(v_xs_2884_);
lean_dec(v___x_2883_);
lean_dec_ref(v_r_2880_);
lean_dec_ref(v_fst_2879_);
v_a_3059_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_2897_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_2897_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3067_ = _args[0];
lean_object* v_r_3068_ = _args[1];
lean_object* v___x_3069_ = _args[2];
lean_object* v___x_3070_ = _args[3];
lean_object* v___x_3071_ = _args[4];
lean_object* v_xs_3072_ = _args[5];
lean_object* v_fst_3073_ = _args[6];
lean_object* v_fst_3074_ = _args[7];
lean_object* v_letMuts_3075_ = _args[8];
lean_object* v___y_3076_ = _args[9];
lean_object* v___y_3077_ = _args[10];
lean_object* v___y_3078_ = _args[11];
lean_object* v___y_3079_ = _args[12];
lean_object* v___y_3080_ = _args[13];
lean_object* v___y_3081_ = _args[14];
lean_object* v___y_3082_ = _args[15];
lean_object* v___y_3083_ = _args[16];
lean_object* v___y_3084_ = _args[17];
_start:
{
uint8_t v___x_92344__boxed_3085_; lean_object* v_res_3086_; 
v___x_92344__boxed_3085_ = lean_unbox(v___x_3069_);
v_res_3086_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3067_, v_r_3068_, v___x_92344__boxed_3085_, v___x_3070_, v___x_3071_, v_xs_3072_, v_fst_3073_, v_fst_3074_, v_letMuts_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___x_3070_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3087_, uint8_t v___x_3088_, lean_object* v___x_3089_, lean_object* v___x_3090_, lean_object* v_xs_3091_, lean_object* v_fst_3092_, lean_object* v_fst_3093_, lean_object* v_snd_3094_, lean_object* v_r_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v___f_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3105_ = lean_box(v___x_3088_);
v___f_3106_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3106_, 0, v_fst_3087_);
lean_closure_set(v___f_3106_, 1, v_r_3095_);
lean_closure_set(v___f_3106_, 2, v___x_3105_);
lean_closure_set(v___f_3106_, 3, v___x_3089_);
lean_closure_set(v___f_3106_, 4, v___x_3090_);
lean_closure_set(v___f_3106_, 5, v_xs_3091_);
lean_closure_set(v___f_3106_, 6, v_fst_3092_);
lean_closure_set(v___f_3106_, 7, v_fst_3093_);
v___x_3107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3108_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3107_, v_snd_3094_, v___f_3106_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3109_ = _args[0];
lean_object* v___x_3110_ = _args[1];
lean_object* v___x_3111_ = _args[2];
lean_object* v___x_3112_ = _args[3];
lean_object* v_xs_3113_ = _args[4];
lean_object* v_fst_3114_ = _args[5];
lean_object* v_fst_3115_ = _args[6];
lean_object* v_snd_3116_ = _args[7];
lean_object* v_r_3117_ = _args[8];
lean_object* v___y_3118_ = _args[9];
lean_object* v___y_3119_ = _args[10];
lean_object* v___y_3120_ = _args[11];
lean_object* v___y_3121_ = _args[12];
lean_object* v___y_3122_ = _args[13];
lean_object* v___y_3123_ = _args[14];
lean_object* v___y_3124_ = _args[15];
lean_object* v___y_3125_ = _args[16];
lean_object* v___y_3126_ = _args[17];
_start:
{
uint8_t v___x_92738__boxed_3127_; lean_object* v_res_3128_; 
v___x_92738__boxed_3127_ = lean_unbox(v___x_3110_);
v_res_3128_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3109_, v___x_92738__boxed_3127_, v___x_3111_, v___x_3112_, v_xs_3113_, v_fst_3114_, v_fst_3115_, v_snd_3116_, v_r_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3132_, uint8_t v___x_3133_, lean_object* v___x_3134_, lean_object* v___x_3135_, lean_object* v_fst_3136_, lean_object* v_fst_3137_, lean_object* v_snd_3138_, lean_object* v_xs_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v___f_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3149_ = lean_box(v___x_3133_);
lean_inc_ref(v_fst_3132_);
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3150_, 0, v_fst_3132_);
lean_closure_set(v___f_3150_, 1, v___x_3149_);
lean_closure_set(v___f_3150_, 2, v___x_3134_);
lean_closure_set(v___f_3150_, 3, v___x_3135_);
lean_closure_set(v___f_3150_, 4, v_xs_3139_);
lean_closure_set(v___f_3150_, 5, v_fst_3136_);
lean_closure_set(v___f_3150_, 6, v_fst_3137_);
lean_closure_set(v___f_3150_, 7, v_snd_3138_);
v___x_3151_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3152_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3151_, v_fst_3132_, v___f_3150_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3153_ = _args[0];
lean_object* v___x_3154_ = _args[1];
lean_object* v___x_3155_ = _args[2];
lean_object* v___x_3156_ = _args[3];
lean_object* v_fst_3157_ = _args[4];
lean_object* v_fst_3158_ = _args[5];
lean_object* v_snd_3159_ = _args[6];
lean_object* v_xs_3160_ = _args[7];
lean_object* v___y_3161_ = _args[8];
lean_object* v___y_3162_ = _args[9];
lean_object* v___y_3163_ = _args[10];
lean_object* v___y_3164_ = _args[11];
lean_object* v___y_3165_ = _args[12];
lean_object* v___y_3166_ = _args[13];
lean_object* v___y_3167_ = _args[14];
lean_object* v___y_3168_ = _args[15];
lean_object* v___y_3169_ = _args[16];
_start:
{
uint8_t v___x_92801__boxed_3170_; lean_object* v_res_3171_; 
v___x_92801__boxed_3170_ = lean_unbox(v___x_3154_);
v_res_3171_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3153_, v___x_92801__boxed_3170_, v___x_3155_, v___x_3156_, v_fst_3157_, v_fst_3158_, v_snd_3159_, v_xs_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3172_, size_t v_sz_3173_, size_t v_i_3174_, lean_object* v_b_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_usize_dec_lt(v_i_3174_, v_sz_3173_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_b_3175_);
return v___x_3182_;
}
else
{
lean_object* v___x_3183_; lean_object* v_a_3184_; lean_object* v___x_3185_; 
v___x_3183_ = lean_box(1);
v_a_3184_ = lean_array_uget_borrowed(v_as_3172_, v_i_3174_);
lean_inc(v_a_3184_);
v___x_3185_ = l_Lean_PrettyPrinter_delab(v_a_3184_, v___x_3183_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; size_t v___x_3188_; size_t v___x_3189_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref(v___x_3185_);
v___x_3187_ = lean_array_push(v_b_3175_, v_a_3186_);
v___x_3188_ = ((size_t)1ULL);
v___x_3189_ = lean_usize_add(v_i_3174_, v___x_3188_);
v_i_3174_ = v___x_3189_;
v_b_3175_ = v___x_3187_;
goto _start;
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v_b_3175_);
v_a_3191_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3185_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3185_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3199_, lean_object* v_sz_3200_, lean_object* v_i_3201_, lean_object* v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
size_t v_sz_boxed_3208_; size_t v_i_boxed_3209_; lean_object* v_res_3210_; 
v_sz_boxed_3208_ = lean_unbox_usize(v_sz_3200_);
lean_dec(v_sz_3200_);
v_i_boxed_3209_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_res_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3199_, v_sz_boxed_3208_, v_i_boxed_3209_, v_b_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec_ref(v_as_3199_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3231_, lean_object* v_fst_3232_, lean_object* v_snd_3233_, lean_object* v___x_3234_, lean_object* v___x_3235_, lean_object* v___x_3236_, lean_object* v___x_3237_, lean_object* v___x_3238_, lean_object* v___x_3239_, lean_object* v___x_3240_, uint8_t v___x_3241_, lean_object* v___x_3242_, lean_object* v_letMuts_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3253_ = lean_unsigned_to_nat(2u);
v___x_3254_ = lean_mk_empty_array_with_capacity(v___x_3253_);
v___x_3255_ = lean_array_push(v___x_3254_, v_xs_3231_);
v___x_3256_ = lean_array_push(v___x_3255_, v_letMuts_3243_);
v___x_3257_ = l_Lean_Expr_beta(v_fst_3232_, v___x_3256_);
v___x_3258_ = lean_box(1);
v___x_3259_ = l_Lean_PrettyPrinter_delab(v___x_3257_, v___x_3258_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3398_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3398_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3398_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
uint8_t v___y_3265_; lean_object* v_points_3301_; lean_object* v_default_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3397_; 
v_points_3301_ = lean_ctor_get(v_snd_3233_, 0);
v_default_3302_ = lean_ctor_get(v_snd_3233_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_snd_3233_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3304_ = v_snd_3233_;
v_isShared_3305_ = v_isSharedCheck_3397_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_default_3302_);
lean_inc(v_points_3301_);
lean_dec(v_snd_3233_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3397_;
goto v_resetjp_3303_;
}
v___jp_3264_:
{
lean_object* v_ref_3266_; lean_object* v_quotContext_3267_; lean_object* v_currMacroScope_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
v_ref_3266_ = lean_ctor_get(v___y_3250_, 5);
v_quotContext_3267_ = lean_ctor_get(v___y_3250_, 10);
v_currMacroScope_3268_ = lean_ctor_get(v___y_3250_, 11);
v___x_3269_ = l_Lean_SourceInfo_fromRef(v_ref_3266_, v___y_3265_);
v___x_3270_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3271_ = l_Lean_Name_mkStr3(v___x_3234_, v___x_3235_, v___x_3270_);
v___x_3272_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3273_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3269_, 11);
v___x_3274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3269_);
lean_ctor_set(v___x_3274_, 1, v___x_3272_);
lean_ctor_set(v___x_3274_, 2, v___x_3273_);
v___x_3275_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3269_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3269_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = l_String_toRawSubstring_x27(v___x_3236_);
lean_inc_n(v_currMacroScope_3268_, 2);
lean_inc_n(v_quotContext_3267_, 2);
v___x_3282_ = l_Lean_addMacroScope(v_quotContext_3267_, v___x_3237_, v_currMacroScope_3268_);
v___x_3283_ = lean_box(0);
v___x_3284_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3269_);
lean_ctor_set(v___x_3284_, 1, v___x_3281_);
lean_ctor_set(v___x_3284_, 2, v___x_3282_);
lean_ctor_set(v___x_3284_, 3, v___x_3283_);
v___x_3285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3269_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_String_toRawSubstring_x27(v___x_3238_);
v___x_3288_ = l_Lean_addMacroScope(v_quotContext_3267_, v___x_3239_, v_currMacroScope_3268_);
v___x_3289_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3269_);
lean_ctor_set(v___x_3289_, 1, v___x_3287_);
lean_ctor_set(v___x_3289_, 2, v___x_3288_);
lean_ctor_set(v___x_3289_, 3, v___x_3283_);
v___x_3290_ = l_Lean_Syntax_node3(v___x_3269_, v___x_3277_, v___x_3284_, v___x_3286_, v___x_3289_);
v___x_3291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3269_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = l_Lean_Syntax_node3(v___x_3269_, v___x_3278_, v___x_3280_, v___x_3290_, v___x_3292_);
v___x_3294_ = l_Lean_Syntax_node1(v___x_3269_, v___x_3277_, v___x_3293_);
v___x_3295_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3269_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = l_Lean_Syntax_node5(v___x_3269_, v___x_3271_, v___x_3274_, v___x_3276_, v___x_3294_, v___x_3296_, v_a_3260_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3297_);
v___x_3299_ = v___x_3262_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
v_resetjp_3303_:
{
uint8_t v___y_3307_; uint8_t v___y_3358_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3394_ = lean_array_get_size(v_points_3301_);
v___x_3395_ = lean_nat_dec_eq(v___x_3394_, v___x_3242_);
if (v___x_3395_ == 0)
{
v___y_3358_ = v___x_3395_;
goto v___jp_3357_;
}
else
{
if (lean_obj_tag(v_default_3302_) == 3)
{
if (v___x_3395_ == 0)
{
v___y_3358_ = v___x_3395_;
goto v___jp_3357_;
}
else
{
uint8_t v___x_3396_; 
lean_del_object(v___x_3262_);
lean_dec_ref(v___x_3235_);
lean_dec_ref(v___x_3234_);
v___x_3396_ = 0;
v___y_3307_ = v___x_3396_;
goto v___jp_3306_;
}
}
else
{
v___y_3358_ = v___x_3395_;
goto v___jp_3357_;
}
}
v___jp_3306_:
{
lean_object* v_ref_3308_; lean_object* v_quotContext_3309_; lean_object* v_currMacroScope_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v_ref_3308_ = lean_ctor_get(v___y_3250_, 5);
v_quotContext_3309_ = lean_ctor_get(v___y_3250_, 10);
v_currMacroScope_3310_ = lean_ctor_get(v___y_3250_, 11);
v___x_3311_ = l_Lean_SourceInfo_fromRef(v_ref_3308_, v___y_3307_);
v___x_3312_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3313_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3311_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 2);
lean_ctor_set(v___x_3304_, 1, v___x_3312_);
lean_ctor_set(v___x_3304_, 0, v___x_3311_);
v___x_3315_ = v___x_3304_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3312_);
v___x_3315_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; size_t v_sz_3343_; size_t v___x_3344_; lean_object* v___x_3345_; 
v___x_3316_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3311_, 11);
v___x_3320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3311_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = l_String_toRawSubstring_x27(v___x_3236_);
lean_inc_n(v_currMacroScope_3310_, 2);
lean_inc_n(v_quotContext_3309_, 2);
v___x_3322_ = l_Lean_addMacroScope(v_quotContext_3309_, v___x_3237_, v_currMacroScope_3310_);
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3311_);
lean_ctor_set(v___x_3324_, 1, v___x_3321_);
lean_ctor_set(v___x_3324_, 2, v___x_3322_);
lean_ctor_set(v___x_3324_, 3, v___x_3323_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3311_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = l_String_toRawSubstring_x27(v___x_3238_);
v___x_3328_ = l_Lean_addMacroScope(v_quotContext_3309_, v___x_3239_, v_currMacroScope_3310_);
v___x_3329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3311_);
lean_ctor_set(v___x_3329_, 1, v___x_3327_);
lean_ctor_set(v___x_3329_, 2, v___x_3328_);
lean_ctor_set(v___x_3329_, 3, v___x_3323_);
v___x_3330_ = l_Lean_Syntax_node3(v___x_3311_, v___x_3317_, v___x_3324_, v___x_3326_, v___x_3329_);
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3311_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_Syntax_node3(v___x_3311_, v___x_3318_, v___x_3320_, v___x_3330_, v___x_3332_);
v___x_3334_ = l_Lean_Syntax_node1(v___x_3311_, v___x_3317_, v___x_3333_);
v___x_3335_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3311_);
lean_ctor_set(v___x_3336_, 1, v___x_3317_);
lean_ctor_set(v___x_3336_, 2, v___x_3335_);
v___x_3337_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3311_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = l_Lean_Syntax_node4(v___x_3311_, v___x_3316_, v___x_3334_, v___x_3336_, v___x_3338_, v_a_3260_);
v___x_3340_ = l_Lean_Syntax_node2(v___x_3311_, v___x_3313_, v___x_3315_, v___x_3339_);
v___x_3341_ = lean_mk_empty_array_with_capacity(v___x_3240_);
v___x_3342_ = lean_array_push(v___x_3341_, v___x_3340_);
v_sz_3343_ = lean_array_size(v_points_3301_);
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3301_, v_sz_3343_, v___x_3344_, v___x_3342_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec_ref(v_points_3301_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3346_, v_default_3302_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v_a_3346_);
return v___x_3347_;
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec(v_default_3302_);
v_a_3348_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3345_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3345_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
v___jp_3357_:
{
if (v___y_3358_ == 0)
{
lean_del_object(v___x_3262_);
lean_dec_ref(v___x_3235_);
lean_dec_ref(v___x_3234_);
v___y_3307_ = v___y_3358_;
goto v___jp_3306_;
}
else
{
lean_del_object(v___x_3304_);
lean_dec_ref(v_points_3301_);
if (lean_obj_tag(v_default_3302_) == 2)
{
if (v___x_3241_ == 0)
{
v___y_3265_ = v___x_3241_;
goto v___jp_3264_;
}
else
{
lean_object* v_ref_3359_; lean_object* v_quotContext_3360_; lean_object* v_currMacroScope_3361_; uint8_t v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_del_object(v___x_3262_);
v_ref_3359_ = lean_ctor_get(v___y_3250_, 5);
v_quotContext_3360_ = lean_ctor_get(v___y_3250_, 10);
v_currMacroScope_3361_ = lean_ctor_get(v___y_3250_, 11);
v___x_3362_ = 0;
v___x_3363_ = l_Lean_SourceInfo_fromRef(v_ref_3359_, v___x_3362_);
v___x_3364_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3365_ = l_Lean_Name_mkStr3(v___x_3234_, v___x_3235_, v___x_3364_);
v___x_3366_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3367_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3363_, 11);
v___x_3368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3363_);
lean_ctor_set(v___x_3368_, 1, v___x_3366_);
lean_ctor_set(v___x_3368_, 2, v___x_3367_);
v___x_3369_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3363_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3363_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_String_toRawSubstring_x27(v___x_3236_);
lean_inc_n(v_currMacroScope_3361_, 2);
lean_inc_n(v_quotContext_3360_, 2);
v___x_3376_ = l_Lean_addMacroScope(v_quotContext_3360_, v___x_3237_, v_currMacroScope_3361_);
v___x_3377_ = lean_box(0);
v___x_3378_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3363_);
lean_ctor_set(v___x_3378_, 1, v___x_3375_);
lean_ctor_set(v___x_3378_, 2, v___x_3376_);
lean_ctor_set(v___x_3378_, 3, v___x_3377_);
v___x_3379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3363_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = l_String_toRawSubstring_x27(v___x_3238_);
v___x_3382_ = l_Lean_addMacroScope(v_quotContext_3360_, v___x_3239_, v_currMacroScope_3361_);
v___x_3383_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3363_);
lean_ctor_set(v___x_3383_, 1, v___x_3381_);
lean_ctor_set(v___x_3383_, 2, v___x_3382_);
lean_ctor_set(v___x_3383_, 3, v___x_3377_);
v___x_3384_ = l_Lean_Syntax_node3(v___x_3363_, v___x_3371_, v___x_3378_, v___x_3380_, v___x_3383_);
v___x_3385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3363_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = l_Lean_Syntax_node3(v___x_3363_, v___x_3372_, v___x_3374_, v___x_3384_, v___x_3386_);
v___x_3388_ = l_Lean_Syntax_node1(v___x_3363_, v___x_3371_, v___x_3387_);
v___x_3389_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3363_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = l_Lean_Syntax_node5(v___x_3363_, v___x_3365_, v___x_3368_, v___x_3370_, v___x_3388_, v___x_3390_, v_a_3260_);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
else
{
uint8_t v___x_3393_; 
lean_dec(v_default_3302_);
v___x_3393_ = 0;
v___y_3265_ = v___x_3393_;
goto v___jp_3264_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3239_);
lean_dec_ref(v___x_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v___x_3236_);
lean_dec_ref(v___x_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_snd_3233_);
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3399_ = _args[0];
lean_object* v_fst_3400_ = _args[1];
lean_object* v_snd_3401_ = _args[2];
lean_object* v___x_3402_ = _args[3];
lean_object* v___x_3403_ = _args[4];
lean_object* v___x_3404_ = _args[5];
lean_object* v___x_3405_ = _args[6];
lean_object* v___x_3406_ = _args[7];
lean_object* v___x_3407_ = _args[8];
lean_object* v___x_3408_ = _args[9];
lean_object* v___x_3409_ = _args[10];
lean_object* v___x_3410_ = _args[11];
lean_object* v_letMuts_3411_ = _args[12];
lean_object* v___y_3412_ = _args[13];
lean_object* v___y_3413_ = _args[14];
lean_object* v___y_3414_ = _args[15];
lean_object* v___y_3415_ = _args[16];
lean_object* v___y_3416_ = _args[17];
lean_object* v___y_3417_ = _args[18];
lean_object* v___y_3418_ = _args[19];
lean_object* v___y_3419_ = _args[20];
lean_object* v___y_3420_ = _args[21];
_start:
{
uint8_t v___x_93010__boxed_3421_; lean_object* v_res_3422_; 
v___x_93010__boxed_3421_ = lean_unbox(v___x_3409_);
v_res_3422_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3399_, v_fst_3400_, v_snd_3401_, v___x_3402_, v___x_3403_, v___x_3404_, v___x_3405_, v___x_3406_, v___x_3407_, v___x_3408_, v___x_93010__boxed_3421_, v___x_3410_, v_letMuts_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___x_3410_);
lean_dec(v___x_3408_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3423_, lean_object* v_snd_3424_, lean_object* v___x_3425_, lean_object* v___x_3426_, lean_object* v___x_3427_, lean_object* v___x_3428_, lean_object* v___x_3429_, uint8_t v___x_3430_, lean_object* v___x_3431_, lean_object* v_arg_3432_, lean_object* v_xs_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___f_3446_; lean_object* v___x_3447_; 
v___x_3443_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3444_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3445_ = lean_box(v___x_3430_);
v___f_3446_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3446_, 0, v_xs_3433_);
lean_closure_set(v___f_3446_, 1, v_fst_3423_);
lean_closure_set(v___f_3446_, 2, v_snd_3424_);
lean_closure_set(v___f_3446_, 3, v___x_3425_);
lean_closure_set(v___f_3446_, 4, v___x_3426_);
lean_closure_set(v___f_3446_, 5, v___x_3427_);
lean_closure_set(v___f_3446_, 6, v___x_3428_);
lean_closure_set(v___f_3446_, 7, v___x_3443_);
lean_closure_set(v___f_3446_, 8, v___x_3444_);
lean_closure_set(v___f_3446_, 9, v___x_3429_);
lean_closure_set(v___f_3446_, 10, v___x_3445_);
lean_closure_set(v___f_3446_, 11, v___x_3431_);
v___x_3447_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3444_, v_arg_3432_, v___f_3446_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3448_ = _args[0];
lean_object* v_snd_3449_ = _args[1];
lean_object* v___x_3450_ = _args[2];
lean_object* v___x_3451_ = _args[3];
lean_object* v___x_3452_ = _args[4];
lean_object* v___x_3453_ = _args[5];
lean_object* v___x_3454_ = _args[6];
lean_object* v___x_3455_ = _args[7];
lean_object* v___x_3456_ = _args[8];
lean_object* v_arg_3457_ = _args[9];
lean_object* v_xs_3458_ = _args[10];
lean_object* v___y_3459_ = _args[11];
lean_object* v___y_3460_ = _args[12];
lean_object* v___y_3461_ = _args[13];
lean_object* v___y_3462_ = _args[14];
lean_object* v___y_3463_ = _args[15];
lean_object* v___y_3464_ = _args[16];
lean_object* v___y_3465_ = _args[17];
lean_object* v___y_3466_ = _args[18];
lean_object* v___y_3467_ = _args[19];
_start:
{
uint8_t v___x_93360__boxed_3468_; lean_object* v_res_3469_; 
v___x_93360__boxed_3468_ = lean_unbox(v___x_3455_);
v_res_3469_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3448_, v_snd_3449_, v___x_3450_, v___x_3451_, v___x_3452_, v___x_3453_, v___x_3454_, v___x_93360__boxed_3468_, v___x_3456_, v_arg_3457_, v_xs_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3470_, size_t v_sz_3471_, size_t v_i_3472_, lean_object* v_b_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_usize_dec_lt(v_i_3472_, v_sz_3471_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_b_3473_);
return v___x_3480_;
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_a_3481_ = lean_array_uget_borrowed(v_as_3470_, v_i_3472_);
v___x_3482_ = lean_box(1);
lean_inc(v_a_3481_);
v___x_3483_ = l_Lean_PrettyPrinter_delab(v_a_3481_, v___x_3482_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; size_t v___x_3486_; size_t v___x_3487_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref(v___x_3483_);
v___x_3485_ = lean_array_push(v_b_3473_, v_a_3484_);
v___x_3486_ = ((size_t)1ULL);
v___x_3487_ = lean_usize_add(v_i_3472_, v___x_3486_);
v_i_3472_ = v___x_3487_;
v_b_3473_ = v___x_3485_;
goto _start;
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec_ref(v_b_3473_);
v_a_3489_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3483_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3483_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3497_, lean_object* v_sz_3498_, lean_object* v_i_3499_, lean_object* v_b_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
size_t v_sz_boxed_3506_; size_t v_i_boxed_3507_; lean_object* v_res_3508_; 
v_sz_boxed_3506_ = lean_unbox_usize(v_sz_3498_);
lean_dec(v_sz_3498_);
v_i_boxed_3507_ = lean_unbox_usize(v_i_3499_);
lean_dec(v_i_3499_);
v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3497_, v_sz_boxed_3506_, v_i_boxed_3507_, v_b_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v_as_3497_);
return v_res_3508_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3517_ = l_String_toRawSubstring_x27(v___x_3516_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3528_ = l_String_toRawSubstring_x27(v___x_3527_);
return v___x_3528_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3533_ = l_String_toRawSubstring_x27(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3535_ = l_String_toRawSubstring_x27(v___x_3534_);
return v___x_3535_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3539_ = l_String_toRawSubstring_x27(v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3544_ = l_String_toRawSubstring_x27(v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3554_, lean_object* v___x_3555_, lean_object* v___f_3556_, lean_object* v_a_3557_, lean_object* v_inv_3558_, lean_object* v_arg_3559_, uint8_t v___x_3560_, lean_object* v___x_3561_, lean_object* v___x_3562_, lean_object* v___x_3563_, lean_object* v___x_3564_, lean_object* v___x_3565_, lean_object* v___x_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_a_3577_; lean_object* v___y_3581_; lean_object* v___x_3583_; 
lean_inc_ref(v___x_3555_);
lean_inc(v___x_3554_);
v___x_3583_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3554_, v___x_3555_, v___f_3556_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3585_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref(v___x_3583_);
v___x_3585_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3557_, v_inv_3558_, v_arg_3559_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref(v___x_3585_);
if (lean_obj_tag(v_a_3586_) == 1)
{
lean_object* v_val_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_4067_; 
lean_dec_ref(v_arg_3559_);
v_val_3587_ = lean_ctor_get(v_a_3586_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_a_3586_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_3589_ = v_a_3586_;
v_isShared_3590_ = v_isSharedCheck_4067_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_val_3587_);
lean_dec(v_a_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_4067_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
if (lean_obj_tag(v_a_3584_) == 1)
{
lean_object* v_val_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3990_; 
lean_del_object(v___x_3589_);
v_val_3591_ = lean_ctor_get(v_a_3584_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v_a_3584_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3593_ = v_a_3584_;
v_isShared_3594_ = v_isSharedCheck_3990_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_val_3591_);
lean_dec(v_a_3584_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3990_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v_snd_3595_; lean_object* v_fst_3596_; lean_object* v_snd_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3989_; 
v_snd_3595_ = lean_ctor_get(v_val_3591_, 1);
lean_inc(v_snd_3595_);
v_fst_3596_ = lean_ctor_get(v_val_3587_, 0);
v_snd_3597_ = lean_ctor_get(v_val_3587_, 1);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_val_3587_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3599_ = v_val_3587_;
v_isShared_3600_ = v_isSharedCheck_3989_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_snd_3597_);
lean_inc(v_fst_3596_);
lean_dec(v_val_3587_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3989_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v_fst_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3987_; 
v_fst_3601_ = lean_ctor_get(v_val_3591_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_val_3591_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; 
v_unused_3988_ = lean_ctor_get(v_val_3591_, 1);
lean_dec(v_unused_3988_);
v___x_3603_ = v_val_3591_;
v_isShared_3604_ = v_isSharedCheck_3987_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_fst_3601_);
lean_dec(v_val_3591_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3987_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_fst_3605_; lean_object* v_snd_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3986_; 
v_fst_3605_ = lean_ctor_get(v_snd_3595_, 0);
v_snd_3606_ = lean_ctor_get(v_snd_3595_, 1);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_snd_3595_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3608_ = v_snd_3595_;
v_isShared_3609_ = v_isSharedCheck_3986_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_snd_3606_);
lean_inc(v_fst_3605_);
lean_dec(v_snd_3595_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3986_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; 
v___x_3610_ = lean_box(v___x_3560_);
lean_inc(v___x_3562_);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3611_, 0, v_fst_3596_);
lean_closure_set(v___f_3611_, 1, v___x_3610_);
lean_closure_set(v___f_3611_, 2, v___x_3561_);
lean_closure_set(v___f_3611_, 3, v___x_3562_);
lean_closure_set(v___f_3611_, 4, v_fst_3601_);
lean_closure_set(v___f_3611_, 5, v_fst_3605_);
lean_closure_set(v___f_3611_, 6, v_snd_3597_);
lean_inc(v___x_3554_);
v___x_3612_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3554_, v___x_3555_, v___f_3611_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v_fst_3614_; lean_object* v_snd_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3977_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref(v___x_3612_);
v_fst_3614_ = lean_ctor_get(v_a_3613_, 0);
v_snd_3615_ = lean_ctor_get(v_a_3613_, 1);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_a_3613_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3617_ = v_a_3613_;
v_isShared_3618_ = v_isSharedCheck_3977_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_snd_3615_);
lean_inc(v_fst_3614_);
lean_dec(v_a_3613_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3977_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v_points_3619_; lean_object* v_default_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3976_; 
v_points_3619_ = lean_ctor_get(v_snd_3606_, 0);
v_default_3620_ = lean_ctor_get(v_snd_3606_, 1);
v_isSharedCheck_3976_ = !lean_is_exclusive(v_snd_3606_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3622_ = v_snd_3606_;
v_isShared_3623_ = v_isSharedCheck_3976_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_default_3620_);
lean_inc(v_points_3619_);
lean_dec(v_snd_3606_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3976_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3624_ = lean_array_get_size(v_points_3619_);
v___x_3625_ = lean_nat_dec_eq(v___x_3624_, v___x_3562_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; size_t v_sz_3627_; size_t v___x_3628_; lean_object* v___x_3629_; 
lean_del_object(v___x_3593_);
v___x_3626_ = lean_mk_empty_array_with_capacity(v___x_3562_);
lean_dec(v___x_3562_);
v_sz_3627_ = lean_array_size(v_points_3619_);
v___x_3628_ = ((size_t)0ULL);
v___x_3629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3619_, v_sz_3627_, v___x_3628_, v___x_3626_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec_ref(v_points_3619_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3631_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3629_);
v___x_3631_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3630_, v_default_3620_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v_a_3630_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3714_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3714_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3714_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v_ref_3636_; lean_object* v_quotContext_3637_; lean_object* v_currMacroScope_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v_ref_3636_ = lean_ctor_get(v___y_3573_, 5);
lean_inc(v_ref_3636_);
v_quotContext_3637_ = lean_ctor_get(v___y_3573_, 10);
lean_inc_n(v_quotContext_3637_, 2);
v_currMacroScope_3638_ = lean_ctor_get(v___y_3573_, 11);
lean_inc_n(v_currMacroScope_3638_, 2);
lean_dec_ref(v___y_3573_);
v___x_3639_ = l_Lean_SourceInfo_fromRef(v_ref_3636_, v___x_3625_);
lean_dec(v_ref_3636_);
v___x_3640_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3641_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3642_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3563_);
v___x_3643_ = l_Lean_Name_mkStr2(v___x_3563_, v___x_3642_);
v___x_3644_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3643_, v_currMacroScope_3638_);
v___x_3645_ = l_Lean_Name_mkStr4(v___x_3564_, v___x_3565_, v___x_3563_, v___x_3642_);
v___x_3646_ = lean_box(0);
lean_inc(v___x_3645_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 1);
lean_ctor_set(v___x_3622_, 1, v___x_3646_);
lean_ctor_set(v___x_3622_, 0, v___x_3645_);
v___x_3648_ = v___x_3622_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3650_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3645_);
v___x_3650_ = v___x_3634_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3645_);
v___x_3650_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3652_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 1);
lean_ctor_set(v___x_3617_, 1, v___x_3646_);
lean_ctor_set(v___x_3617_, 0, v___x_3650_);
v___x_3652_ = v___x_3617_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v___x_3646_);
v___x_3652_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3654_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 1);
lean_ctor_set(v___x_3608_, 1, v___x_3652_);
lean_ctor_set(v___x_3608_, 0, v___x_3648_);
v___x_3654_ = v___x_3608_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_inc_n(v___x_3639_, 2);
v___x_3655_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3639_);
lean_ctor_set(v___x_3655_, 1, v___x_3641_);
lean_ctor_set(v___x_3655_, 2, v___x_3644_);
lean_ctor_set(v___x_3655_, 3, v___x_3654_);
v___x_3656_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3658_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 2);
lean_ctor_set(v___x_3603_, 1, v___x_3658_);
lean_ctor_set(v___x_3603_, 0, v___x_3639_);
v___x_3660_ = v___x_3603_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3661_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3662_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3638_);
lean_inc(v_quotContext_3637_);
v___x_3663_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3662_, v_currMacroScope_3638_);
lean_inc_n(v___x_3639_, 2);
v___x_3664_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3639_);
lean_ctor_set(v___x_3664_, 1, v___x_3661_);
lean_ctor_set(v___x_3664_, 2, v___x_3663_);
lean_ctor_set(v___x_3664_, 3, v___x_3646_);
v___x_3665_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 2);
lean_ctor_set(v___x_3599_, 1, v___x_3665_);
lean_ctor_set(v___x_3599_, 0, v___x_3639_);
v___x_3667_ = v___x_3599_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3668_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3669_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3639_, 19);
v___x_3670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3639_);
lean_ctor_set(v___x_3670_, 1, v___x_3668_);
v___x_3671_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3672_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3673_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3638_, 4);
lean_inc_n(v_quotContext_3637_, 4);
v___x_3674_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3673_, v_currMacroScope_3638_);
v___x_3675_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3639_);
lean_ctor_set(v___x_3675_, 1, v___x_3672_);
lean_ctor_set(v___x_3675_, 2, v___x_3674_);
lean_ctor_set(v___x_3675_, 3, v___x_3646_);
v___x_3676_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3678_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3677_, v_currMacroScope_3638_);
v___x_3679_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3639_);
lean_ctor_set(v___x_3679_, 1, v___x_3676_);
lean_ctor_set(v___x_3679_, 2, v___x_3678_);
lean_ctor_set(v___x_3679_, 3, v___x_3646_);
lean_inc_ref(v___x_3679_);
v___x_3680_ = l_Lean_Syntax_node2(v___x_3639_, v___x_3656_, v___x_3675_, v___x_3679_);
v___x_3681_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3639_);
lean_ctor_set(v___x_3682_, 1, v___x_3656_);
lean_ctor_set(v___x_3682_, 2, v___x_3681_);
v___x_3683_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3639_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
lean_inc_ref(v___x_3684_);
lean_inc_ref(v___x_3682_);
v___x_3685_ = l_Lean_Syntax_node4(v___x_3639_, v___x_3671_, v___x_3680_, v___x_3682_, v___x_3684_, v_snd_3615_);
lean_inc_ref(v___x_3670_);
v___x_3686_ = l_Lean_Syntax_node2(v___x_3639_, v___x_3669_, v___x_3670_, v___x_3685_);
v___x_3687_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3639_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
lean_inc_ref_n(v___x_3688_, 2);
lean_inc_ref_n(v___x_3667_, 2);
lean_inc_ref_n(v___x_3660_, 2);
v___x_3689_ = l_Lean_Syntax_node5(v___x_3639_, v___x_3657_, v___x_3660_, v___x_3664_, v___x_3667_, v___x_3686_, v___x_3688_);
v___x_3690_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3692_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3691_, v_currMacroScope_3638_);
v___x_3693_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3639_);
lean_ctor_set(v___x_3693_, 1, v___x_3690_);
lean_ctor_set(v___x_3693_, 2, v___x_3692_);
lean_ctor_set(v___x_3693_, 3, v___x_3646_);
v___x_3694_ = l_String_toRawSubstring_x27(v___x_3566_);
v___x_3695_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3554_, v_currMacroScope_3638_);
v___x_3696_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3639_);
lean_ctor_set(v___x_3696_, 1, v___x_3694_);
lean_ctor_set(v___x_3696_, 2, v___x_3695_);
lean_ctor_set(v___x_3696_, 3, v___x_3646_);
v___x_3697_ = l_Lean_Syntax_node2(v___x_3639_, v___x_3656_, v___x_3696_, v___x_3679_);
v___x_3698_ = l_Lean_Syntax_node4(v___x_3639_, v___x_3671_, v___x_3697_, v___x_3682_, v___x_3684_, v_fst_3614_);
v___x_3699_ = l_Lean_Syntax_node2(v___x_3639_, v___x_3669_, v___x_3670_, v___x_3698_);
v___x_3700_ = l_Lean_Syntax_node5(v___x_3639_, v___x_3657_, v___x_3660_, v___x_3693_, v___x_3667_, v___x_3699_, v___x_3688_);
v___x_3701_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3702_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3703_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3702_, v_currMacroScope_3638_);
v___x_3704_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3639_);
lean_ctor_set(v___x_3704_, 1, v___x_3701_);
lean_ctor_set(v___x_3704_, 2, v___x_3703_);
lean_ctor_set(v___x_3704_, 3, v___x_3646_);
v___x_3705_ = l_Lean_Syntax_node5(v___x_3639_, v___x_3657_, v___x_3660_, v___x_3704_, v___x_3667_, v_a_3632_, v___x_3688_);
v___x_3706_ = l_Lean_Syntax_node3(v___x_3639_, v___x_3656_, v___x_3689_, v___x_3700_, v___x_3705_);
v___x_3707_ = l_Lean_Syntax_node2(v___x_3639_, v___x_3640_, v___x_3655_, v___x_3706_);
v_a_3577_ = v___x_3707_;
goto v___jp_3576_;
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
lean_del_object(v___x_3622_);
lean_del_object(v___x_3617_);
lean_dec(v_snd_3615_);
lean_dec(v_fst_3614_);
lean_del_object(v___x_3608_);
lean_del_object(v___x_3603_);
lean_del_object(v___x_3599_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___x_3566_);
lean_dec_ref(v___x_3565_);
lean_dec_ref(v___x_3564_);
lean_dec_ref(v___x_3563_);
lean_dec(v___x_3554_);
v___y_3581_ = v___x_3631_;
goto v___jp_3580_;
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_del_object(v___x_3622_);
lean_dec(v_default_3620_);
lean_del_object(v___x_3617_);
lean_dec(v_snd_3615_);
lean_dec(v_fst_3614_);
lean_del_object(v___x_3608_);
lean_del_object(v___x_3603_);
lean_del_object(v___x_3599_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___x_3566_);
lean_dec_ref(v___x_3565_);
lean_dec_ref(v___x_3564_);
lean_dec_ref(v___x_3563_);
lean_dec(v___x_3554_);
v_a_3715_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3629_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3629_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
lean_dec_ref(v_points_3619_);
lean_dec(v___x_3562_);
switch(lean_obj_tag(v_default_3620_))
{
case 2:
{
lean_object* v_ref_3723_; lean_object* v_quotContext_3724_; lean_object* v_currMacroScope_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3736_; 
v_ref_3723_ = lean_ctor_get(v___y_3573_, 5);
lean_inc(v_ref_3723_);
v_quotContext_3724_ = lean_ctor_get(v___y_3573_, 10);
lean_inc_n(v_quotContext_3724_, 2);
v_currMacroScope_3725_ = lean_ctor_get(v___y_3573_, 11);
lean_inc_n(v_currMacroScope_3725_, 2);
lean_dec_ref(v___y_3573_);
v___x_3726_ = 0;
v___x_3727_ = l_Lean_SourceInfo_fromRef(v_ref_3723_, v___x_3726_);
lean_dec(v_ref_3723_);
v___x_3728_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3729_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3730_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3563_);
v___x_3731_ = l_Lean_Name_mkStr2(v___x_3563_, v___x_3730_);
v___x_3732_ = l_Lean_addMacroScope(v_quotContext_3724_, v___x_3731_, v_currMacroScope_3725_);
lean_inc_ref(v___x_3565_);
lean_inc_ref(v___x_3564_);
v___x_3733_ = l_Lean_Name_mkStr4(v___x_3564_, v___x_3565_, v___x_3563_, v___x_3730_);
v___x_3734_ = lean_box(0);
lean_inc(v___x_3733_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 1);
lean_ctor_set(v___x_3622_, 1, v___x_3734_);
lean_ctor_set(v___x_3622_, 0, v___x_3733_);
v___x_3736_ = v___x_3622_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3738_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set_tag(v___x_3593_, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3733_);
v___x_3738_ = v___x_3593_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3733_);
v___x_3738_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3740_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 1);
lean_ctor_set(v___x_3617_, 1, v___x_3734_);
lean_ctor_set(v___x_3617_, 0, v___x_3738_);
v___x_3740_ = v___x_3617_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v___x_3734_);
v___x_3740_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3742_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 1);
lean_ctor_set(v___x_3608_, 1, v___x_3740_);
lean_ctor_set(v___x_3608_, 0, v___x_3736_);
v___x_3742_ = v___x_3608_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3748_; 
lean_inc_n(v___x_3727_, 2);
v___x_3743_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3727_);
lean_ctor_set(v___x_3743_, 1, v___x_3729_);
lean_ctor_set(v___x_3743_, 2, v___x_3732_);
lean_ctor_set(v___x_3743_, 3, v___x_3742_);
v___x_3744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3745_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 2);
lean_ctor_set(v___x_3603_, 1, v___x_3746_);
lean_ctor_set(v___x_3603_, 0, v___x_3727_);
v___x_3748_ = v___x_3603_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3749_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3750_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3725_);
lean_inc(v_quotContext_3724_);
v___x_3751_ = l_Lean_addMacroScope(v_quotContext_3724_, v___x_3750_, v_currMacroScope_3725_);
lean_inc_n(v___x_3727_, 2);
v___x_3752_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3727_);
lean_ctor_set(v___x_3752_, 1, v___x_3749_);
lean_ctor_set(v___x_3752_, 2, v___x_3751_);
lean_ctor_set(v___x_3752_, 3, v___x_3734_);
v___x_3753_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 2);
lean_ctor_set(v___x_3599_, 1, v___x_3753_);
lean_ctor_set(v___x_3599_, 0, v___x_3727_);
v___x_3755_ = v___x_3599_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3756_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3757_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3727_, 22);
v___x_3758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3727_);
lean_ctor_set(v___x_3758_, 1, v___x_3756_);
v___x_3759_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3760_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3761_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3725_, 5);
lean_inc_n(v_quotContext_3724_, 5);
v___x_3762_ = l_Lean_addMacroScope(v_quotContext_3724_, v___x_3761_, v_currMacroScope_3725_);
v___x_3763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3727_);
lean_ctor_set(v___x_3763_, 1, v___x_3760_);
lean_ctor_set(v___x_3763_, 2, v___x_3762_);
lean_ctor_set(v___x_3763_, 3, v___x_3734_);
v___x_3764_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3765_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3766_ = l_Lean_addMacroScope(v_quotContext_3724_, v___x_3765_, v_currMacroScope_3725_);
v___x_3767_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3727_);
lean_ctor_set(v___x_3767_, 1, v___x_3764_);
lean_ctor_set(v___x_3767_, 2, v___x_3766_);
lean_ctor_set(v___x_3767_, 3, v___x_3734_);
lean_inc_ref(v___x_3767_);
v___x_3768_ = l_Lean_Syntax_node2(v___x_3727_, v___x_3744_, v___x_3763_, v___x_3767_);
v___x_3769_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3727_);
lean_ctor_set(v___x_3770_, 1, v___x_3744_);
lean_ctor_set(v___x_3770_, 2, v___x_3769_);
v___x_3771_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3727_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
lean_inc_ref(v___x_3772_);
lean_inc_ref(v___x_3770_);
v___x_3773_ = l_Lean_Syntax_node4(v___x_3727_, v___x_3759_, v___x_3768_, v___x_3770_, v___x_3772_, v_snd_3615_);
lean_inc_ref(v___x_3758_);
v___x_3774_ = l_Lean_Syntax_node2(v___x_3727_, v___x_3757_, v___x_3758_, v___x_3773_);
v___x_3775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3727_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
lean_inc_ref_n(v___x_3776_, 2);
lean_inc_ref_n(v___x_3755_, 2);
lean_inc_ref_n(v___x_3748_, 2);
v___x_3777_ = l_Lean_Syntax_node5(v___x_3727_, v___x_3745_, v___x_3748_, v___x_3752_, v___x_3755_, v___x_3774_, v___x_3776_);
v___x_3778_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3779_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3780_ = l_Lean_addMacroScope(v_quotContext_3724_, v___x_3779_, v_currMacroScope_3725_);
v___x_3781_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3727_);
lean_ctor_set(v___x_3781_, 1, v___x_3778_);
lean_ctor_set(v___x_3781_, 2, v___x_3780_);
lean_ctor_set(v___x_3781_, 3, v___x_3734_);
v___x_3782_ = l_String_toRawSubstring_x27(v___x_3566_);
v___x_3783_ = l_Lean_addMacroScope(v_quotContext_3724_, v___x_3554_, v_currMacroScope_3725_);
v___x_3784_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3727_);
lean_ctor_set(v___x_3784_, 1, v___x_3782_);
lean_ctor_set(v___x_3784_, 2, v___x_3783_);
lean_ctor_set(v___x_3784_, 3, v___x_3734_);
v___x_3785_ = l_Lean_Syntax_node2(v___x_3727_, v___x_3744_, v___x_3784_, v___x_3767_);
v___x_3786_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3787_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3788_ = l_Lean_addMacroScope(v_quotContext_3724_, v___x_3787_, v_currMacroScope_3725_);
v___x_3789_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3727_);
lean_ctor_set(v___x_3789_, 1, v___x_3786_);
lean_ctor_set(v___x_3789_, 2, v___x_3788_);
lean_ctor_set(v___x_3789_, 3, v___x_3734_);
v___x_3790_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3794_ = l_Lean_addMacroScope(v_quotContext_3724_, v___x_3793_, v_currMacroScope_3725_);
v___x_3795_ = l_Lean_Name_mkStr4(v___x_3564_, v___x_3565_, v___x_3791_, v___x_3792_);
v___x_3796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v___x_3734_);
v___x_3797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
lean_ctor_set(v___x_3797_, 1, v___x_3734_);
v___x_3798_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3727_);
lean_ctor_set(v___x_3798_, 1, v___x_3790_);
lean_ctor_set(v___x_3798_, 2, v___x_3794_);
lean_ctor_set(v___x_3798_, 3, v___x_3797_);
v___x_3799_ = l_Lean_Syntax_node5(v___x_3727_, v___x_3745_, v___x_3748_, v___x_3789_, v___x_3755_, v___x_3798_, v___x_3776_);
v___x_3800_ = l_Lean_Syntax_node1(v___x_3727_, v___x_3744_, v___x_3799_);
v___x_3801_ = l_Lean_Syntax_node2(v___x_3727_, v___x_3728_, v_fst_3614_, v___x_3800_);
v___x_3802_ = l_Lean_Syntax_node4(v___x_3727_, v___x_3759_, v___x_3785_, v___x_3770_, v___x_3772_, v___x_3801_);
v___x_3803_ = l_Lean_Syntax_node2(v___x_3727_, v___x_3757_, v___x_3758_, v___x_3802_);
v___x_3804_ = l_Lean_Syntax_node5(v___x_3727_, v___x_3745_, v___x_3748_, v___x_3781_, v___x_3755_, v___x_3803_, v___x_3776_);
v___x_3805_ = l_Lean_Syntax_node2(v___x_3727_, v___x_3744_, v___x_3777_, v___x_3804_);
v___x_3806_ = l_Lean_Syntax_node2(v___x_3727_, v___x_3728_, v___x_3743_, v___x_3805_);
v_a_3577_ = v___x_3806_;
goto v___jp_3576_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
lean_del_object(v___x_3593_);
v_e_3813_ = lean_ctor_get(v_default_3620_, 0);
lean_inc_ref(v_e_3813_);
lean_dec_ref(v_default_3620_);
v___x_3814_ = lean_box(1);
v___x_3815_ = l_Lean_PrettyPrinter_delab(v_e_3813_, v___x_3814_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3901_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3901_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3901_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v_ref_3820_; lean_object* v_quotContext_3821_; lean_object* v_currMacroScope_3822_; uint8_t v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v_ref_3820_ = lean_ctor_get(v___y_3573_, 5);
lean_inc(v_ref_3820_);
v_quotContext_3821_ = lean_ctor_get(v___y_3573_, 10);
lean_inc_n(v_quotContext_3821_, 2);
v_currMacroScope_3822_ = lean_ctor_get(v___y_3573_, 11);
lean_inc_n(v_currMacroScope_3822_, 2);
lean_dec_ref(v___y_3573_);
v___x_3823_ = 0;
v___x_3824_ = l_Lean_SourceInfo_fromRef(v_ref_3820_, v___x_3823_);
lean_dec(v_ref_3820_);
v___x_3825_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3826_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3827_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3563_);
v___x_3828_ = l_Lean_Name_mkStr2(v___x_3563_, v___x_3827_);
v___x_3829_ = l_Lean_addMacroScope(v_quotContext_3821_, v___x_3828_, v_currMacroScope_3822_);
v___x_3830_ = l_Lean_Name_mkStr4(v___x_3564_, v___x_3565_, v___x_3563_, v___x_3827_);
v___x_3831_ = lean_box(0);
lean_inc(v___x_3830_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 1);
lean_ctor_set(v___x_3622_, 1, v___x_3831_);
lean_ctor_set(v___x_3622_, 0, v___x_3830_);
v___x_3833_ = v___x_3622_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3835_; 
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3830_);
v___x_3835_ = v___x_3818_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3830_);
v___x_3835_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3837_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 1);
lean_ctor_set(v___x_3617_, 1, v___x_3831_);
lean_ctor_set(v___x_3617_, 0, v___x_3835_);
v___x_3837_ = v___x_3617_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v___x_3831_);
v___x_3837_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3839_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 1);
lean_ctor_set(v___x_3608_, 1, v___x_3837_);
lean_ctor_set(v___x_3608_, 0, v___x_3833_);
v___x_3839_ = v___x_3608_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_inc_n(v___x_3824_, 2);
v___x_3840_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3824_);
lean_ctor_set(v___x_3840_, 1, v___x_3826_);
lean_ctor_set(v___x_3840_, 2, v___x_3829_);
lean_ctor_set(v___x_3840_, 3, v___x_3839_);
v___x_3841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3842_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3843_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 2);
lean_ctor_set(v___x_3603_, 1, v___x_3843_);
lean_ctor_set(v___x_3603_, 0, v___x_3824_);
v___x_3845_ = v___x_3603_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3846_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3847_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3822_);
lean_inc(v_quotContext_3821_);
v___x_3848_ = l_Lean_addMacroScope(v_quotContext_3821_, v___x_3847_, v_currMacroScope_3822_);
lean_inc_n(v___x_3824_, 2);
v___x_3849_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3824_);
lean_ctor_set(v___x_3849_, 1, v___x_3846_);
lean_ctor_set(v___x_3849_, 2, v___x_3848_);
lean_ctor_set(v___x_3849_, 3, v___x_3831_);
v___x_3850_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 2);
lean_ctor_set(v___x_3599_, 1, v___x_3850_);
lean_ctor_set(v___x_3599_, 0, v___x_3824_);
v___x_3852_ = v___x_3599_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3853_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3854_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3824_, 21);
v___x_3855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3824_);
lean_ctor_set(v___x_3855_, 1, v___x_3853_);
v___x_3856_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3857_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3858_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3822_, 4);
lean_inc_n(v_quotContext_3821_, 4);
v___x_3859_ = l_Lean_addMacroScope(v_quotContext_3821_, v___x_3858_, v_currMacroScope_3822_);
v___x_3860_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3824_);
lean_ctor_set(v___x_3860_, 1, v___x_3857_);
lean_ctor_set(v___x_3860_, 2, v___x_3859_);
lean_ctor_set(v___x_3860_, 3, v___x_3831_);
v___x_3861_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3862_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3863_ = l_Lean_addMacroScope(v_quotContext_3821_, v___x_3862_, v_currMacroScope_3822_);
v___x_3864_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3824_);
lean_ctor_set(v___x_3864_, 1, v___x_3861_);
lean_ctor_set(v___x_3864_, 2, v___x_3863_);
lean_ctor_set(v___x_3864_, 3, v___x_3831_);
lean_inc_ref(v___x_3864_);
v___x_3865_ = l_Lean_Syntax_node2(v___x_3824_, v___x_3841_, v___x_3860_, v___x_3864_);
v___x_3866_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3824_);
lean_ctor_set(v___x_3867_, 1, v___x_3841_);
lean_ctor_set(v___x_3867_, 2, v___x_3866_);
v___x_3868_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3824_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
lean_inc_ref(v___x_3869_);
lean_inc_ref(v___x_3867_);
v___x_3870_ = l_Lean_Syntax_node4(v___x_3824_, v___x_3856_, v___x_3865_, v___x_3867_, v___x_3869_, v_snd_3615_);
lean_inc_ref(v___x_3855_);
v___x_3871_ = l_Lean_Syntax_node2(v___x_3824_, v___x_3854_, v___x_3855_, v___x_3870_);
v___x_3872_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3824_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
lean_inc_ref_n(v___x_3873_, 2);
lean_inc_ref_n(v___x_3852_, 2);
lean_inc_ref_n(v___x_3845_, 2);
v___x_3874_ = l_Lean_Syntax_node5(v___x_3824_, v___x_3842_, v___x_3845_, v___x_3849_, v___x_3852_, v___x_3871_, v___x_3873_);
v___x_3875_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3876_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3877_ = l_Lean_addMacroScope(v_quotContext_3821_, v___x_3876_, v_currMacroScope_3822_);
v___x_3878_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3824_);
lean_ctor_set(v___x_3878_, 1, v___x_3875_);
lean_ctor_set(v___x_3878_, 2, v___x_3877_);
lean_ctor_set(v___x_3878_, 3, v___x_3831_);
v___x_3879_ = l_String_toRawSubstring_x27(v___x_3566_);
v___x_3880_ = l_Lean_addMacroScope(v_quotContext_3821_, v___x_3554_, v_currMacroScope_3822_);
v___x_3881_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3824_);
lean_ctor_set(v___x_3881_, 1, v___x_3879_);
lean_ctor_set(v___x_3881_, 2, v___x_3880_);
lean_ctor_set(v___x_3881_, 3, v___x_3831_);
v___x_3882_ = l_Lean_Syntax_node2(v___x_3824_, v___x_3841_, v___x_3881_, v___x_3864_);
v___x_3883_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3884_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3885_ = l_Lean_addMacroScope(v_quotContext_3821_, v___x_3884_, v_currMacroScope_3822_);
v___x_3886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3824_);
lean_ctor_set(v___x_3886_, 1, v___x_3883_);
lean_ctor_set(v___x_3886_, 2, v___x_3885_);
lean_ctor_set(v___x_3886_, 3, v___x_3831_);
v___x_3887_ = l_Lean_Syntax_node5(v___x_3824_, v___x_3842_, v___x_3845_, v___x_3886_, v___x_3852_, v_a_3816_, v___x_3873_);
v___x_3888_ = l_Lean_Syntax_node1(v___x_3824_, v___x_3841_, v___x_3887_);
v___x_3889_ = l_Lean_Syntax_node2(v___x_3824_, v___x_3825_, v_fst_3614_, v___x_3888_);
v___x_3890_ = l_Lean_Syntax_node4(v___x_3824_, v___x_3856_, v___x_3882_, v___x_3867_, v___x_3869_, v___x_3889_);
v___x_3891_ = l_Lean_Syntax_node2(v___x_3824_, v___x_3854_, v___x_3855_, v___x_3890_);
v___x_3892_ = l_Lean_Syntax_node5(v___x_3824_, v___x_3842_, v___x_3845_, v___x_3878_, v___x_3852_, v___x_3891_, v___x_3873_);
v___x_3893_ = l_Lean_Syntax_node2(v___x_3824_, v___x_3841_, v___x_3874_, v___x_3892_);
v___x_3894_ = l_Lean_Syntax_node2(v___x_3824_, v___x_3825_, v___x_3840_, v___x_3893_);
v_a_3577_ = v___x_3894_;
goto v___jp_3576_;
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
lean_del_object(v___x_3622_);
lean_del_object(v___x_3617_);
lean_dec(v_snd_3615_);
lean_dec(v_fst_3614_);
lean_del_object(v___x_3608_);
lean_del_object(v___x_3603_);
lean_del_object(v___x_3599_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___x_3566_);
lean_dec_ref(v___x_3565_);
lean_dec_ref(v___x_3564_);
lean_dec_ref(v___x_3563_);
lean_dec(v___x_3554_);
v___y_3581_ = v___x_3815_;
goto v___jp_3580_;
}
}
default: 
{
lean_object* v_ref_3902_; lean_object* v_quotContext_3903_; lean_object* v_currMacroScope_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec(v_default_3620_);
v_ref_3902_ = lean_ctor_get(v___y_3573_, 5);
lean_inc(v_ref_3902_);
v_quotContext_3903_ = lean_ctor_get(v___y_3573_, 10);
lean_inc_n(v_quotContext_3903_, 2);
v_currMacroScope_3904_ = lean_ctor_get(v___y_3573_, 11);
lean_inc_n(v_currMacroScope_3904_, 2);
lean_dec_ref(v___y_3573_);
v___x_3905_ = 0;
v___x_3906_ = l_Lean_SourceInfo_fromRef(v_ref_3902_, v___x_3905_);
lean_dec(v_ref_3902_);
v___x_3907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3908_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3909_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3563_);
v___x_3910_ = l_Lean_Name_mkStr2(v___x_3563_, v___x_3909_);
v___x_3911_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3910_, v_currMacroScope_3904_);
v___x_3912_ = l_Lean_Name_mkStr4(v___x_3564_, v___x_3565_, v___x_3563_, v___x_3909_);
v___x_3913_ = lean_box(0);
lean_inc(v___x_3912_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 1);
lean_ctor_set(v___x_3622_, 1, v___x_3913_);
lean_ctor_set(v___x_3622_, 0, v___x_3912_);
v___x_3915_ = v___x_3622_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3912_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set_tag(v___x_3593_, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3912_);
v___x_3917_ = v___x_3593_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3912_);
v___x_3917_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3919_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 1);
lean_ctor_set(v___x_3617_, 1, v___x_3913_);
lean_ctor_set(v___x_3617_, 0, v___x_3917_);
v___x_3919_ = v___x_3617_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v___x_3913_);
v___x_3919_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3921_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 1);
lean_ctor_set(v___x_3608_, 1, v___x_3919_);
lean_ctor_set(v___x_3608_, 0, v___x_3915_);
v___x_3921_ = v___x_3608_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3927_; 
lean_inc_n(v___x_3906_, 2);
v___x_3922_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3906_);
lean_ctor_set(v___x_3922_, 1, v___x_3908_);
lean_ctor_set(v___x_3922_, 2, v___x_3911_);
lean_ctor_set(v___x_3922_, 3, v___x_3921_);
v___x_3923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3924_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3925_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 2);
lean_ctor_set(v___x_3603_, 1, v___x_3925_);
lean_ctor_set(v___x_3603_, 0, v___x_3906_);
v___x_3927_ = v___x_3603_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3928_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3904_);
lean_inc(v_quotContext_3903_);
v___x_3930_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3929_, v_currMacroScope_3904_);
lean_inc_n(v___x_3906_, 2);
v___x_3931_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3906_);
lean_ctor_set(v___x_3931_, 1, v___x_3928_);
lean_ctor_set(v___x_3931_, 2, v___x_3930_);
lean_ctor_set(v___x_3931_, 3, v___x_3913_);
v___x_3932_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 2);
lean_ctor_set(v___x_3599_, 1, v___x_3932_);
lean_ctor_set(v___x_3599_, 0, v___x_3906_);
v___x_3934_ = v___x_3599_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3935_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3936_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3906_, 17);
v___x_3937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3906_);
lean_ctor_set(v___x_3937_, 1, v___x_3935_);
v___x_3938_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3939_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3940_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3904_, 3);
lean_inc_n(v_quotContext_3903_, 3);
v___x_3941_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3940_, v_currMacroScope_3904_);
v___x_3942_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3906_);
lean_ctor_set(v___x_3942_, 1, v___x_3939_);
lean_ctor_set(v___x_3942_, 2, v___x_3941_);
lean_ctor_set(v___x_3942_, 3, v___x_3913_);
v___x_3943_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3945_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3944_, v_currMacroScope_3904_);
v___x_3946_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3906_);
lean_ctor_set(v___x_3946_, 1, v___x_3943_);
lean_ctor_set(v___x_3946_, 2, v___x_3945_);
lean_ctor_set(v___x_3946_, 3, v___x_3913_);
lean_inc_ref(v___x_3946_);
v___x_3947_ = l_Lean_Syntax_node2(v___x_3906_, v___x_3923_, v___x_3942_, v___x_3946_);
v___x_3948_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3906_);
lean_ctor_set(v___x_3949_, 1, v___x_3923_);
lean_ctor_set(v___x_3949_, 2, v___x_3948_);
v___x_3950_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3906_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
lean_inc_ref(v___x_3951_);
lean_inc_ref(v___x_3949_);
v___x_3952_ = l_Lean_Syntax_node4(v___x_3906_, v___x_3938_, v___x_3947_, v___x_3949_, v___x_3951_, v_snd_3615_);
lean_inc_ref(v___x_3937_);
v___x_3953_ = l_Lean_Syntax_node2(v___x_3906_, v___x_3936_, v___x_3937_, v___x_3952_);
v___x_3954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3906_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
lean_inc_ref(v___x_3955_);
lean_inc_ref(v___x_3934_);
lean_inc_ref(v___x_3927_);
v___x_3956_ = l_Lean_Syntax_node5(v___x_3906_, v___x_3924_, v___x_3927_, v___x_3931_, v___x_3934_, v___x_3953_, v___x_3955_);
v___x_3957_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3958_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3959_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3958_, v_currMacroScope_3904_);
v___x_3960_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3906_);
lean_ctor_set(v___x_3960_, 1, v___x_3957_);
lean_ctor_set(v___x_3960_, 2, v___x_3959_);
lean_ctor_set(v___x_3960_, 3, v___x_3913_);
v___x_3961_ = l_String_toRawSubstring_x27(v___x_3566_);
v___x_3962_ = l_Lean_addMacroScope(v_quotContext_3903_, v___x_3554_, v_currMacroScope_3904_);
v___x_3963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3906_);
lean_ctor_set(v___x_3963_, 1, v___x_3961_);
lean_ctor_set(v___x_3963_, 2, v___x_3962_);
lean_ctor_set(v___x_3963_, 3, v___x_3913_);
v___x_3964_ = l_Lean_Syntax_node2(v___x_3906_, v___x_3923_, v___x_3963_, v___x_3946_);
v___x_3965_ = l_Lean_Syntax_node4(v___x_3906_, v___x_3938_, v___x_3964_, v___x_3949_, v___x_3951_, v_fst_3614_);
v___x_3966_ = l_Lean_Syntax_node2(v___x_3906_, v___x_3936_, v___x_3937_, v___x_3965_);
v___x_3967_ = l_Lean_Syntax_node5(v___x_3906_, v___x_3924_, v___x_3927_, v___x_3960_, v___x_3934_, v___x_3966_, v___x_3955_);
v___x_3968_ = l_Lean_Syntax_node2(v___x_3906_, v___x_3923_, v___x_3956_, v___x_3967_);
v___x_3969_ = l_Lean_Syntax_node2(v___x_3906_, v___x_3907_, v___x_3922_, v___x_3968_);
v_a_3577_ = v___x_3969_;
goto v___jp_3576_;
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
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_del_object(v___x_3608_);
lean_dec(v_snd_3606_);
lean_del_object(v___x_3603_);
lean_del_object(v___x_3599_);
lean_del_object(v___x_3593_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___x_3566_);
lean_dec_ref(v___x_3565_);
lean_dec_ref(v___x_3564_);
lean_dec_ref(v___x_3563_);
lean_dec(v___x_3562_);
lean_dec(v___x_3554_);
v_a_3978_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3612_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3612_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
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
lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_a_3584_);
lean_dec(v___x_3562_);
lean_dec(v___x_3561_);
lean_dec_ref(v___x_3555_);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_val_3587_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; lean_object* v_unused_4066_; 
v_unused_4065_ = lean_ctor_get(v_val_3587_, 1);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_val_3587_, 0);
lean_dec(v_unused_4066_);
v___x_3992_ = v_val_3587_;
v_isShared_3993_ = v_isSharedCheck_4064_;
goto v_resetjp_3991_;
}
else
{
lean_dec(v_val_3587_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4064_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v_ref_3994_; lean_object* v_quotContext_3995_; lean_object* v_currMacroScope_3996_; uint8_t v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4007_; 
v_ref_3994_ = lean_ctor_get(v___y_3573_, 5);
lean_inc(v_ref_3994_);
v_quotContext_3995_ = lean_ctor_get(v___y_3573_, 10);
lean_inc_n(v_quotContext_3995_, 2);
v_currMacroScope_3996_ = lean_ctor_get(v___y_3573_, 11);
lean_inc_n(v_currMacroScope_3996_, 2);
lean_dec_ref(v___y_3573_);
v___x_3997_ = 0;
v___x_3998_ = l_Lean_SourceInfo_fromRef(v_ref_3994_, v___x_3997_);
lean_dec(v_ref_3994_);
v___x_3999_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4000_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4001_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3563_);
v___x_4002_ = l_Lean_Name_mkStr2(v___x_3563_, v___x_4001_);
v___x_4003_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4002_, v_currMacroScope_3996_);
v___x_4004_ = l_Lean_Name_mkStr4(v___x_3564_, v___x_3565_, v___x_3563_, v___x_4001_);
v___x_4005_ = lean_box(0);
lean_inc(v___x_4004_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set_tag(v___x_3992_, 1);
lean_ctor_set(v___x_3992_, 1, v___x_4005_);
lean_ctor_set(v___x_3992_, 0, v___x_4004_);
v___x_4007_ = v___x_3992_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___x_4005_);
v___x_4007_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4009_; 
if (v_isShared_3590_ == 0)
{
lean_ctor_set_tag(v___x_3589_, 0);
lean_ctor_set(v___x_3589_, 0, v___x_4004_);
v___x_4009_ = v___x_3589_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4004_);
v___x_4009_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
lean_ctor_set(v___x_4010_, 1, v___x_4005_);
v___x_4011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4007_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
lean_inc_n(v___x_3998_, 23);
v___x_4012_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4012_, 0, v___x_3998_);
lean_ctor_set(v___x_4012_, 1, v___x_4000_);
lean_ctor_set(v___x_4012_, 2, v___x_4003_);
lean_ctor_set(v___x_4012_, 3, v___x_4011_);
v___x_4013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4014_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4015_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_4016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_3998_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
v___x_4017_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4018_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_3996_, 4);
lean_inc_n(v_quotContext_3995_, 4);
v___x_4019_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4018_, v_currMacroScope_3996_);
v___x_4020_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4020_, 0, v___x_3998_);
lean_ctor_set(v___x_4020_, 1, v___x_4017_);
lean_ctor_set(v___x_4020_, 2, v___x_4019_);
lean_ctor_set(v___x_4020_, 3, v___x_4005_);
v___x_4021_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_4022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4022_, 0, v___x_3998_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
v___x_4023_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4024_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
v___x_4025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_3998_);
lean_ctor_set(v___x_4025_, 1, v___x_4023_);
v___x_4026_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4027_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4028_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_4029_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4028_, v_currMacroScope_3996_);
v___x_4030_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4030_, 0, v___x_3998_);
lean_ctor_set(v___x_4030_, 1, v___x_4027_);
lean_ctor_set(v___x_4030_, 2, v___x_4029_);
lean_ctor_set(v___x_4030_, 3, v___x_4005_);
v___x_4031_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4032_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4033_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4032_, v_currMacroScope_3996_);
v___x_4034_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4034_, 0, v___x_3998_);
lean_ctor_set(v___x_4034_, 1, v___x_4031_);
lean_ctor_set(v___x_4034_, 2, v___x_4033_);
lean_ctor_set(v___x_4034_, 3, v___x_4005_);
lean_inc_ref(v___x_4034_);
v___x_4035_ = l_Lean_Syntax_node2(v___x_3998_, v___x_4013_, v___x_4030_, v___x_4034_);
v___x_4036_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4037_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4037_, 0, v___x_3998_);
lean_ctor_set(v___x_4037_, 1, v___x_4013_);
lean_ctor_set(v___x_4037_, 2, v___x_4036_);
v___x_4038_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_3998_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_3998_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = l_Lean_Syntax_node1(v___x_3998_, v___x_4040_, v___x_4042_);
lean_inc(v___x_4043_);
lean_inc_ref(v___x_4039_);
lean_inc_ref(v___x_4037_);
v___x_4044_ = l_Lean_Syntax_node4(v___x_3998_, v___x_4026_, v___x_4035_, v___x_4037_, v___x_4039_, v___x_4043_);
lean_inc_ref(v___x_4025_);
v___x_4045_ = l_Lean_Syntax_node2(v___x_3998_, v___x_4024_, v___x_4025_, v___x_4044_);
v___x_4046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_3998_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
lean_inc_ref(v___x_4047_);
lean_inc_ref(v___x_4022_);
lean_inc_ref(v___x_4016_);
v___x_4048_ = l_Lean_Syntax_node5(v___x_3998_, v___x_4014_, v___x_4016_, v___x_4020_, v___x_4022_, v___x_4045_, v___x_4047_);
v___x_4049_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4050_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4051_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4050_, v_currMacroScope_3996_);
v___x_4052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4052_, 0, v___x_3998_);
lean_ctor_set(v___x_4052_, 1, v___x_4049_);
lean_ctor_set(v___x_4052_, 2, v___x_4051_);
lean_ctor_set(v___x_4052_, 3, v___x_4005_);
v___x_4053_ = l_String_toRawSubstring_x27(v___x_3566_);
v___x_4054_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_3554_, v_currMacroScope_3996_);
v___x_4055_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4055_, 0, v___x_3998_);
lean_ctor_set(v___x_4055_, 1, v___x_4053_);
lean_ctor_set(v___x_4055_, 2, v___x_4054_);
lean_ctor_set(v___x_4055_, 3, v___x_4005_);
v___x_4056_ = l_Lean_Syntax_node2(v___x_3998_, v___x_4013_, v___x_4055_, v___x_4034_);
v___x_4057_ = l_Lean_Syntax_node4(v___x_3998_, v___x_4026_, v___x_4056_, v___x_4037_, v___x_4039_, v___x_4043_);
v___x_4058_ = l_Lean_Syntax_node2(v___x_3998_, v___x_4024_, v___x_4025_, v___x_4057_);
v___x_4059_ = l_Lean_Syntax_node5(v___x_3998_, v___x_4014_, v___x_4016_, v___x_4052_, v___x_4022_, v___x_4058_, v___x_4047_);
v___x_4060_ = l_Lean_Syntax_node2(v___x_3998_, v___x_4013_, v___x_4048_, v___x_4059_);
v___x_4061_ = l_Lean_Syntax_node2(v___x_3998_, v___x_3999_, v___x_4012_, v___x_4060_);
v_a_3577_ = v___x_4061_;
goto v___jp_3576_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3586_);
lean_dec_ref(v___x_3563_);
if (lean_obj_tag(v_a_3584_) == 1)
{
lean_object* v_val_4068_; lean_object* v_snd_4069_; lean_object* v_fst_4070_; lean_object* v_snd_4071_; lean_object* v___x_4072_; lean_object* v___f_4073_; lean_object* v___x_4074_; 
v_val_4068_ = lean_ctor_get(v_a_3584_, 0);
lean_inc(v_val_4068_);
lean_dec_ref(v_a_3584_);
v_snd_4069_ = lean_ctor_get(v_val_4068_, 1);
lean_inc(v_snd_4069_);
v_fst_4070_ = lean_ctor_get(v_val_4068_, 0);
lean_inc(v_fst_4070_);
lean_dec(v_val_4068_);
v_snd_4071_ = lean_ctor_get(v_snd_4069_, 1);
lean_inc(v_snd_4071_);
lean_dec(v_snd_4069_);
v___x_4072_ = lean_box(v___x_3560_);
lean_inc(v___x_3554_);
v___f_4073_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4073_, 0, v_fst_4070_);
lean_closure_set(v___f_4073_, 1, v_snd_4071_);
lean_closure_set(v___f_4073_, 2, v___x_3564_);
lean_closure_set(v___f_4073_, 3, v___x_3565_);
lean_closure_set(v___f_4073_, 4, v___x_3566_);
lean_closure_set(v___f_4073_, 5, v___x_3554_);
lean_closure_set(v___f_4073_, 6, v___x_3561_);
lean_closure_set(v___f_4073_, 7, v___x_4072_);
lean_closure_set(v___f_4073_, 8, v___x_3562_);
lean_closure_set(v___f_4073_, 9, v_arg_3559_);
v___x_4074_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3554_, v___x_3555_, v___f_4073_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec_ref(v___y_3573_);
v___y_3581_ = v___x_4074_;
goto v___jp_3580_;
}
else
{
lean_object* v_ref_4075_; lean_object* v_quotContext_4076_; lean_object* v_currMacroScope_4077_; uint8_t v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
lean_dec(v_a_3584_);
lean_dec(v___x_3562_);
lean_dec(v___x_3561_);
lean_dec_ref(v_arg_3559_);
lean_dec_ref(v___x_3555_);
v_ref_4075_ = lean_ctor_get(v___y_3573_, 5);
lean_inc(v_ref_4075_);
v_quotContext_4076_ = lean_ctor_get(v___y_3573_, 10);
lean_inc_n(v_quotContext_4076_, 2);
v_currMacroScope_4077_ = lean_ctor_get(v___y_3573_, 11);
lean_inc_n(v_currMacroScope_4077_, 2);
lean_dec_ref(v___y_3573_);
v___x_4078_ = 0;
v___x_4079_ = l_Lean_SourceInfo_fromRef(v_ref_4075_, v___x_4078_);
lean_dec(v_ref_4075_);
v___x_4080_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4081_ = l_Lean_Name_mkStr3(v___x_3564_, v___x_3565_, v___x_4080_);
v___x_4082_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4083_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4079_, 13);
v___x_4084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4079_);
lean_ctor_set(v___x_4084_, 1, v___x_4082_);
lean_ctor_set(v___x_4084_, 2, v___x_4083_);
v___x_4085_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_4086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4079_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
v___x_4087_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4088_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4079_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = l_String_toRawSubstring_x27(v___x_3566_);
v___x_4092_ = l_Lean_addMacroScope(v_quotContext_4076_, v___x_3554_, v_currMacroScope_4077_);
v___x_4093_ = lean_box(0);
v___x_4094_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4079_);
lean_ctor_set(v___x_4094_, 1, v___x_4091_);
lean_ctor_set(v___x_4094_, 2, v___x_4092_);
lean_ctor_set(v___x_4094_, 3, v___x_4093_);
v___x_4095_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4079_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4098_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4099_ = l_Lean_addMacroScope(v_quotContext_4076_, v___x_4098_, v_currMacroScope_4077_);
v___x_4100_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4079_);
lean_ctor_set(v___x_4100_, 1, v___x_4097_);
lean_ctor_set(v___x_4100_, 2, v___x_4099_);
lean_ctor_set(v___x_4100_, 3, v___x_4093_);
v___x_4101_ = l_Lean_Syntax_node3(v___x_4079_, v___x_4087_, v___x_4094_, v___x_4096_, v___x_4100_);
v___x_4102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4079_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = l_Lean_Syntax_node3(v___x_4079_, v___x_4088_, v___x_4090_, v___x_4101_, v___x_4103_);
v___x_4105_ = l_Lean_Syntax_node1(v___x_4079_, v___x_4087_, v___x_4104_);
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4079_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4109_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4079_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Lean_Syntax_node1(v___x_4079_, v___x_4108_, v___x_4110_);
v___x_4112_ = l_Lean_Syntax_node5(v___x_4079_, v___x_4081_, v___x_4084_, v___x_4086_, v___x_4105_, v___x_4107_, v___x_4111_);
v_a_3577_ = v___x_4112_;
goto v___jp_3576_;
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v_a_3584_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___x_3566_);
lean_dec_ref(v___x_3565_);
lean_dec_ref(v___x_3564_);
lean_dec_ref(v___x_3563_);
lean_dec(v___x_3562_);
lean_dec(v___x_3561_);
lean_dec_ref(v_arg_3559_);
lean_dec_ref(v___x_3555_);
lean_dec(v___x_3554_);
v_a_4113_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_3585_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_3585_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
else
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___x_3566_);
lean_dec_ref(v___x_3565_);
lean_dec_ref(v___x_3564_);
lean_dec_ref(v___x_3563_);
lean_dec(v___x_3562_);
lean_dec(v___x_3561_);
lean_dec_ref(v_arg_3559_);
lean_dec(v_inv_3558_);
lean_dec_ref(v___x_3555_);
lean_dec(v___x_3554_);
v_a_4121_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4123_ = v___x_3583_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_3583_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
v___jp_3576_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3577_);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
return v___x_3579_;
}
v___jp_3580_:
{
if (lean_obj_tag(v___y_3581_) == 0)
{
lean_object* v_a_3582_; 
v_a_3582_ = lean_ctor_get(v___y_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref(v___y_3581_);
v_a_3577_ = v_a_3582_;
goto v___jp_3576_;
}
else
{
return v___y_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4129_ = _args[0];
lean_object* v___x_4130_ = _args[1];
lean_object* v___f_4131_ = _args[2];
lean_object* v_a_4132_ = _args[3];
lean_object* v_inv_4133_ = _args[4];
lean_object* v_arg_4134_ = _args[5];
lean_object* v___x_4135_ = _args[6];
lean_object* v___x_4136_ = _args[7];
lean_object* v___x_4137_ = _args[8];
lean_object* v___x_4138_ = _args[9];
lean_object* v___x_4139_ = _args[10];
lean_object* v___x_4140_ = _args[11];
lean_object* v___x_4141_ = _args[12];
lean_object* v___y_4142_ = _args[13];
lean_object* v___y_4143_ = _args[14];
lean_object* v___y_4144_ = _args[15];
lean_object* v___y_4145_ = _args[16];
lean_object* v___y_4146_ = _args[17];
lean_object* v___y_4147_ = _args[18];
lean_object* v___y_4148_ = _args[19];
lean_object* v___y_4149_ = _args[20];
lean_object* v___y_4150_ = _args[21];
_start:
{
uint8_t v___x_93878__boxed_4151_; lean_object* v_res_4152_; 
v___x_93878__boxed_4151_ = lean_unbox(v___x_4135_);
v_res_4152_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4129_, v___x_4130_, v___f_4131_, v_a_4132_, v_inv_4133_, v_arg_4134_, v___x_93878__boxed_4151_, v___x_4136_, v___x_4137_, v___x_4138_, v___x_4139_, v___x_4140_, v___x_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec_ref(v_a_4132_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v___x_4159_; lean_object* v_env_4160_; lean_object* v___x_4161_; lean_object* v_mctx_4162_; lean_object* v_lctx_4163_; lean_object* v_options_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4159_ = lean_st_ref_get(v___y_4157_);
v_env_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc_ref(v_env_4160_);
lean_dec(v___x_4159_);
v___x_4161_ = lean_st_ref_get(v___y_4155_);
v_mctx_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc_ref(v_mctx_4162_);
lean_dec(v___x_4161_);
v_lctx_4163_ = lean_ctor_get(v___y_4154_, 2);
v_options_4164_ = lean_ctor_get(v___y_4156_, 2);
lean_inc_ref(v_options_4164_);
lean_inc_ref(v_lctx_4163_);
v___x_4165_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4165_, 0, v_env_4160_);
lean_ctor_set(v___x_4165_, 1, v_mctx_4162_);
lean_ctor_set(v___x_4165_, 2, v_lctx_4163_);
lean_ctor_set(v___x_4165_, 3, v_options_4164_);
v___x_4166_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
lean_ctor_set(v___x_4166_, 1, v_msgData_4153_);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_ref_4181_; lean_object* v___x_4182_; lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4191_; 
v_ref_4181_ = lean_ctor_get(v___y_4178_, 5);
v___x_4182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4185_ = v___x_4182_;
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4189_; 
lean_inc(v_ref_4181_);
v___x_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4187_, 0, v_ref_4181_);
lean_ctor_set(v___x_4187_, 1, v_a_4183_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set_tag(v___x_4185_, 1);
lean_ctor_set(v___x_4185_, 0, v___x_4187_);
v___x_4189_ = v___x_4185_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4205_, size_t v_i_4206_, size_t v_stop_4207_, lean_object* v_b_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_a_4219_; lean_object* v_a_4224_; uint8_t v___x_4226_; 
v___x_4226_ = lean_usize_dec_eq(v_i_4206_, v_stop_4207_);
if (v___x_4226_ == 0)
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4210_, v___y_4212_, v___y_4214_, v___y_4216_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; lean_object* v___y_4231_; uint8_t v___y_4232_; lean_object* v___y_4247_; lean_object* v_a_4248_; lean_object* v___x_4251_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref(v___x_4227_);
v___x_4229_ = lean_array_uget_borrowed(v_as_4205_, v_i_4206_);
lean_inc(v___x_4229_);
v___x_4251_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4229_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; lean_object* v_ref_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref(v___x_4251_);
v_ref_4253_ = lean_ctor_get(v___y_4215_, 5);
v___x_4254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
v___x_4256_ = l_Lean_SourceInfo_fromRef(v_ref_4253_, v___x_4226_);
lean_inc(v___x_4256_);
v___x_4257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
lean_ctor_set(v___x_4257_, 1, v___x_4254_);
v___x_4258_ = l_Lean_Syntax_node1(v___x_4256_, v___x_4255_, v___x_4257_);
v___x_4259_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4258_, v_a_4252_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4261_; 
lean_dec(v_a_4228_);
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref(v___x_4259_);
v___x_4261_ = lean_array_mk(v_a_4260_);
v_a_4224_ = v___x_4261_;
goto v___jp_4223_;
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
v_a_4262_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4259_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4259_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
lean_inc(v_a_4262_);
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
v___y_4247_ = v___x_4267_;
v_a_4248_ = v_a_4262_;
goto v___jp_4246_;
}
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
v_a_4270_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4251_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4251_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
lean_inc(v_a_4270_);
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
v___y_4247_ = v___x_4275_;
v_a_4248_ = v_a_4270_;
goto v___jp_4246_;
}
}
}
v___jp_4230_:
{
if (v___y_4232_ == 0)
{
lean_object* v___x_4233_; 
lean_dec_ref(v___y_4231_);
v___x_4233_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4228_, v___y_4232_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
lean_dec_ref(v___x_4233_);
v___x_4234_ = lean_unsigned_to_nat(1u);
v___x_4235_ = lean_mk_empty_array_with_capacity(v___x_4234_);
lean_inc(v___x_4229_);
v___x_4236_ = lean_array_push(v___x_4235_, v___x_4229_);
v_a_4224_ = v___x_4236_;
goto v___jp_4223_;
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v_b_4208_);
v_a_4237_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4233_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4233_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
else
{
lean_dec(v_a_4228_);
lean_dec_ref(v_b_4208_);
if (lean_obj_tag(v___y_4231_) == 0)
{
lean_object* v_a_4245_; 
v_a_4245_ = lean_ctor_get(v___y_4231_, 0);
lean_inc(v_a_4245_);
lean_dec_ref(v___y_4231_);
v_a_4219_ = v_a_4245_;
goto v___jp_4218_;
}
else
{
return v___y_4231_;
}
}
}
v___jp_4246_:
{
uint8_t v___x_4249_; 
v___x_4249_ = l_Lean_Exception_isInterrupt(v_a_4248_);
if (v___x_4249_ == 0)
{
uint8_t v___x_4250_; 
v___x_4250_ = l_Lean_Exception_isRuntime(v_a_4248_);
v___y_4231_ = v___y_4247_;
v___y_4232_ = v___x_4250_;
goto v___jp_4230_;
}
else
{
lean_dec_ref(v_a_4248_);
v___y_4231_ = v___y_4247_;
v___y_4232_ = v___x_4249_;
goto v___jp_4230_;
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec_ref(v_b_4208_);
v_a_4278_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4227_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4227_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
else
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v_b_4208_);
return v___x_4286_;
}
v___jp_4218_:
{
size_t v___x_4220_; size_t v___x_4221_; 
v___x_4220_ = ((size_t)1ULL);
v___x_4221_ = lean_usize_add(v_i_4206_, v___x_4220_);
v_i_4206_ = v___x_4221_;
v_b_4208_ = v_a_4219_;
goto _start;
}
v___jp_4223_:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Array_append___redArg(v_b_4208_, v_a_4224_);
lean_dec_ref(v_a_4224_);
v_a_4219_ = v___x_4225_;
goto v___jp_4218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4287_, lean_object* v_i_4288_, lean_object* v_stop_4289_, lean_object* v_b_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
size_t v_i_boxed_4300_; size_t v_stop_boxed_4301_; lean_object* v_res_4302_; 
v_i_boxed_4300_ = lean_unbox_usize(v_i_4288_);
lean_dec(v_i_4288_);
v_stop_boxed_4301_ = lean_unbox_usize(v_stop_4289_);
lean_dec(v_stop_4289_);
v_res_4302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4287_, v_i_boxed_4300_, v_stop_boxed_4301_, v_b_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v_as_4287_);
return v_res_4302_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4305_ = l_Lean_stringToMessageData(v___x_4304_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4321_, lean_object* v_inv_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v___x_4332_; 
lean_inc(v_inv_4322_);
v___x_4332_ = l_Lean_MVarId_getType(v_inv_4322_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4334_; lean_object* v_a_4335_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___x_4349_; uint8_t v___x_4350_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref(v___x_4332_);
v___x_4334_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4333_, v_a_4328_);
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc_n(v_a_4335_, 2);
lean_dec_ref(v___x_4334_);
v___x_4349_ = l_Lean_Expr_cleanupAnnotations(v_a_4335_);
v___x_4350_ = l_Lean_Expr_isApp(v___x_4349_);
if (v___x_4350_ == 0)
{
lean_dec_ref(v___x_4349_);
lean_dec(v_inv_4322_);
v___y_4337_ = v_a_4323_;
v___y_4338_ = v_a_4324_;
v___y_4339_ = v_a_4325_;
v___y_4340_ = v_a_4326_;
v___y_4341_ = v_a_4327_;
v___y_4342_ = v_a_4328_;
v___y_4343_ = v_a_4329_;
v___y_4344_ = v_a_4330_;
goto v___jp_4336_;
}
else
{
lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4349_);
v___x_4352_ = l_Lean_Expr_isApp(v___x_4351_);
if (v___x_4352_ == 0)
{
lean_dec_ref(v___x_4351_);
lean_dec(v_inv_4322_);
v___y_4337_ = v_a_4323_;
v___y_4338_ = v_a_4324_;
v___y_4339_ = v_a_4325_;
v___y_4340_ = v_a_4326_;
v___y_4341_ = v_a_4327_;
v___y_4342_ = v_a_4328_;
v___y_4343_ = v_a_4329_;
v___y_4344_ = v_a_4330_;
goto v___jp_4336_;
}
else
{
lean_object* v_arg_4353_; lean_object* v___x_4354_; uint8_t v___x_4355_; 
v_arg_4353_ = lean_ctor_get(v___x_4351_, 1);
lean_inc_ref(v_arg_4353_);
v___x_4354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4351_);
v___x_4355_ = l_Lean_Expr_isApp(v___x_4354_);
if (v___x_4355_ == 0)
{
lean_dec_ref(v___x_4354_);
lean_dec_ref(v_arg_4353_);
lean_dec(v_inv_4322_);
v___y_4337_ = v_a_4323_;
v___y_4338_ = v_a_4324_;
v___y_4339_ = v_a_4325_;
v___y_4340_ = v_a_4326_;
v___y_4341_ = v_a_4327_;
v___y_4342_ = v_a_4328_;
v___y_4343_ = v_a_4329_;
v___y_4344_ = v_a_4330_;
goto v___jp_4336_;
}
else
{
lean_object* v_arg_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v_arg_4356_ = lean_ctor_get(v___x_4354_, 1);
lean_inc_ref(v_arg_4356_);
v___x_4357_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4354_);
v___x_4358_ = l_Lean_Expr_isApp(v___x_4357_);
if (v___x_4358_ == 0)
{
lean_dec_ref(v___x_4357_);
lean_dec_ref(v_arg_4356_);
lean_dec_ref(v_arg_4353_);
lean_dec(v_inv_4322_);
v___y_4337_ = v_a_4323_;
v___y_4338_ = v_a_4324_;
v___y_4339_ = v_a_4325_;
v___y_4340_ = v_a_4326_;
v___y_4341_ = v_a_4327_;
v___y_4342_ = v_a_4328_;
v___y_4343_ = v_a_4329_;
v___y_4344_ = v_a_4330_;
goto v___jp_4336_;
}
else
{
lean_object* v_arg_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; 
v_arg_4359_ = lean_ctor_get(v___x_4357_, 1);
lean_inc_ref(v_arg_4359_);
v___x_4360_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4357_);
v___x_4361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4363_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4364_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4365_ = l_Lean_Expr_isConstOf(v___x_4360_, v___x_4364_);
if (v___x_4365_ == 0)
{
lean_dec_ref(v___x_4360_);
lean_dec_ref(v_arg_4359_);
lean_dec_ref(v_arg_4356_);
lean_dec_ref(v_arg_4353_);
lean_dec(v_inv_4322_);
v___y_4337_ = v_a_4323_;
v___y_4338_ = v_a_4324_;
v___y_4339_ = v_a_4325_;
v___y_4340_ = v_a_4326_;
v___y_4341_ = v_a_4327_;
v___y_4342_ = v_a_4328_;
v___y_4343_ = v_a_4329_;
v___y_4344_ = v_a_4330_;
goto v___jp_4336_;
}
else
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v_a_4372_; lean_object* v___y_4384_; lean_object* v___x_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; 
lean_dec(v_a_4335_);
v___x_4366_ = lean_unsigned_to_nat(1u);
v___x_4367_ = l_Lean_Expr_constLevels_x21(v___x_4360_);
lean_dec_ref(v___x_4360_);
v___x_4368_ = lean_unsigned_to_nat(0u);
v___x_4369_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4367_);
v___x_4370_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4367_, v___x_4367_, v___x_4366_, v___x_4369_);
lean_dec(v___x_4367_);
v___x_4394_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4395_ = lean_array_get_size(v_vcs_4321_);
v___x_4396_ = lean_nat_dec_lt(v___x_4368_, v___x_4395_);
if (v___x_4396_ == 0)
{
v_a_4372_ = v___x_4394_;
goto v___jp_4371_;
}
else
{
uint8_t v___x_4397_; 
v___x_4397_ = lean_nat_dec_le(v___x_4395_, v___x_4395_);
if (v___x_4397_ == 0)
{
if (v___x_4396_ == 0)
{
v_a_4372_ = v___x_4394_;
goto v___jp_4371_;
}
else
{
size_t v___x_4398_; size_t v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = ((size_t)0ULL);
v___x_4399_ = lean_usize_of_nat(v___x_4395_);
v___x_4400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4321_, v___x_4398_, v___x_4399_, v___x_4394_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
v___y_4384_ = v___x_4400_;
goto v___jp_4383_;
}
}
else
{
size_t v___x_4401_; size_t v___x_4402_; lean_object* v___x_4403_; 
v___x_4401_ = ((size_t)0ULL);
v___x_4402_ = lean_usize_of_nat(v___x_4395_);
v___x_4403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4321_, v___x_4401_, v___x_4402_, v___x_4394_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
v___y_4384_ = v___x_4403_;
goto v___jp_4383_;
}
}
v___jp_4371_:
{
lean_object* v___x_4373_; lean_object* v___f_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___f_4381_; lean_object* v___x_4382_; 
v___x_4373_ = lean_box(v___x_4365_);
lean_inc_ref(v_arg_4353_);
lean_inc_n(v_inv_4322_, 2);
lean_inc_ref(v_a_4372_);
v___f_4374_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4374_, 0, v_a_4372_);
lean_closure_set(v___f_4374_, 1, v_inv_4322_);
lean_closure_set(v___f_4374_, 2, v___x_4373_);
lean_closure_set(v___f_4374_, 3, v___x_4366_);
lean_closure_set(v___f_4374_, 4, v_arg_4353_);
v___x_4375_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4376_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4377_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4378_ = l_Lean_mkConst(v___x_4377_, v___x_4370_);
v___x_4379_ = l_Lean_mkAppB(v___x_4378_, v_arg_4359_, v_arg_4356_);
v___x_4380_ = lean_box(v___x_4365_);
v___f_4381_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4381_, 0, v___x_4376_);
lean_closure_set(v___f_4381_, 1, v___x_4379_);
lean_closure_set(v___f_4381_, 2, v___f_4374_);
lean_closure_set(v___f_4381_, 3, v_a_4372_);
lean_closure_set(v___f_4381_, 4, v_inv_4322_);
lean_closure_set(v___f_4381_, 5, v_arg_4353_);
lean_closure_set(v___f_4381_, 6, v___x_4380_);
lean_closure_set(v___f_4381_, 7, v___x_4366_);
lean_closure_set(v___f_4381_, 8, v___x_4368_);
lean_closure_set(v___f_4381_, 9, v___x_4363_);
lean_closure_set(v___f_4381_, 10, v___x_4361_);
lean_closure_set(v___f_4381_, 11, v___x_4362_);
lean_closure_set(v___f_4381_, 12, v___x_4375_);
v___x_4382_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4322_, v___f_4381_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
return v___x_4382_;
}
v___jp_4383_:
{
if (lean_obj_tag(v___y_4384_) == 0)
{
lean_object* v_a_4385_; 
v_a_4385_ = lean_ctor_get(v___y_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref(v___y_4384_);
v_a_4372_ = v_a_4385_;
goto v___jp_4371_;
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_dec(v___x_4370_);
lean_dec_ref(v_arg_4359_);
lean_dec_ref(v_arg_4356_);
lean_dec_ref(v_arg_4353_);
lean_dec(v_inv_4322_);
v_a_4386_ = lean_ctor_get(v___y_4384_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___y_4384_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___y_4384_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___y_4384_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
}
}
}
}
v___jp_4336_:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4345_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4346_ = l_Lean_MessageData_ofExpr(v_a_4335_);
v___x_4347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4345_);
lean_ctor_set(v___x_4347_, 1, v___x_4346_);
v___x_4348_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4347_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
return v___x_4348_;
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec(v_inv_4322_);
v_a_4404_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4332_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4332_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4412_, lean_object* v_inv_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4412_, v_inv_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_);
lean_dec(v_a_4421_);
lean_dec_ref(v_a_4420_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
lean_dec(v_a_4417_);
lean_dec_ref(v_a_4416_);
lean_dec(v_a_4415_);
lean_dec_ref(v_a_4414_);
lean_dec_ref(v_vcs_4412_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4424_, lean_object* v_msg_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4425_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4436_, lean_object* v_msg_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4436_, v_msg_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4448_, lean_object* v_name_4449_, uint8_t v_bi_4450_, lean_object* v_type_4451_, lean_object* v_k_4452_, uint8_t v_kind_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4449_, v_bi_4450_, v_type_4451_, v_k_4452_, v_kind_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4464_, lean_object* v_name_4465_, lean_object* v_bi_4466_, lean_object* v_type_4467_, lean_object* v_k_4468_, lean_object* v_kind_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
uint8_t v_bi_boxed_4479_; uint8_t v_kind_boxed_4480_; lean_object* v_res_4481_; 
v_bi_boxed_4479_ = lean_unbox(v_bi_4466_);
v_kind_boxed_4480_ = lean_unbox(v_kind_4469_);
v_res_4481_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4464_, v_name_4465_, v_bi_boxed_4479_, v_type_4467_, v_k_4468_, v_kind_boxed_4480_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4482_, lean_object* v_name_4483_, lean_object* v_type_4484_, lean_object* v_k_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4483_, v_type_4484_, v_k_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4496_, lean_object* v_name_4497_, lean_object* v_type_4498_, lean_object* v_k_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4496_, v_name_4497_, v_type_4498_, v_k_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4510_, size_t v_sz_4511_, size_t v_i_4512_, lean_object* v_b_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4510_, v_sz_4511_, v_i_4512_, v_b_4513_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4524_, lean_object* v_sz_4525_, lean_object* v_i_4526_, lean_object* v_b_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
size_t v_sz_boxed_4537_; size_t v_i_boxed_4538_; lean_object* v_res_4539_; 
v_sz_boxed_4537_ = lean_unbox_usize(v_sz_4525_);
lean_dec(v_sz_4525_);
v_i_boxed_4538_ = lean_unbox_usize(v_i_4526_);
lean_dec(v_i_4526_);
v_res_4539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4524_, v_sz_boxed_4537_, v_i_boxed_4538_, v_b_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec_ref(v_as_4524_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4540_, size_t v_sz_4541_, size_t v_i_4542_, lean_object* v_b_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4540_, v_sz_4541_, v_i_4542_, v_b_4543_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4554_, lean_object* v_sz_4555_, lean_object* v_i_4556_, lean_object* v_b_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
size_t v_sz_boxed_4567_; size_t v_i_boxed_4568_; lean_object* v_res_4569_; 
v_sz_boxed_4567_ = lean_unbox_usize(v_sz_4555_);
lean_dec(v_sz_4555_);
v_i_boxed_4568_ = lean_unbox_usize(v_i_4556_);
lean_dec(v_i_4556_);
v_res_4569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4554_, v_sz_boxed_4567_, v_i_boxed_4568_, v_b_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec_ref(v_as_4554_);
return v_res_4569_;
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
