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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_inc(v___y_54_);
v___x_55_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget_toAssertion(v___y_54_, v___y_53_);
lean_inc(v___y_54_);
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
lean_inc_ref(v_lctx_67_);
lean_dec_ref(v_a_50_);
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
lean_dec_ref(v_a_50_);
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
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
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
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
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
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
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
lean_inc(v___y_479_);
lean_inc_ref(v___y_478_);
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
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
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
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
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
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
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
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
v_i_474_ = v___x_484_;
v_b_475_ = v_a_482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___boxed(lean_object* v_inv_560_, lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v_as_563_, lean_object* v_sz_564_, lean_object* v_i_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___x_5772__boxed_572_; size_t v_sz_boxed_573_; size_t v_i_boxed_574_; lean_object* v_res_575_; 
v___x_5772__boxed_572_ = lean_unbox(v___x_561_);
v_sz_boxed_573_ = lean_unbox_usize(v_sz_564_);
lean_dec(v_sz_564_);
v_i_boxed_574_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2(v_inv_560_, v___x_5772__boxed_572_, v___x_562_, v_as_563_, v_sz_boxed_573_, v_i_boxed_574_, v_b_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
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
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
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
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
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
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
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
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
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
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
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
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
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
lean_inc_ref(v___y_911_);
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
lean_object* v___x_923_; lean_object* v___y_925_; size_t v___y_926_; lean_object* v___y_927_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___y_940_; size_t v___y_941_; lean_object* v_fvarIds_942_; lean_object* v___y_951_; size_t v___y_952_; lean_object* v___y_953_; lean_object* v___y_956_; lean_object* v___x_983_; uint8_t v___x_984_; 
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
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_928_, v___y_926_, v___y_927_);
v___x_930_ = l_Array_append___redArg(v___y_925_, v___x_929_);
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
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
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
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_909_, v_fvarIds_942_, v___y_941_, v___x_946_, v___x_938_);
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
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_909_, v_fvarIds_942_, v___y_941_, v___x_948_, v___x_938_);
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
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
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
v___y_940_ = v___y_956_;
v___y_941_ = v___x_961_;
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
v___y_940_ = v___y_956_;
v___y_941_ = v___x_961_;
v_fvarIds_942_ = v___x_938_;
goto v___jp_939_;
}
else
{
size_t v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_usize_of_nat(v___x_964_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_963_, v___x_961_, v___x_970_, v___x_968_);
lean_dec(v_a_963_);
v___y_951_ = v___y_956_;
v___y_952_ = v___x_961_;
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
v___y_951_ = v___y_956_;
v___y_952_ = v___x_961_;
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
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
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
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
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
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
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
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
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
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
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
lean_inc(v___x_1074_);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1074_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1095_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_mkConst(v___x_1096_, v___x_1099_);
lean_inc(v___x_1074_);
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
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
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
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
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
lean_inc(v___x_1074_);
v___x_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1074_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_a_1130_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_mkConst(v___x_1131_, v___x_1134_);
lean_inc(v___x_1074_);
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
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
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
lean_dec_ref(v_a_1149_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1164_, lean_object* v_dontRevert_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; 
lean_inc(v_a_1169_);
lean_inc_ref(v_a_1168_);
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
lean_inc_ref(v_e_1164_);
v___x_1171_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1164_, v_dontRevert_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_lctx_1173_; lean_object* v___x_1174_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
v_lctx_1173_ = lean_ctor_get(v_a_1166_, 2);
lean_inc_ref(v_lctx_1173_);
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
lean_dec_ref(v_lctx_1173_);
lean_dec(v_a_1172_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
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
lean_dec_ref(v_lctx_1173_);
lean_dec(v_a_1172_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
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
v___x_1196_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1172_, v_lctx_1173_, v___x_1193_, v___x_1194_, v___x_1195_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1172_);
return v___x_1196_;
}
}
}
}
else
{
lean_dec_ref(v_lctx_1173_);
lean_dec(v_a_1172_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v_e_1164_);
return v___x_1174_;
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
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
lean_dec_ref(v___x_1335_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1341_, lean_object* v___x_1342_, lean_object* v___x_1343_, lean_object* v_fvarId_1344_){
_start:
{
uint8_t v___x_11586__boxed_1345_; uint8_t v_res_1346_; lean_object* v_r_1347_; 
v___x_11586__boxed_1345_ = lean_unbox(v___x_1343_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1341_, v___x_1342_, v___x_11586__boxed_1345_, v_fvarId_1344_);
lean_dec(v_fvarId_1344_);
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
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1450_);
if (v___y_1460_ == 0)
{
lean_object* v___x_1462_; 
lean_dec_ref(v___y_1458_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v___y_1453_);
lean_dec_ref(v___y_1452_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___y_1451_);
v___x_1462_ = v___x_1444_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___y_1451_);
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
lean_ctor_set(v___x_1439_, 0, v___y_1454_);
v___x_1464_ = v___x_1439_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___y_1454_);
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
lean_ctor_set(v___x_1444_, 0, v___y_1453_);
v___x_1468_ = v___x_1444_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___y_1453_);
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
lean_dec_ref(v___y_1458_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v___y_1452_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_snd_1442_);
lean_ctor_set(v___x_1480_, 0, v___y_1451_);
v___x_1487_ = v___x_1480_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___y_1451_);
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
lean_ctor_set(v___x_1475_, 0, v___y_1454_);
v___x_1489_ = v___x_1475_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___y_1454_);
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
lean_inc_ref(v___y_1458_);
lean_inc_ref(v___y_1455_);
lean_inc_ref(v___y_1452_);
v___x_1498_ = l_Lean_Name_mkStr4(v___y_1452_, v___y_1455_, v___y_1458_, v___x_1497_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = l_Lean_Expr_isAppOfArity(v_fst_1477_, v___x_1498_, v___x_1499_);
lean_dec(v___x_1498_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_1502_ = l_Lean_Name_mkStr4(v___y_1452_, v___y_1455_, v___y_1458_, v___x_1501_);
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
lean_ctor_set(v___x_1480_, 0, v___y_1451_);
v___x_1508_ = v___x_1480_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___y_1451_);
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
lean_ctor_set(v___x_1475_, 0, v___y_1454_);
v___x_1510_ = v___x_1475_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___y_1454_);
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
lean_ctor_set(v___x_1480_, 0, v___y_1451_);
v___x_1518_ = v___x_1480_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___y_1451_);
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
lean_ctor_set(v___x_1475_, 0, v___y_1454_);
v___x_1520_ = v___x_1475_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___y_1454_);
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
lean_dec_ref(v___y_1458_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v___y_1452_);
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
lean_ctor_set(v___x_1480_, 0, v___y_1451_);
v___x_1528_ = v___x_1480_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___y_1451_);
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
lean_ctor_set(v___x_1475_, 0, v___y_1454_);
v___x_1530_ = v___x_1475_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___y_1454_);
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
lean_dec_ref(v___y_1458_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v___y_1452_);
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
lean_ctor_set(v___x_1480_, 0, v___y_1451_);
v___x_1537_ = v___x_1480_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___y_1451_);
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
lean_ctor_set(v___x_1475_, 0, v___y_1454_);
v___x_1539_ = v___x_1475_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___y_1454_);
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
lean_dec_ref(v___y_1458_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec(v_snd_1442_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
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
v___y_1450_ = v___y_1565_;
v___y_1451_ = v_suffixPoint_x3f_1562_;
v___y_1452_ = v___x_1567_;
v___y_1453_ = v___x_1577_;
v___y_1454_ = v_prefixPoint_x3f_1561_;
v___y_1455_ = v___x_1568_;
v___y_1456_ = v___y_1566_;
v___y_1457_ = v___y_1563_;
v___y_1458_ = v___x_1569_;
v___y_1459_ = v___y_1564_;
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
v___y_1450_ = v___y_1565_;
v___y_1451_ = v_suffixPoint_x3f_1562_;
v___y_1452_ = v___x_1567_;
v___y_1453_ = v___x_1577_;
v___y_1454_ = v_prefixPoint_x3f_1561_;
v___y_1455_ = v___x_1568_;
v___y_1456_ = v___y_1566_;
v___y_1457_ = v___y_1563_;
v___y_1458_ = v___x_1569_;
v___y_1459_ = v___y_1564_;
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
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
v___y_1560_ = v___y_1598_;
v_prefixPoint_x3f_1561_ = v___y_1591_;
v_suffixPoint_x3f_1562_ = v_fst_1441_;
v___y_1563_ = v___y_1594_;
v___y_1564_ = v___y_1597_;
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1596_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1594_);
lean_inc_ref(v_xs_1415_);
v___x_1603_ = l_Lean_Meta_mkProjection(v_xs_1415_, v___x_1602_, v___y_1594_, v___y_1597_, v___y_1592_, v___y_1596_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1594_);
v___x_1605_ = l_Lean_Meta_mkEq(v_a_1604_, v___y_1595_, v___y_1594_, v___y_1597_, v___y_1592_, v___y_1596_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1607_, 0, v___y_1599_);
lean_closure_set(v___x_1607_, 1, v___y_1593_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1594_);
lean_inc(v_a_1433_);
v___x_1608_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1433_, v___x_1607_, v___y_1594_, v___y_1597_, v___y_1592_, v___y_1596_);
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
lean_dec_ref(v___y_1590_);
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
v___x_1621_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1589_, v_letMutsPred_1617_, v___x_1610_);
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
v___y_1560_ = v___y_1598_;
v_prefixPoint_x3f_1561_ = v___y_1591_;
v_suffixPoint_x3f_1562_ = v___x_1625_;
v___y_1563_ = v___y_1594_;
v___y_1564_ = v___y_1597_;
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1596_;
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
v___x_1630_ = lean_apply_1(v___y_1590_, v_a_1606_);
v___x_1631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1631_, 0, v___y_1589_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
lean_ctor_set(v___x_1631_, 2, v___x_1610_);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
v___y_1560_ = v___y_1598_;
v_prefixPoint_x3f_1561_ = v___y_1591_;
v_suffixPoint_x3f_1562_ = v___x_1632_;
v___y_1563_ = v___y_1594_;
v___y_1564_ = v___y_1597_;
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1596_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_a_1606_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_del_object(v___x_1444_);
lean_dec(v_snd_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1439_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
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
v___y_1589_ = v___y_1658_;
v___y_1590_ = v___y_1659_;
v___y_1591_ = v_prefixPoint_x3f_1663_;
v___y_1592_ = v___y_1666_;
v___y_1593_ = v___f_1677_;
v___y_1594_ = v___y_1664_;
v___y_1595_ = v_cursorSuffix_1671_;
v___y_1596_ = v___y_1667_;
v___y_1597_ = v___y_1665_;
v___y_1598_ = v___y_1661_;
v___y_1599_ = v___y_1660_;
v___y_1600_ = v_letMutsTuple_1672_;
v___y_1601_ = v___x_1679_;
goto v___jp_1588_;
}
else
{
uint8_t v___x_1680_; 
v___x_1680_ = l_Lean_Expr_isFVar(v_letMutsTuple_1672_);
v___y_1589_ = v___y_1658_;
v___y_1590_ = v___y_1659_;
v___y_1591_ = v_prefixPoint_x3f_1663_;
v___y_1592_ = v___y_1666_;
v___y_1593_ = v___f_1677_;
v___y_1594_ = v___y_1664_;
v___y_1595_ = v_cursorSuffix_1671_;
v___y_1596_ = v___y_1667_;
v___y_1597_ = v___y_1665_;
v___y_1598_ = v___y_1661_;
v___y_1599_ = v___y_1660_;
v___y_1600_ = v_letMutsTuple_1672_;
v___y_1601_ = v___x_1680_;
goto v___jp_1588_;
}
}
}
else
{
lean_dec(v___x_1668_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
v___y_1560_ = v___y_1661_;
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
lean_inc_ref(v___y_1683_);
v___x_1689_ = lean_apply_1(v___y_1683_, v___y_1684_);
lean_inc(v___y_1682_);
v___x_1690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1690_, 0, v___y_1682_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_ctor_set(v___x_1690_, 2, v_a_1688_);
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
v___y_1658_ = v___y_1682_;
v___y_1659_ = v___y_1683_;
v___y_1660_ = v___y_1686_;
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
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
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
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
v___y_1658_ = v_fst_1699_;
v___y_1659_ = v___f_1708_;
v___y_1660_ = v_snd_1704_;
v___y_1661_ = v_a_1693_;
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
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc_ref(v_xs_1415_);
v___x_1724_ = l_Lean_Meta_mkProjection(v_xs_1415_, v___x_1723_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
v___x_1726_ = l_Lean_Meta_mkEq(v_a_1725_, v_cursorPrefix_1712_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1726_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
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
v___y_1682_ = v_fst_1699_;
v___y_1683_ = v___f_1708_;
v___y_1684_ = v_a_1727_;
v___y_1685_ = v_a_1693_;
v___y_1686_ = v_snd_1704_;
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
v___y_1682_ = v_fst_1699_;
v___y_1683_ = v___f_1708_;
v___y_1684_ = v_a_1727_;
v___y_1685_ = v_a_1693_;
v___y_1686_ = v_snd_1704_;
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
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
v___y_1658_ = v_fst_1699_;
v___y_1659_ = v___f_1708_;
v___y_1660_ = v_snd_1704_;
v___y_1661_ = v_a_1693_;
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
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
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
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
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
lean_dec_ref(v_as_1793_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1814_, lean_object* v_inv_1815_, lean_object* v_xs_1816_, lean_object* v_letMuts_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_lctx_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; size_t v_sz_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v_lctx_1823_ = lean_ctor_get(v_a_1818_, 2);
lean_inc_ref(v_lctx_1823_);
v___x_1824_ = lean_box(0);
v___x_1825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1826_ = lean_array_size(v_vcs_1814_);
v___x_1827_ = ((size_t)0ULL);
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
v___x_1954_ = lean_panic_fn(v___x_1953_, v_msg_1952_);
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
lean_object* v___x_2095_; 
v___x_2095_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(v_x_2090_, v_h__1_2091_, v_h__2_2092_, v_h__3_2093_, v_h__4_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2096_, lean_object* v_h__1_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_apply_2(v_h__1_2097_, v_x_2096_, lean_box(0));
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2099_, lean_object* v_P_2100_, lean_object* v_motive_2101_, lean_object* v_x_2102_, lean_object* v_h__1_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_apply_2(v_h__1_2103_, v_x_2102_, lean_box(0));
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2107_, lean_object* v_syn_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2110_, lean_object* v_syn_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2110_, v_syn_2111_);
lean_dec(v_name_2110_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2119_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2147_ = lean_unsigned_to_nat(2u);
v___x_2148_ = l_Lean_Expr_isAppOfArity(v_e_2119_, v___x_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2150_ = lean_unsigned_to_nat(3u);
v___x_2151_ = l_Lean_Expr_isAppOfArity(v_e_2119_, v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2153_ = l_Lean_Expr_isAppOfArity(v_e_2119_, v___x_2152_, v___x_2150_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2155_ = l_Lean_Expr_isAppOfArity(v_e_2119_, v___x_2154_, v___x_2150_);
if (v___x_2155_ == 0)
{
goto v___jp_2120_;
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Expr_appArg_x21(v_e_2119_);
if (lean_obj_tag(v___x_2156_) == 6)
{
lean_object* v_binderName_2157_; lean_object* v_binderType_2158_; lean_object* v_body_2159_; uint8_t v_binderInfo_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v_e_2119_);
v_binderName_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_binderName_2157_);
v_binderType_2158_ = lean_ctor_get(v___x_2156_, 1);
lean_inc_ref(v_binderType_2158_);
v_body_2159_ = lean_ctor_get(v___x_2156_, 2);
lean_inc_ref(v_body_2159_);
v_binderInfo_2160_ = lean_ctor_get_uint8(v___x_2156_, sizeof(void*)*3 + 8);
lean_dec_ref(v___x_2156_);
v___x_2161_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2159_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_dec_ref(v_binderType_2158_);
lean_dec(v_binderName_2157_);
return v___x_2161_;
}
else
{
lean_object* v_val_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2179_; 
v_val_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2179_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_val_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2179_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_fst_2166_; lean_object* v_snd_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2178_; 
v_fst_2166_ = lean_ctor_get(v_val_2162_, 0);
v_snd_2167_ = lean_ctor_get(v_val_2162_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_val_2162_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2169_ = v_val_2162_;
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_snd_2167_);
lean_inc(v_fst_2166_);
lean_dec(v_val_2162_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = l_Lean_mkForall(v_binderName_2157_, v_binderInfo_2160_, v_binderType_2158_, v_snd_2167_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v___x_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_fst_2166_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2173_);
v___x_2175_ = v___x_2164_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2156_);
goto v___jp_2120_;
}
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = l_Lean_Expr_appFn_x21(v_e_2119_);
v___x_2181_ = l_Lean_Expr_appArg_x21(v___x_2180_);
lean_dec_ref(v___x_2180_);
v___x_2182_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2181_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_dec_ref(v_e_2119_);
return v___x_2182_;
}
else
{
lean_object* v_val_2183_; lean_object* v_snd_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_val_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref(v___x_2182_);
v_snd_2184_ = lean_ctor_get(v_val_2183_, 1);
lean_inc(v_snd_2184_);
lean_dec(v_val_2183_);
v___x_2185_ = l_Lean_Expr_appArg_x21(v_e_2119_);
lean_dec_ref(v_e_2119_);
v___x_2186_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2185_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_dec(v_snd_2184_);
return v___x_2186_;
}
else
{
lean_object* v_val_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2204_; 
v_val_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2204_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_val_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2204_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_fst_2191_; lean_object* v_snd_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2203_; 
v_fst_2191_ = lean_ctor_get(v_val_2187_, 0);
v_snd_2192_ = lean_ctor_get(v_val_2187_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_val_2187_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2194_ = v_val_2187_;
v_isShared_2195_ = v_isSharedCheck_2203_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_snd_2192_);
lean_inc(v_fst_2191_);
lean_dec(v_val_2187_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2203_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = l_Lean_mkOr(v_snd_2184_, v_snd_2192_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v___x_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_fst_2191_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2200_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2198_);
v___x_2200_ = v___x_2189_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
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
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = l_Lean_Expr_appFn_x21(v_e_2119_);
v___x_2206_ = l_Lean_Expr_appArg_x21(v___x_2205_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2206_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_dec_ref(v_e_2119_);
return v___x_2207_;
}
else
{
lean_object* v_val_2208_; lean_object* v_snd_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_val_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2208_);
lean_dec_ref(v___x_2207_);
v_snd_2209_ = lean_ctor_get(v_val_2208_, 1);
lean_inc(v_snd_2209_);
lean_dec(v_val_2208_);
v___x_2210_ = l_Lean_Expr_appArg_x21(v_e_2119_);
lean_dec_ref(v_e_2119_);
v___x_2211_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2210_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_dec(v_snd_2209_);
return v___x_2211_;
}
else
{
lean_object* v_val_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2229_; 
v_val_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2229_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_val_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2229_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_fst_2216_; lean_object* v_snd_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2228_; 
v_fst_2216_ = lean_ctor_get(v_val_2212_, 0);
v_snd_2217_ = lean_ctor_get(v_val_2212_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_val_2212_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2219_ = v_val_2212_;
v_isShared_2220_ = v_isSharedCheck_2228_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_snd_2217_);
lean_inc(v_fst_2216_);
lean_dec(v_val_2212_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2228_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2221_ = l_Lean_mkAnd(v_snd_2209_, v_snd_2217_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v___x_2221_);
v___x_2223_ = v___x_2219_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_fst_2216_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2225_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2223_);
v___x_2225_ = v___x_2214_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
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
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2230_ = lean_box(0);
v___x_2231_ = l_Lean_Expr_getAppFn(v_e_2119_);
v___x_2232_ = l_Lean_Expr_constLevels_x21(v___x_2231_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = l_List_get_x21Internal___redArg(v___x_2230_, v___x_2232_, v___x_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = l_Lean_Expr_getAppNumArgs(v_e_2119_);
v___x_2237_ = lean_nat_sub(v___x_2236_, v___x_2235_);
lean_dec(v___x_2236_);
v___x_2238_ = lean_nat_sub(v___x_2237_, v___x_2235_);
lean_dec(v___x_2237_);
v___x_2239_ = l_Lean_Expr_getRevArg_x21(v_e_2119_, v___x_2238_);
lean_dec_ref(v_e_2119_);
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2234_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
v___jp_2120_:
{
if (lean_obj_tag(v_e_2119_) == 8)
{
lean_object* v_declName_2121_; lean_object* v_type_2122_; lean_object* v_value_2123_; lean_object* v_body_2124_; uint8_t v_nondep_2125_; lean_object* v___x_2126_; 
v_declName_2121_ = lean_ctor_get(v_e_2119_, 0);
lean_inc(v_declName_2121_);
v_type_2122_ = lean_ctor_get(v_e_2119_, 1);
lean_inc_ref(v_type_2122_);
v_value_2123_ = lean_ctor_get(v_e_2119_, 2);
lean_inc_ref(v_value_2123_);
v_body_2124_ = lean_ctor_get(v_e_2119_, 3);
lean_inc_ref(v_body_2124_);
v_nondep_2125_ = lean_ctor_get_uint8(v_e_2119_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2119_);
v___x_2126_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2124_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_dec_ref(v_value_2123_);
lean_dec_ref(v_type_2122_);
lean_dec(v_declName_2121_);
return v___x_2126_;
}
else
{
lean_object* v_val_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2144_; 
v_val_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2144_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_val_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2144_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_fst_2131_; lean_object* v_snd_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2143_; 
v_fst_2131_ = lean_ctor_get(v_val_2127_, 0);
v_snd_2132_ = lean_ctor_get(v_val_2127_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_val_2127_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2134_ = v_val_2127_;
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_snd_2132_);
lean_inc(v_fst_2131_);
lean_dec(v_val_2127_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = l_Lean_Expr_letE___override(v_declName_2121_, v_type_2122_, v_value_2123_, v_snd_2132_, v_nondep_2125_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 1, v___x_2136_);
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_fst_2131_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2138_);
v___x_2140_ = v___x_2129_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
else
{
lean_object* v___x_2145_; 
lean_dec_ref(v_e_2119_);
v___x_2145_ = lean_box(0);
return v___x_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2242_){
_start:
{
lean_object* v___x_2243_; 
lean_inc_ref(v_e_2242_);
v___x_2243_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
return v_e_2242_;
}
else
{
lean_object* v_val_2244_; lean_object* v_fst_2245_; lean_object* v_snd_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec_ref(v_e_2242_);
v_val_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_val_2244_);
lean_dec_ref(v___x_2243_);
v_fst_2245_ = lean_ctor_get(v_val_2244_, 0);
lean_inc(v_fst_2245_);
v_snd_2246_ = lean_ctor_get(v_val_2244_, 1);
lean_inc(v_snd_2246_);
lean_dec(v_val_2244_);
lean_inc(v_fst_2245_);
v___x_2247_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2245_);
v___x_2248_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2245_, v___x_2247_, v_snd_2246_);
return v___x_2248_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Array_mkArray0(lean_box(0));
return v___x_2259_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2298_ = l_String_toRawSubstring_x27(v___x_2297_);
return v___x_2298_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2315_ = l_String_toRawSubstring_x27(v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2330_, lean_object* v_default_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2337_; lean_object* v_handlers_2338_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2338_ = l_Lean_Syntax_SepArray_ofElems(v___x_2337_, v_handlers_2330_);
switch(lean_obj_tag(v_default_2331_))
{
case 0:
{
lean_object* v_ref_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
lean_dec(v_a_2335_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
v_ref_2339_ = lean_ctor_get(v_a_2334_, 5);
lean_inc(v_ref_2339_);
lean_dec_ref(v_a_2334_);
v___x_2340_ = 0;
v___x_2341_ = l_Lean_SourceInfo_fromRef(v_ref_2339_, v___x_2340_);
lean_dec(v_ref_2339_);
v___x_2342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2343_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc(v___x_2341_);
v___x_2344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2341_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2346_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2347_ = l_Array_append___redArg(v___x_2346_, v_handlers_2338_);
lean_dec_ref(v_handlers_2338_);
lean_inc(v___x_2341_);
v___x_2348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2341_);
lean_ctor_set(v___x_2348_, 1, v___x_2345_);
lean_ctor_set(v___x_2348_, 2, v___x_2347_);
v___x_2349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
lean_inc(v___x_2341_);
v___x_2350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2341_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Lean_Syntax_node3(v___x_2341_, v___x_2342_, v___x_2344_, v___x_2348_, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
case 1:
{
lean_object* v_ref_2353_; lean_object* v_quotContext_2354_; lean_object* v_currMacroScope_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v_a_2335_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
v_ref_2353_ = lean_ctor_get(v_a_2334_, 5);
lean_inc(v_ref_2353_);
v_quotContext_2354_ = lean_ctor_get(v_a_2334_, 10);
lean_inc(v_quotContext_2354_);
v_currMacroScope_2355_ = lean_ctor_get(v_a_2334_, 11);
lean_inc(v_currMacroScope_2355_);
lean_dec_ref(v_a_2334_);
v___x_2356_ = 0;
v___x_2357_ = l_Lean_SourceInfo_fromRef(v_ref_2353_, v___x_2356_);
lean_dec(v_ref_2353_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc(v___x_2357_);
v___x_2360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2357_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
lean_inc(v___x_2357_);
v___x_2366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2357_);
lean_ctor_set(v___x_2366_, 1, v___x_2364_);
v___x_2367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc(v___x_2357_);
v___x_2369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2357_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2371_ = l_Array_append___redArg(v___x_2370_, v_handlers_2338_);
lean_dec_ref(v_handlers_2338_);
lean_inc(v___x_2357_);
v___x_2372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2357_);
lean_ctor_set(v___x_2372_, 1, v___x_2337_);
v___x_2373_ = lean_array_push(v___x_2371_, v___x_2372_);
v___x_2374_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
v___x_2376_ = l_Lean_addMacroScope(v_quotContext_2354_, v___x_2375_, v_currMacroScope_2355_);
v___x_2377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
lean_inc(v___x_2357_);
v___x_2378_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2357_);
lean_ctor_set(v___x_2378_, 1, v___x_2374_);
lean_ctor_set(v___x_2378_, 2, v___x_2376_);
lean_ctor_set(v___x_2378_, 3, v___x_2377_);
v___x_2379_ = lean_array_push(v___x_2373_, v___x_2378_);
lean_inc(v___x_2357_);
v___x_2380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2357_);
lean_ctor_set(v___x_2380_, 1, v___x_2363_);
lean_ctor_set(v___x_2380_, 2, v___x_2379_);
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
lean_inc(v___x_2357_);
v___x_2382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2357_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
lean_inc(v___x_2357_);
v___x_2383_ = l_Lean_Syntax_node3(v___x_2357_, v___x_2367_, v___x_2369_, v___x_2380_, v___x_2382_);
lean_inc(v___x_2357_);
v___x_2384_ = l_Lean_Syntax_node2(v___x_2357_, v___x_2365_, v___x_2366_, v___x_2383_);
lean_inc(v___x_2357_);
v___x_2385_ = l_Lean_Syntax_node1(v___x_2357_, v___x_2363_, v___x_2384_);
lean_inc(v___x_2357_);
v___x_2386_ = l_Lean_Syntax_node1(v___x_2357_, v___x_2362_, v___x_2385_);
lean_inc(v___x_2357_);
v___x_2387_ = l_Lean_Syntax_node1(v___x_2357_, v___x_2361_, v___x_2386_);
v___x_2388_ = l_Lean_Syntax_node2(v___x_2357_, v___x_2358_, v___x_2360_, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
case 2:
{
lean_object* v_ref_2390_; lean_object* v_quotContext_2391_; lean_object* v_currMacroScope_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec(v_a_2335_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
v_ref_2390_ = lean_ctor_get(v_a_2334_, 5);
lean_inc(v_ref_2390_);
v_quotContext_2391_ = lean_ctor_get(v_a_2334_, 10);
lean_inc(v_quotContext_2391_);
v_currMacroScope_2392_ = lean_ctor_get(v_a_2334_, 11);
lean_inc(v_currMacroScope_2392_);
lean_dec_ref(v_a_2334_);
v___x_2393_ = 0;
v___x_2394_ = l_Lean_SourceInfo_fromRef(v_ref_2390_, v___x_2393_);
lean_dec(v_ref_2390_);
v___x_2395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc(v___x_2394_);
v___x_2397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2394_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
lean_inc(v___x_2394_);
v___x_2403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2394_);
lean_ctor_set(v___x_2403_, 1, v___x_2401_);
v___x_2404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc(v___x_2394_);
v___x_2406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2394_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2408_ = l_Array_append___redArg(v___x_2407_, v_handlers_2338_);
lean_dec_ref(v_handlers_2338_);
lean_inc(v___x_2394_);
v___x_2409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2394_);
lean_ctor_set(v___x_2409_, 1, v___x_2337_);
v___x_2410_ = lean_array_push(v___x_2408_, v___x_2409_);
v___x_2411_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_2413_ = l_Lean_addMacroScope(v_quotContext_2391_, v___x_2412_, v_currMacroScope_2392_);
v___x_2414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
lean_inc(v___x_2394_);
v___x_2415_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2394_);
lean_ctor_set(v___x_2415_, 1, v___x_2411_);
lean_ctor_set(v___x_2415_, 2, v___x_2413_);
lean_ctor_set(v___x_2415_, 3, v___x_2414_);
v___x_2416_ = lean_array_push(v___x_2410_, v___x_2415_);
lean_inc(v___x_2394_);
v___x_2417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2394_);
lean_ctor_set(v___x_2417_, 1, v___x_2400_);
lean_ctor_set(v___x_2417_, 2, v___x_2416_);
v___x_2418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
lean_inc(v___x_2394_);
v___x_2419_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2394_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
lean_inc(v___x_2394_);
v___x_2420_ = l_Lean_Syntax_node3(v___x_2394_, v___x_2404_, v___x_2406_, v___x_2417_, v___x_2419_);
lean_inc(v___x_2394_);
v___x_2421_ = l_Lean_Syntax_node2(v___x_2394_, v___x_2402_, v___x_2403_, v___x_2420_);
lean_inc(v___x_2394_);
v___x_2422_ = l_Lean_Syntax_node1(v___x_2394_, v___x_2400_, v___x_2421_);
lean_inc(v___x_2394_);
v___x_2423_ = l_Lean_Syntax_node1(v___x_2394_, v___x_2399_, v___x_2422_);
lean_inc(v___x_2394_);
v___x_2424_ = l_Lean_Syntax_node1(v___x_2394_, v___x_2398_, v___x_2423_);
v___x_2425_ = l_Lean_Syntax_node2(v___x_2394_, v___x_2395_, v___x_2397_, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
default: 
{
lean_object* v_e_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_e_2427_ = lean_ctor_get(v_default_2331_, 0);
lean_inc_ref(v_e_2427_);
lean_dec_ref(v_default_2331_);
v___x_2428_ = lean_box(1);
lean_inc_ref(v_a_2334_);
v___x_2429_ = l_Lean_PrettyPrinter_delab(v_e_2427_, v___x_2428_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2466_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2466_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2466_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_ref_2434_; uint8_t v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v_ref_2434_ = lean_ctor_get(v_a_2334_, 5);
lean_inc(v_ref_2434_);
lean_dec_ref(v_a_2334_);
v___x_2435_ = 0;
v___x_2436_ = l_Lean_SourceInfo_fromRef(v_ref_2434_, v___x_2435_);
lean_dec(v_ref_2434_);
v___x_2437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc(v___x_2436_);
v___x_2439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2436_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
lean_inc(v___x_2436_);
v___x_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2436_);
lean_ctor_set(v___x_2445_, 1, v___x_2443_);
v___x_2446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc(v___x_2436_);
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2436_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2450_ = l_Array_append___redArg(v___x_2449_, v_handlers_2338_);
lean_dec_ref(v_handlers_2338_);
lean_inc(v___x_2436_);
v___x_2451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2436_);
lean_ctor_set(v___x_2451_, 1, v___x_2337_);
v___x_2452_ = lean_array_push(v___x_2450_, v___x_2451_);
v___x_2453_ = lean_array_push(v___x_2452_, v_a_2430_);
lean_inc(v___x_2436_);
v___x_2454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2436_);
lean_ctor_set(v___x_2454_, 1, v___x_2442_);
lean_ctor_set(v___x_2454_, 2, v___x_2453_);
v___x_2455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
lean_inc(v___x_2436_);
v___x_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2436_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
lean_inc(v___x_2436_);
v___x_2457_ = l_Lean_Syntax_node3(v___x_2436_, v___x_2446_, v___x_2448_, v___x_2454_, v___x_2456_);
lean_inc(v___x_2436_);
v___x_2458_ = l_Lean_Syntax_node2(v___x_2436_, v___x_2444_, v___x_2445_, v___x_2457_);
lean_inc(v___x_2436_);
v___x_2459_ = l_Lean_Syntax_node1(v___x_2436_, v___x_2442_, v___x_2458_);
lean_inc(v___x_2436_);
v___x_2460_ = l_Lean_Syntax_node1(v___x_2436_, v___x_2441_, v___x_2459_);
lean_inc(v___x_2436_);
v___x_2461_ = l_Lean_Syntax_node1(v___x_2436_, v___x_2440_, v___x_2460_);
v___x_2462_ = l_Lean_Syntax_node2(v___x_2436_, v___x_2437_, v___x_2439_, v___x_2461_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2462_);
v___x_2464_ = v___x_2432_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_dec_ref(v_handlers_2338_);
lean_dec_ref(v_a_2334_);
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2467_, lean_object* v_default_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2467_, v_default_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec_ref(v_handlers_2467_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2475_, lean_object* v___y_2476_){
_start:
{
uint8_t v___x_2478_; 
v___x_2478_ = l_Lean_Expr_hasMVar(v_e_2475_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v_e_2475_);
return v___x_2479_;
}
else
{
lean_object* v___x_2480_; lean_object* v_mctx_2481_; lean_object* v___x_2482_; lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___x_2485_; lean_object* v_cache_2486_; lean_object* v_zetaDeltaFVarIds_2487_; lean_object* v_postponed_2488_; lean_object* v_diag_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2498_; 
v___x_2480_ = lean_st_ref_get(v___y_2476_);
v_mctx_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc_ref(v_mctx_2481_);
lean_dec(v___x_2480_);
v___x_2482_ = l_Lean_instantiateMVarsCore(v_mctx_2481_, v_e_2475_);
v_fst_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_fst_2483_);
v_snd_2484_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_snd_2484_);
lean_dec_ref(v___x_2482_);
v___x_2485_ = lean_st_ref_take(v___y_2476_);
v_cache_2486_ = lean_ctor_get(v___x_2485_, 1);
v_zetaDeltaFVarIds_2487_ = lean_ctor_get(v___x_2485_, 2);
v_postponed_2488_ = lean_ctor_get(v___x_2485_, 3);
v_diag_2489_ = lean_ctor_get(v___x_2485_, 4);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v___x_2485_, 0);
lean_dec(v_unused_2499_);
v___x_2491_ = v___x_2485_;
v_isShared_2492_ = v_isSharedCheck_2498_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_diag_2489_);
lean_inc(v_postponed_2488_);
lean_inc(v_zetaDeltaFVarIds_2487_);
lean_inc(v_cache_2486_);
lean_dec(v___x_2485_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2498_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v_snd_2484_);
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_snd_2484_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_cache_2486_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_zetaDeltaFVarIds_2487_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v_postponed_2488_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v_diag_2489_);
v___x_2494_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_st_ref_set(v___y_2476_, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_fst_2483_);
return v___x_2496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2500_, v___y_2501_);
lean_dec(v___y_2501_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2504_, v___y_2510_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_apply_9(v_x_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, lean_box(0));
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2548_, lean_object* v_x_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___f_2559_; lean_object* v___x_2560_; 
v___f_2559_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2559_, 0, v_x_2549_);
lean_closure_set(v___f_2559_, 1, v___y_2550_);
lean_closure_set(v___f_2559_, 2, v___y_2551_);
lean_closure_set(v___f_2559_, 3, v___y_2552_);
lean_closure_set(v___f_2559_, 4, v___y_2553_);
v___x_2560_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2548_, v___f_2559_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2560_) == 0)
{
return v___x_2560_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2569_, lean_object* v_x_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2569_, v_x_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2581_, lean_object* v_mvarId_2582_, lean_object* v_x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2582_, v_x_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2594_, lean_object* v_mvarId_2595_, lean_object* v_x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2594_, v_mvarId_2595_, v_x_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2607_, lean_object* v_inv_2608_, lean_object* v_xs_2609_, uint8_t v___x_2610_, lean_object* v___x_2611_, lean_object* v_letMuts_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
lean_inc(v___y_2620_);
lean_inc_ref(v___y_2619_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc_ref(v_letMuts_2612_);
lean_inc_ref(v_xs_2609_);
v___x_2622_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2607_, v_inv_2608_, v_xs_2609_, v_letMuts_2612_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2699_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2699_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2699_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
if (lean_obj_tag(v_a_2623_) == 1)
{
lean_object* v_val_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2694_; 
lean_del_object(v___x_2625_);
v_val_2627_ = lean_ctor_get(v_a_2623_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2623_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2629_ = v_a_2623_;
v_isShared_2630_ = v_isSharedCheck_2694_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_val_2627_);
lean_dec(v_a_2623_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2694_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_snd_2631_; lean_object* v_fst_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2693_; 
v_snd_2631_ = lean_ctor_get(v_val_2627_, 1);
v_fst_2632_ = lean_ctor_get(v_val_2627_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_val_2627_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2634_ = v_val_2627_;
v_isShared_2635_ = v_isSharedCheck_2693_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_snd_2631_);
lean_inc(v_fst_2632_);
lean_dec(v_val_2627_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2693_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2692_; 
v_fst_2636_ = lean_ctor_get(v_snd_2631_, 0);
v_snd_2637_ = lean_ctor_get(v_snd_2631_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_snd_2631_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2639_ = v_snd_2631_;
v_isShared_2640_ = v_isSharedCheck_2692_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_snd_2637_);
lean_inc(v_fst_2636_);
lean_dec(v_snd_2631_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2692_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_lvl_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; 
v_lvl_2641_ = lean_ctor_get(v_fst_2632_, 0);
lean_inc(v_lvl_2641_);
v___x_2642_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2632_);
lean_inc(v_fst_2636_);
v___x_2643_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2636_);
v___x_2644_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2641_, v___x_2642_, v___x_2643_);
v___x_2645_ = lean_unsigned_to_nat(2u);
v___x_2646_ = lean_mk_empty_array_with_capacity(v___x_2645_);
v___x_2647_ = lean_array_push(v___x_2646_, v_xs_2609_);
lean_inc_ref(v_letMuts_2612_);
v___x_2648_ = lean_array_push(v___x_2647_, v_letMuts_2612_);
v___x_2649_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2644_);
v___x_2650_ = 0;
v___x_2651_ = 1;
v___x_2652_ = l_Lean_Meta_mkLambdaFVars(v___x_2648_, v___x_2649_, v___x_2650_, v___x_2610_, v___x_2650_, v___x_2610_, v___x_2651_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec_ref(v___x_2648_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_letMutsPred_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v_letMutsPred_2654_ = lean_ctor_get(v_fst_2636_, 2);
lean_inc_ref(v_letMutsPred_2654_);
lean_dec(v_fst_2636_);
v___x_2655_ = lean_mk_empty_array_with_capacity(v___x_2611_);
v___x_2656_ = lean_array_push(v___x_2655_, v_letMuts_2612_);
v___x_2657_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2654_);
v___x_2658_ = l_Lean_Meta_mkLambdaFVars(v___x_2656_, v___x_2657_, v___x_2650_, v___x_2610_, v___x_2650_, v___x_2610_, v___x_2651_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___x_2656_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2675_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_a_2659_);
v___x_2664_ = v___x_2639_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2659_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_snd_2637_);
v___x_2664_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2666_; 
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 1, v___x_2664_);
lean_ctor_set(v___x_2634_, 0, v_a_2653_);
v___x_2666_ = v___x_2634_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2653_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2668_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2666_);
v___x_2668_ = v___x_2629_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2670_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2668_);
v___x_2670_ = v___x_2661_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_a_2653_);
lean_del_object(v___x_2639_);
lean_dec(v_snd_2637_);
lean_del_object(v___x_2634_);
lean_del_object(v___x_2629_);
v_a_2676_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2658_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2658_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_del_object(v___x_2639_);
lean_dec(v_snd_2637_);
lean_dec(v_fst_2636_);
lean_del_object(v___x_2634_);
lean_del_object(v___x_2629_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v_letMuts_2612_);
v_a_2684_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2652_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2652_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2697_; 
lean_dec(v_a_2623_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v_letMuts_2612_);
lean_dec_ref(v_xs_2609_);
v___x_2695_ = lean_box(0);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2695_);
v___x_2697_ = v___x_2625_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v_letMuts_2612_);
lean_dec_ref(v_xs_2609_);
v_a_2700_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2622_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2622_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2708_, lean_object* v_inv_2709_, lean_object* v_xs_2710_, lean_object* v___x_2711_, lean_object* v___x_2712_, lean_object* v_letMuts_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v___x_93476__boxed_2723_; lean_object* v_res_2724_; 
v___x_93476__boxed_2723_ = lean_unbox(v___x_2711_);
v_res_2724_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2708_, v_inv_2709_, v_xs_2710_, v___x_93476__boxed_2723_, v___x_2712_, v_letMuts_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___x_2712_);
lean_dec_ref(v_a_2708_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = lean_apply_10(v_k_2725_, v_b_2730_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v_b_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v_b_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2749_, uint8_t v_bi_2750_, lean_object* v_type_2751_, lean_object* v_k_2752_, uint8_t v_kind_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___f_2763_; lean_object* v___x_2764_; 
v___f_2763_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2763_, 0, v_k_2752_);
lean_closure_set(v___f_2763_, 1, v___y_2754_);
lean_closure_set(v___f_2763_, 2, v___y_2755_);
lean_closure_set(v___f_2763_, 3, v___y_2756_);
lean_closure_set(v___f_2763_, 4, v___y_2757_);
v___x_2764_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2749_, v_bi_2750_, v_type_2751_, v___f_2763_, v_kind_2753_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2764_) == 0)
{
return v___x_2764_;
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2773_, lean_object* v_bi_2774_, lean_object* v_type_2775_, lean_object* v_k_2776_, lean_object* v_kind_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
uint8_t v_bi_boxed_2787_; uint8_t v_kind_boxed_2788_; lean_object* v_res_2789_; 
v_bi_boxed_2787_ = lean_unbox(v_bi_2774_);
v_kind_boxed_2788_ = lean_unbox(v_kind_2777_);
v_res_2789_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2773_, v_bi_boxed_2787_, v_type_2775_, v_k_2776_, v_kind_boxed_2788_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2790_, lean_object* v_type_2791_, lean_object* v_k_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
uint8_t v___x_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = 0;
v___x_2803_ = 0;
v___x_2804_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2790_, v___x_2802_, v_type_2791_, v_k_2792_, v___x_2803_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2805_, lean_object* v_type_2806_, lean_object* v_k_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2805_, v_type_2806_, v_k_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2821_, lean_object* v_inv_2822_, uint8_t v___x_2823_, lean_object* v___x_2824_, lean_object* v_arg_2825_, lean_object* v_xs_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2836_ = lean_box(v___x_2823_);
v___f_2837_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2837_, 0, v_a_2821_);
lean_closure_set(v___f_2837_, 1, v_inv_2822_);
lean_closure_set(v___f_2837_, 2, v_xs_2826_);
lean_closure_set(v___f_2837_, 3, v___x_2836_);
lean_closure_set(v___f_2837_, 4, v___x_2824_);
v___x_2838_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2839_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2838_, v_arg_2825_, v___f_2837_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2840_, lean_object* v_inv_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v_arg_2844_, lean_object* v_xs_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
uint8_t v___x_93796__boxed_2855_; lean_object* v_res_2856_; 
v___x_93796__boxed_2855_ = lean_unbox(v___x_2842_);
v_res_2856_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2840_, v_inv_2841_, v___x_93796__boxed_2855_, v___x_2843_, v_arg_2844_, v_xs_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
return v_res_2856_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2860_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = lean_unsigned_to_nat(32u);
v___x_2864_ = lean_mk_empty_array_with_capacity(v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2866_, lean_object* v_r_2867_, uint8_t v___x_2868_, lean_object* v___x_2869_, lean_object* v___x_2870_, lean_object* v_xs_2871_, lean_object* v_fst_2872_, lean_object* v_fst_2873_, lean_object* v_letMuts_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; 
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
lean_inc_ref(v_fst_2866_);
v___x_2884_ = l_Lean_Meta_mkNone(v_fst_2866_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref(v___x_2884_);
v___x_2886_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___closed__1));
v___x_2887_ = lean_unsigned_to_nat(2u);
v___x_2888_ = lean_mk_empty_array_with_capacity(v___x_2887_);
lean_inc_ref(v___x_2888_);
v___x_2889_ = lean_array_push(v___x_2888_, v_a_2885_);
lean_inc_ref(v_letMuts_2874_);
v___x_2890_ = lean_array_push(v___x_2889_, v_letMuts_2874_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
v___x_2891_ = l_Lean_Meta_mkAppM(v___x_2886_, v___x_2890_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
v___x_2893_ = l_Lean_Meta_mkSome(v_fst_2866_, v_r_2867_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2893_);
lean_inc_ref(v___x_2888_);
v___x_2895_ = lean_array_push(v___x_2888_, v_a_2894_);
v___x_2896_ = lean_array_push(v___x_2895_, v_letMuts_2874_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
v___x_2897_ = l_Lean_Meta_mkAppM(v___x_2886_, v___x_2896_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2882_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___x_2899_);
v___x_2901_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2882_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; uint8_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
v___x_2903_ = lean_unsigned_to_nat(100000u);
v___x_2904_ = 0;
v___x_2905_ = 0;
v___x_2906_ = lean_box(0);
v___x_2907_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2907_, 0, v___x_2903_);
lean_ctor_set(v___x_2907_, 1, v___x_2887_);
lean_ctor_set(v___x_2907_, 2, v___x_2906_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 1, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 2, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 3, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 4, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 5, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 6, v___x_2905_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 7, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 8, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 9, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 10, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 11, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 12, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 13, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 14, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 15, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 16, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 17, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 18, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 19, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 20, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 21, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 22, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 23, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 24, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 25, v___x_2868_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 26, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 27, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3 + 28, v___x_2904_);
v___x_2908_ = lean_mk_empty_array_with_capacity(v___x_2869_);
lean_inc_ref(v___x_2908_);
v___x_2909_ = lean_array_push(v___x_2908_, v_a_2900_);
v___x_2910_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2907_, v___x_2909_, v_a_2902_, v___y_2879_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
v___x_2912_ = lean_mk_empty_array_with_capacity(v___x_2870_);
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2914_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2912_, v___x_2913_, v___x_2904_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
v___x_2916_ = lean_array_push(v___x_2888_, v_xs_2871_);
v___x_2917_ = lean_array_push(v___x_2916_, v_a_2892_);
v___x_2918_ = l_Lean_Expr_beta(v_fst_2872_, v___x_2917_);
v___x_2919_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc(v___x_2870_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
lean_ctor_set(v___x_2920_, 1, v___x_2870_);
v___x_2921_ = lean_unsigned_to_nat(32u);
v___x_2922_ = lean_mk_empty_array_with_capacity(v___x_2921_);
v___x_2923_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2924_ = ((size_t)5ULL);
lean_inc(v___x_2870_);
v___x_2925_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2922_);
lean_ctor_set(v___x_2925_, 2, v___x_2870_);
lean_ctor_set(v___x_2925_, 3, v___x_2870_);
lean_ctor_set_usize(v___x_2925_, 4, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2919_);
lean_ctor_set(v___x_2926_, 1, v___x_2919_);
lean_ctor_set(v___x_2926_, 2, v___x_2919_);
lean_ctor_set(v___x_2926_, 3, v___x_2925_);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2920_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
lean_inc(v_a_2915_);
lean_inc(v_a_2911_);
v___x_2928_ = l_Lean_Meta_simp(v___x_2918_, v_a_2911_, v_a_2915_, v___x_2906_, v___x_2927_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v_fst_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref(v___x_2928_);
v_fst_2930_ = lean_ctor_get(v_a_2929_, 0);
lean_inc(v_fst_2930_);
lean_dec(v_a_2929_);
v___x_2931_ = lean_array_push(v___x_2908_, v_a_2898_);
v___x_2932_ = l_Lean_Expr_beta(v_fst_2873_, v___x_2931_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
v___x_2933_ = l_Lean_Meta_simp(v___x_2932_, v_a_2911_, v_a_2915_, v___x_2906_, v___x_2927_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec_ref(v___x_2927_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v_fst_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2972_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref(v___x_2933_);
v_fst_2935_ = lean_ctor_get(v_a_2934_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_a_2934_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; 
v_unused_2973_ = lean_ctor_get(v_a_2934_, 1);
lean_dec(v_unused_2973_);
v___x_2937_ = v_a_2934_;
v_isShared_2938_ = v_isSharedCheck_2972_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_fst_2935_);
lean_dec(v_a_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2972_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v_expr_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_expr_2939_ = lean_ctor_get(v_fst_2930_, 0);
lean_inc_ref(v_expr_2939_);
lean_dec(v_fst_2930_);
v___x_2940_ = lean_box(1);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
v___x_2941_ = l_Lean_PrettyPrinter_delab(v_expr_2939_, v___x_2940_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v_expr_2943_; lean_object* v___x_2944_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
v_expr_2943_ = lean_ctor_get(v_fst_2935_, 0);
lean_inc_ref(v_expr_2943_);
lean_dec(v_fst_2935_);
v___x_2944_ = l_Lean_PrettyPrinter_delab(v_expr_2943_, v___x_2940_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2955_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2955_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2955_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v_a_2945_);
lean_ctor_set(v___x_2937_, 0, v_a_2942_);
v___x_2950_ = v___x_2937_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2942_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2952_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2950_);
v___x_2952_ = v___x_2947_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_a_2942_);
lean_del_object(v___x_2937_);
v_a_2956_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2944_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2944_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_del_object(v___x_2937_);
lean_dec(v_fst_2935_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
v_a_2964_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2941_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2941_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v_fst_2930_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
v_a_2974_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2933_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2933_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
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
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref(v___x_2927_);
lean_dec(v_a_2915_);
lean_dec(v_a_2911_);
lean_dec_ref(v___x_2908_);
lean_dec(v_a_2898_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_fst_2873_);
v_a_2982_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2928_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2928_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v_a_2911_);
lean_dec_ref(v___x_2908_);
lean_dec(v_a_2898_);
lean_dec(v_a_2892_);
lean_dec_ref(v___x_2888_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_fst_2873_);
lean_dec_ref(v_fst_2872_);
lean_dec_ref(v_xs_2871_);
lean_dec(v___x_2870_);
v_a_2990_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2914_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2914_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v___x_2908_);
lean_dec(v_a_2898_);
lean_dec(v_a_2892_);
lean_dec_ref(v___x_2888_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_fst_2873_);
lean_dec_ref(v_fst_2872_);
lean_dec_ref(v_xs_2871_);
lean_dec(v___x_2870_);
v_a_2998_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2910_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2910_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v_a_2900_);
lean_dec(v_a_2898_);
lean_dec(v_a_2892_);
lean_dec_ref(v___x_2888_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_fst_2873_);
lean_dec_ref(v_fst_2872_);
lean_dec_ref(v_xs_2871_);
lean_dec(v___x_2870_);
v_a_3006_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2901_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2901_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_a_2898_);
lean_dec(v_a_2892_);
lean_dec_ref(v___x_2888_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_fst_2873_);
lean_dec_ref(v_fst_2872_);
lean_dec_ref(v_xs_2871_);
lean_dec(v___x_2870_);
v_a_3014_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2899_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2899_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_2892_);
lean_dec_ref(v___x_2888_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_fst_2873_);
lean_dec_ref(v_fst_2872_);
lean_dec_ref(v_xs_2871_);
lean_dec(v___x_2870_);
v_a_3022_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2897_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2897_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v_a_2892_);
lean_dec_ref(v___x_2888_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_letMuts_2874_);
lean_dec_ref(v_fst_2873_);
lean_dec_ref(v_fst_2872_);
lean_dec_ref(v_xs_2871_);
lean_dec(v___x_2870_);
v_a_3030_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2893_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2893_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___x_2888_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_letMuts_2874_);
lean_dec_ref(v_fst_2873_);
lean_dec_ref(v_fst_2872_);
lean_dec_ref(v_xs_2871_);
lean_dec(v___x_2870_);
lean_dec_ref(v_r_2867_);
lean_dec_ref(v_fst_2866_);
v_a_3038_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2891_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2891_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_letMuts_2874_);
lean_dec_ref(v_fst_2873_);
lean_dec_ref(v_fst_2872_);
lean_dec_ref(v_xs_2871_);
lean_dec(v___x_2870_);
lean_dec_ref(v_r_2867_);
lean_dec_ref(v_fst_2866_);
v_a_3046_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_2884_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_2884_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3054_ = _args[0];
lean_object* v_r_3055_ = _args[1];
lean_object* v___x_3056_ = _args[2];
lean_object* v___x_3057_ = _args[3];
lean_object* v___x_3058_ = _args[4];
lean_object* v_xs_3059_ = _args[5];
lean_object* v_fst_3060_ = _args[6];
lean_object* v_fst_3061_ = _args[7];
lean_object* v_letMuts_3062_ = _args[8];
lean_object* v___y_3063_ = _args[9];
lean_object* v___y_3064_ = _args[10];
lean_object* v___y_3065_ = _args[11];
lean_object* v___y_3066_ = _args[12];
lean_object* v___y_3067_ = _args[13];
lean_object* v___y_3068_ = _args[14];
lean_object* v___y_3069_ = _args[15];
lean_object* v___y_3070_ = _args[16];
lean_object* v___y_3071_ = _args[17];
_start:
{
uint8_t v___x_93869__boxed_3072_; lean_object* v_res_3073_; 
v___x_93869__boxed_3072_ = lean_unbox(v___x_3056_);
v_res_3073_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3054_, v_r_3055_, v___x_93869__boxed_3072_, v___x_3057_, v___x_3058_, v_xs_3059_, v_fst_3060_, v_fst_3061_, v_letMuts_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___x_3057_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3074_, uint8_t v___x_3075_, lean_object* v___x_3076_, lean_object* v___x_3077_, lean_object* v_xs_3078_, lean_object* v_fst_3079_, lean_object* v_fst_3080_, lean_object* v_snd_3081_, lean_object* v_r_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v___x_3092_; lean_object* v___f_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3092_ = lean_box(v___x_3075_);
v___f_3093_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3093_, 0, v_fst_3074_);
lean_closure_set(v___f_3093_, 1, v_r_3082_);
lean_closure_set(v___f_3093_, 2, v___x_3092_);
lean_closure_set(v___f_3093_, 3, v___x_3076_);
lean_closure_set(v___f_3093_, 4, v___x_3077_);
lean_closure_set(v___f_3093_, 5, v_xs_3078_);
lean_closure_set(v___f_3093_, 6, v_fst_3079_);
lean_closure_set(v___f_3093_, 7, v_fst_3080_);
v___x_3094_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3095_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3094_, v_snd_3081_, v___f_3093_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3096_ = _args[0];
lean_object* v___x_3097_ = _args[1];
lean_object* v___x_3098_ = _args[2];
lean_object* v___x_3099_ = _args[3];
lean_object* v_xs_3100_ = _args[4];
lean_object* v_fst_3101_ = _args[5];
lean_object* v_fst_3102_ = _args[6];
lean_object* v_snd_3103_ = _args[7];
lean_object* v_r_3104_ = _args[8];
lean_object* v___y_3105_ = _args[9];
lean_object* v___y_3106_ = _args[10];
lean_object* v___y_3107_ = _args[11];
lean_object* v___y_3108_ = _args[12];
lean_object* v___y_3109_ = _args[13];
lean_object* v___y_3110_ = _args[14];
lean_object* v___y_3111_ = _args[15];
lean_object* v___y_3112_ = _args[16];
lean_object* v___y_3113_ = _args[17];
_start:
{
uint8_t v___x_94263__boxed_3114_; lean_object* v_res_3115_; 
v___x_94263__boxed_3114_ = lean_unbox(v___x_3097_);
v_res_3115_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3096_, v___x_94263__boxed_3114_, v___x_3098_, v___x_3099_, v_xs_3100_, v_fst_3101_, v_fst_3102_, v_snd_3103_, v_r_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3119_, uint8_t v___x_3120_, lean_object* v___x_3121_, lean_object* v___x_3122_, lean_object* v_fst_3123_, lean_object* v_fst_3124_, lean_object* v_snd_3125_, lean_object* v_xs_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; lean_object* v___f_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3136_ = lean_box(v___x_3120_);
lean_inc_ref(v_fst_3119_);
v___f_3137_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3137_, 0, v_fst_3119_);
lean_closure_set(v___f_3137_, 1, v___x_3136_);
lean_closure_set(v___f_3137_, 2, v___x_3121_);
lean_closure_set(v___f_3137_, 3, v___x_3122_);
lean_closure_set(v___f_3137_, 4, v_xs_3126_);
lean_closure_set(v___f_3137_, 5, v_fst_3123_);
lean_closure_set(v___f_3137_, 6, v_fst_3124_);
lean_closure_set(v___f_3137_, 7, v_snd_3125_);
v___x_3138_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3139_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3138_, v_fst_3119_, v___f_3137_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3140_ = _args[0];
lean_object* v___x_3141_ = _args[1];
lean_object* v___x_3142_ = _args[2];
lean_object* v___x_3143_ = _args[3];
lean_object* v_fst_3144_ = _args[4];
lean_object* v_fst_3145_ = _args[5];
lean_object* v_snd_3146_ = _args[6];
lean_object* v_xs_3147_ = _args[7];
lean_object* v___y_3148_ = _args[8];
lean_object* v___y_3149_ = _args[9];
lean_object* v___y_3150_ = _args[10];
lean_object* v___y_3151_ = _args[11];
lean_object* v___y_3152_ = _args[12];
lean_object* v___y_3153_ = _args[13];
lean_object* v___y_3154_ = _args[14];
lean_object* v___y_3155_ = _args[15];
lean_object* v___y_3156_ = _args[16];
_start:
{
uint8_t v___x_94326__boxed_3157_; lean_object* v_res_3158_; 
v___x_94326__boxed_3157_ = lean_unbox(v___x_3141_);
v_res_3158_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3140_, v___x_94326__boxed_3157_, v___x_3142_, v___x_3143_, v_fst_3144_, v_fst_3145_, v_snd_3146_, v_xs_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3159_, size_t v_sz_3160_, size_t v_i_3161_, lean_object* v_b_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_usize_dec_lt(v_i_3161_, v_sz_3160_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; 
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_b_3162_);
return v___x_3169_;
}
else
{
lean_object* v___x_3170_; lean_object* v_a_3171_; lean_object* v___x_3172_; 
v___x_3170_ = lean_box(1);
v_a_3171_ = lean_array_uget_borrowed(v_as_3159_, v_i_3161_);
lean_inc(v___y_3166_);
lean_inc_ref(v___y_3165_);
lean_inc(v___y_3164_);
lean_inc_ref(v___y_3163_);
lean_inc(v_a_3171_);
v___x_3172_ = l_Lean_PrettyPrinter_delab(v_a_3171_, v___x_3170_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3174_; size_t v___x_3175_; size_t v___x_3176_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref(v___x_3172_);
v___x_3174_ = lean_array_push(v_b_3162_, v_a_3173_);
v___x_3175_ = ((size_t)1ULL);
v___x_3176_ = lean_usize_add(v_i_3161_, v___x_3175_);
v_i_3161_ = v___x_3176_;
v_b_3162_ = v___x_3174_;
goto _start;
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v_b_3162_);
v_a_3178_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3172_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3172_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3186_, lean_object* v_sz_3187_, lean_object* v_i_3188_, lean_object* v_b_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
size_t v_sz_boxed_3195_; size_t v_i_boxed_3196_; lean_object* v_res_3197_; 
v_sz_boxed_3195_ = lean_unbox_usize(v_sz_3187_);
lean_dec(v_sz_3187_);
v_i_boxed_3196_ = lean_unbox_usize(v_i_3188_);
lean_dec(v_i_3188_);
v_res_3197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3186_, v_sz_boxed_3195_, v_i_boxed_3196_, v_b_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec_ref(v_as_3186_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3218_, lean_object* v_fst_3219_, lean_object* v_snd_3220_, lean_object* v___x_3221_, lean_object* v___x_3222_, lean_object* v___x_3223_, lean_object* v___x_3224_, lean_object* v___x_3225_, lean_object* v___x_3226_, lean_object* v___x_3227_, uint8_t v___x_3228_, lean_object* v___x_3229_, lean_object* v_letMuts_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3240_ = lean_unsigned_to_nat(2u);
v___x_3241_ = lean_mk_empty_array_with_capacity(v___x_3240_);
v___x_3242_ = lean_array_push(v___x_3241_, v_xs_3218_);
v___x_3243_ = lean_array_push(v___x_3242_, v_letMuts_3230_);
v___x_3244_ = l_Lean_Expr_beta(v_fst_3219_, v___x_3243_);
v___x_3245_ = lean_box(1);
lean_inc(v___y_3238_);
lean_inc_ref(v___y_3237_);
lean_inc(v___y_3236_);
lean_inc_ref(v___y_3235_);
v___x_3246_ = l_Lean_PrettyPrinter_delab(v___x_3244_, v___x_3245_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3385_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3385_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3385_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
uint8_t v___y_3252_; lean_object* v_points_3288_; lean_object* v_default_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3384_; 
v_points_3288_ = lean_ctor_get(v_snd_3220_, 0);
v_default_3289_ = lean_ctor_get(v_snd_3220_, 1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_snd_3220_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3291_ = v_snd_3220_;
v_isShared_3292_ = v_isSharedCheck_3384_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_default_3289_);
lean_inc(v_points_3288_);
lean_dec(v_snd_3220_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3384_;
goto v_resetjp_3290_;
}
v___jp_3251_:
{
lean_object* v_ref_3253_; lean_object* v_quotContext_3254_; lean_object* v_currMacroScope_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v_ref_3253_ = lean_ctor_get(v___y_3237_, 5);
lean_inc(v_ref_3253_);
v_quotContext_3254_ = lean_ctor_get(v___y_3237_, 10);
lean_inc(v_quotContext_3254_);
v_currMacroScope_3255_ = lean_ctor_get(v___y_3237_, 11);
lean_inc(v_currMacroScope_3255_);
lean_dec_ref(v___y_3237_);
v___x_3256_ = l_Lean_SourceInfo_fromRef(v_ref_3253_, v___y_3252_);
lean_dec(v_ref_3253_);
v___x_3257_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3258_ = l_Lean_Name_mkStr3(v___x_3221_, v___x_3222_, v___x_3257_);
v___x_3259_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3260_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_3256_);
v___x_3261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3256_);
lean_ctor_set(v___x_3261_, 1, v___x_3259_);
lean_ctor_set(v___x_3261_, 2, v___x_3260_);
v___x_3262_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
lean_inc(v___x_3256_);
v___x_3263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3256_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc(v___x_3256_);
v___x_3267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3256_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = l_String_toRawSubstring_x27(v___x_3223_);
lean_inc(v_currMacroScope_3255_);
lean_inc(v_quotContext_3254_);
v___x_3269_ = l_Lean_addMacroScope(v_quotContext_3254_, v___x_3224_, v_currMacroScope_3255_);
v___x_3270_ = lean_box(0);
lean_inc(v___x_3256_);
v___x_3271_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3256_);
lean_ctor_set(v___x_3271_, 1, v___x_3268_);
lean_ctor_set(v___x_3271_, 2, v___x_3269_);
lean_ctor_set(v___x_3271_, 3, v___x_3270_);
v___x_3272_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
lean_inc(v___x_3256_);
v___x_3273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3256_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = l_String_toRawSubstring_x27(v___x_3225_);
v___x_3275_ = l_Lean_addMacroScope(v_quotContext_3254_, v___x_3226_, v_currMacroScope_3255_);
lean_inc(v___x_3256_);
v___x_3276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3256_);
lean_ctor_set(v___x_3276_, 1, v___x_3274_);
lean_ctor_set(v___x_3276_, 2, v___x_3275_);
lean_ctor_set(v___x_3276_, 3, v___x_3270_);
lean_inc(v___x_3256_);
v___x_3277_ = l_Lean_Syntax_node3(v___x_3256_, v___x_3264_, v___x_3271_, v___x_3273_, v___x_3276_);
v___x_3278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
lean_inc(v___x_3256_);
v___x_3279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3256_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
lean_inc(v___x_3256_);
v___x_3280_ = l_Lean_Syntax_node3(v___x_3256_, v___x_3265_, v___x_3267_, v___x_3277_, v___x_3279_);
lean_inc(v___x_3256_);
v___x_3281_ = l_Lean_Syntax_node1(v___x_3256_, v___x_3264_, v___x_3280_);
v___x_3282_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_3256_);
v___x_3283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3256_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = l_Lean_Syntax_node5(v___x_3256_, v___x_3258_, v___x_3261_, v___x_3263_, v___x_3281_, v___x_3283_, v_a_3247_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3284_);
v___x_3286_ = v___x_3249_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
v_resetjp_3290_:
{
uint8_t v___y_3294_; uint8_t v___y_3345_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3381_ = lean_array_get_size(v_points_3288_);
v___x_3382_ = lean_nat_dec_eq(v___x_3381_, v___x_3229_);
if (v___x_3382_ == 0)
{
v___y_3345_ = v___x_3382_;
goto v___jp_3344_;
}
else
{
if (lean_obj_tag(v_default_3289_) == 3)
{
if (v___x_3382_ == 0)
{
v___y_3345_ = v___x_3382_;
goto v___jp_3344_;
}
else
{
uint8_t v___x_3383_; 
lean_del_object(v___x_3249_);
lean_dec_ref(v___x_3222_);
lean_dec_ref(v___x_3221_);
v___x_3383_ = 0;
v___y_3294_ = v___x_3383_;
goto v___jp_3293_;
}
}
else
{
v___y_3345_ = v___x_3382_;
goto v___jp_3344_;
}
}
v___jp_3293_:
{
lean_object* v_ref_3295_; lean_object* v_quotContext_3296_; lean_object* v_currMacroScope_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v_ref_3295_ = lean_ctor_get(v___y_3237_, 5);
v_quotContext_3296_ = lean_ctor_get(v___y_3237_, 10);
v_currMacroScope_3297_ = lean_ctor_get(v___y_3237_, 11);
v___x_3298_ = l_Lean_SourceInfo_fromRef(v_ref_3295_, v___y_3294_);
v___x_3299_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3300_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3298_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 2);
lean_ctor_set(v___x_3291_, 1, v___x_3299_);
lean_ctor_set(v___x_3291_, 0, v___x_3298_);
v___x_3302_ = v___x_3291_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v___x_3299_);
v___x_3302_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; size_t v_sz_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc(v___x_3298_);
v___x_3307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3298_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_String_toRawSubstring_x27(v___x_3223_);
lean_inc(v_currMacroScope_3297_);
lean_inc(v_quotContext_3296_);
v___x_3309_ = l_Lean_addMacroScope(v_quotContext_3296_, v___x_3224_, v_currMacroScope_3297_);
v___x_3310_ = lean_box(0);
lean_inc(v___x_3298_);
v___x_3311_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3298_);
lean_ctor_set(v___x_3311_, 1, v___x_3308_);
lean_ctor_set(v___x_3311_, 2, v___x_3309_);
lean_ctor_set(v___x_3311_, 3, v___x_3310_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
lean_inc(v___x_3298_);
v___x_3313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3298_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = l_String_toRawSubstring_x27(v___x_3225_);
lean_inc(v_currMacroScope_3297_);
lean_inc(v_quotContext_3296_);
v___x_3315_ = l_Lean_addMacroScope(v_quotContext_3296_, v___x_3226_, v_currMacroScope_3297_);
lean_inc(v___x_3298_);
v___x_3316_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3298_);
lean_ctor_set(v___x_3316_, 1, v___x_3314_);
lean_ctor_set(v___x_3316_, 2, v___x_3315_);
lean_ctor_set(v___x_3316_, 3, v___x_3310_);
lean_inc(v___x_3298_);
v___x_3317_ = l_Lean_Syntax_node3(v___x_3298_, v___x_3304_, v___x_3311_, v___x_3313_, v___x_3316_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
lean_inc(v___x_3298_);
v___x_3319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3298_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
lean_inc(v___x_3298_);
v___x_3320_ = l_Lean_Syntax_node3(v___x_3298_, v___x_3305_, v___x_3307_, v___x_3317_, v___x_3319_);
lean_inc(v___x_3298_);
v___x_3321_ = l_Lean_Syntax_node1(v___x_3298_, v___x_3304_, v___x_3320_);
v___x_3322_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_3298_);
v___x_3323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3298_);
lean_ctor_set(v___x_3323_, 1, v___x_3304_);
lean_ctor_set(v___x_3323_, 2, v___x_3322_);
v___x_3324_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_3298_);
v___x_3325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3298_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
lean_inc(v___x_3298_);
v___x_3326_ = l_Lean_Syntax_node4(v___x_3298_, v___x_3303_, v___x_3321_, v___x_3323_, v___x_3325_, v_a_3247_);
v___x_3327_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3300_, v___x_3302_, v___x_3326_);
v___x_3328_ = lean_mk_empty_array_with_capacity(v___x_3227_);
v___x_3329_ = lean_array_push(v___x_3328_, v___x_3327_);
v_sz_3330_ = lean_array_size(v_points_3288_);
v___x_3331_ = ((size_t)0ULL);
lean_inc(v___y_3238_);
lean_inc_ref(v___y_3237_);
lean_inc(v___y_3236_);
lean_inc_ref(v___y_3235_);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3288_, v_sz_3330_, v___x_3331_, v___x_3329_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec_ref(v_points_3288_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3333_, v_default_3289_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v_a_3333_);
return v___x_3334_;
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_default_3289_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
v_a_3335_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3332_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3332_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
v___jp_3344_:
{
if (v___y_3345_ == 0)
{
lean_del_object(v___x_3249_);
lean_dec_ref(v___x_3222_);
lean_dec_ref(v___x_3221_);
v___y_3294_ = v___y_3345_;
goto v___jp_3293_;
}
else
{
lean_del_object(v___x_3291_);
lean_dec_ref(v_points_3288_);
lean_dec(v___y_3238_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
if (lean_obj_tag(v_default_3289_) == 2)
{
if (v___x_3228_ == 0)
{
v___y_3252_ = v___x_3228_;
goto v___jp_3251_;
}
else
{
lean_object* v_ref_3346_; lean_object* v_quotContext_3347_; lean_object* v_currMacroScope_3348_; uint8_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
lean_del_object(v___x_3249_);
v_ref_3346_ = lean_ctor_get(v___y_3237_, 5);
lean_inc(v_ref_3346_);
v_quotContext_3347_ = lean_ctor_get(v___y_3237_, 10);
lean_inc(v_quotContext_3347_);
v_currMacroScope_3348_ = lean_ctor_get(v___y_3237_, 11);
lean_inc(v_currMacroScope_3348_);
lean_dec_ref(v___y_3237_);
v___x_3349_ = 0;
v___x_3350_ = l_Lean_SourceInfo_fromRef(v_ref_3346_, v___x_3349_);
lean_dec(v_ref_3346_);
v___x_3351_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3352_ = l_Lean_Name_mkStr3(v___x_3221_, v___x_3222_, v___x_3351_);
v___x_3353_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3354_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_3350_);
v___x_3355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3350_);
lean_ctor_set(v___x_3355_, 1, v___x_3353_);
lean_ctor_set(v___x_3355_, 2, v___x_3354_);
v___x_3356_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
lean_inc(v___x_3350_);
v___x_3357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3350_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc(v___x_3350_);
v___x_3361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3350_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = l_String_toRawSubstring_x27(v___x_3223_);
lean_inc(v_currMacroScope_3348_);
lean_inc(v_quotContext_3347_);
v___x_3363_ = l_Lean_addMacroScope(v_quotContext_3347_, v___x_3224_, v_currMacroScope_3348_);
v___x_3364_ = lean_box(0);
lean_inc(v___x_3350_);
v___x_3365_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3350_);
lean_ctor_set(v___x_3365_, 1, v___x_3362_);
lean_ctor_set(v___x_3365_, 2, v___x_3363_);
lean_ctor_set(v___x_3365_, 3, v___x_3364_);
v___x_3366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
lean_inc(v___x_3350_);
v___x_3367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3350_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = l_String_toRawSubstring_x27(v___x_3225_);
v___x_3369_ = l_Lean_addMacroScope(v_quotContext_3347_, v___x_3226_, v_currMacroScope_3348_);
lean_inc(v___x_3350_);
v___x_3370_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3350_);
lean_ctor_set(v___x_3370_, 1, v___x_3368_);
lean_ctor_set(v___x_3370_, 2, v___x_3369_);
lean_ctor_set(v___x_3370_, 3, v___x_3364_);
lean_inc(v___x_3350_);
v___x_3371_ = l_Lean_Syntax_node3(v___x_3350_, v___x_3358_, v___x_3365_, v___x_3367_, v___x_3370_);
v___x_3372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
lean_inc(v___x_3350_);
v___x_3373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3350_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
lean_inc(v___x_3350_);
v___x_3374_ = l_Lean_Syntax_node3(v___x_3350_, v___x_3359_, v___x_3361_, v___x_3371_, v___x_3373_);
lean_inc(v___x_3350_);
v___x_3375_ = l_Lean_Syntax_node1(v___x_3350_, v___x_3358_, v___x_3374_);
v___x_3376_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_3350_);
v___x_3377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3350_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = l_Lean_Syntax_node5(v___x_3350_, v___x_3352_, v___x_3355_, v___x_3357_, v___x_3375_, v___x_3377_, v_a_3247_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
}
else
{
uint8_t v___x_3380_; 
lean_dec(v_default_3289_);
v___x_3380_ = 0;
v___y_3252_ = v___x_3380_;
goto v___jp_3251_;
}
}
}
}
}
}
else
{
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___x_3226_);
lean_dec_ref(v___x_3225_);
lean_dec(v___x_3224_);
lean_dec_ref(v___x_3223_);
lean_dec_ref(v___x_3222_);
lean_dec_ref(v___x_3221_);
lean_dec_ref(v_snd_3220_);
return v___x_3246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3386_ = _args[0];
lean_object* v_fst_3387_ = _args[1];
lean_object* v_snd_3388_ = _args[2];
lean_object* v___x_3389_ = _args[3];
lean_object* v___x_3390_ = _args[4];
lean_object* v___x_3391_ = _args[5];
lean_object* v___x_3392_ = _args[6];
lean_object* v___x_3393_ = _args[7];
lean_object* v___x_3394_ = _args[8];
lean_object* v___x_3395_ = _args[9];
lean_object* v___x_3396_ = _args[10];
lean_object* v___x_3397_ = _args[11];
lean_object* v_letMuts_3398_ = _args[12];
lean_object* v___y_3399_ = _args[13];
lean_object* v___y_3400_ = _args[14];
lean_object* v___y_3401_ = _args[15];
lean_object* v___y_3402_ = _args[16];
lean_object* v___y_3403_ = _args[17];
lean_object* v___y_3404_ = _args[18];
lean_object* v___y_3405_ = _args[19];
lean_object* v___y_3406_ = _args[20];
lean_object* v___y_3407_ = _args[21];
_start:
{
uint8_t v___x_94535__boxed_3408_; lean_object* v_res_3409_; 
v___x_94535__boxed_3408_ = lean_unbox(v___x_3396_);
v_res_3409_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3386_, v_fst_3387_, v_snd_3388_, v___x_3389_, v___x_3390_, v___x_3391_, v___x_3392_, v___x_3393_, v___x_3394_, v___x_3395_, v___x_94535__boxed_3408_, v___x_3397_, v_letMuts_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___x_3397_);
lean_dec(v___x_3395_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3410_, lean_object* v_snd_3411_, lean_object* v___x_3412_, lean_object* v___x_3413_, lean_object* v___x_3414_, lean_object* v___x_3415_, lean_object* v___x_3416_, uint8_t v___x_3417_, lean_object* v___x_3418_, lean_object* v_arg_3419_, lean_object* v_xs_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___f_3433_; lean_object* v___x_3434_; 
v___x_3430_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3431_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3432_ = lean_box(v___x_3417_);
v___f_3433_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3433_, 0, v_xs_3420_);
lean_closure_set(v___f_3433_, 1, v_fst_3410_);
lean_closure_set(v___f_3433_, 2, v_snd_3411_);
lean_closure_set(v___f_3433_, 3, v___x_3412_);
lean_closure_set(v___f_3433_, 4, v___x_3413_);
lean_closure_set(v___f_3433_, 5, v___x_3414_);
lean_closure_set(v___f_3433_, 6, v___x_3415_);
lean_closure_set(v___f_3433_, 7, v___x_3430_);
lean_closure_set(v___f_3433_, 8, v___x_3431_);
lean_closure_set(v___f_3433_, 9, v___x_3416_);
lean_closure_set(v___f_3433_, 10, v___x_3432_);
lean_closure_set(v___f_3433_, 11, v___x_3418_);
v___x_3434_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3431_, v_arg_3419_, v___f_3433_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3435_ = _args[0];
lean_object* v_snd_3436_ = _args[1];
lean_object* v___x_3437_ = _args[2];
lean_object* v___x_3438_ = _args[3];
lean_object* v___x_3439_ = _args[4];
lean_object* v___x_3440_ = _args[5];
lean_object* v___x_3441_ = _args[6];
lean_object* v___x_3442_ = _args[7];
lean_object* v___x_3443_ = _args[8];
lean_object* v_arg_3444_ = _args[9];
lean_object* v_xs_3445_ = _args[10];
lean_object* v___y_3446_ = _args[11];
lean_object* v___y_3447_ = _args[12];
lean_object* v___y_3448_ = _args[13];
lean_object* v___y_3449_ = _args[14];
lean_object* v___y_3450_ = _args[15];
lean_object* v___y_3451_ = _args[16];
lean_object* v___y_3452_ = _args[17];
lean_object* v___y_3453_ = _args[18];
lean_object* v___y_3454_ = _args[19];
_start:
{
uint8_t v___x_94885__boxed_3455_; lean_object* v_res_3456_; 
v___x_94885__boxed_3455_ = lean_unbox(v___x_3442_);
v_res_3456_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3435_, v_snd_3436_, v___x_3437_, v___x_3438_, v___x_3439_, v___x_3440_, v___x_3441_, v___x_94885__boxed_3455_, v___x_3443_, v_arg_3444_, v_xs_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3457_, size_t v_sz_3458_, size_t v_i_3459_, lean_object* v_b_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
uint8_t v___x_3466_; 
v___x_3466_ = lean_usize_dec_lt(v_i_3459_, v_sz_3458_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_b_3460_);
return v___x_3467_;
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_a_3468_ = lean_array_uget_borrowed(v_as_3457_, v_i_3459_);
v___x_3469_ = lean_box(1);
lean_inc(v___y_3464_);
lean_inc_ref(v___y_3463_);
lean_inc(v___y_3462_);
lean_inc_ref(v___y_3461_);
lean_inc(v_a_3468_);
v___x_3470_ = l_Lean_PrettyPrinter_delab(v_a_3468_, v___x_3469_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3472_; size_t v___x_3473_; size_t v___x_3474_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = lean_array_push(v_b_3460_, v_a_3471_);
v___x_3473_ = ((size_t)1ULL);
v___x_3474_ = lean_usize_add(v_i_3459_, v___x_3473_);
v_i_3459_ = v___x_3474_;
v_b_3460_ = v___x_3472_;
goto _start;
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v_b_3460_);
v_a_3476_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3470_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3470_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3484_, lean_object* v_sz_3485_, lean_object* v_i_3486_, lean_object* v_b_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
size_t v_sz_boxed_3493_; size_t v_i_boxed_3494_; lean_object* v_res_3495_; 
v_sz_boxed_3493_ = lean_unbox_usize(v_sz_3485_);
lean_dec(v_sz_3485_);
v_i_boxed_3494_ = lean_unbox_usize(v_i_3486_);
lean_dec(v_i_3486_);
v_res_3495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3484_, v_sz_boxed_3493_, v_i_boxed_3494_, v_b_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
lean_dec_ref(v_as_3484_);
return v_res_3495_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3504_ = l_String_toRawSubstring_x27(v___x_3503_);
return v___x_3504_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3515_ = l_String_toRawSubstring_x27(v___x_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3520_ = l_String_toRawSubstring_x27(v___x_3519_);
return v___x_3520_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3522_ = l_String_toRawSubstring_x27(v___x_3521_);
return v___x_3522_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3526_ = l_String_toRawSubstring_x27(v___x_3525_);
return v___x_3526_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3531_ = l_String_toRawSubstring_x27(v___x_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3541_, lean_object* v___x_3542_, lean_object* v___f_3543_, lean_object* v_a_3544_, lean_object* v_inv_3545_, lean_object* v_arg_3546_, uint8_t v___x_3547_, lean_object* v___x_3548_, lean_object* v___x_3549_, lean_object* v___x_3550_, lean_object* v___x_3551_, lean_object* v___x_3552_, lean_object* v___x_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_a_3564_; lean_object* v___y_3568_; lean_object* v___x_3570_; 
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
lean_inc(v___y_3559_);
lean_inc_ref(v___y_3558_);
lean_inc(v___y_3557_);
lean_inc_ref(v___y_3556_);
lean_inc(v___y_3555_);
lean_inc_ref(v___y_3554_);
lean_inc_ref(v___x_3542_);
lean_inc(v___x_3541_);
v___x_3570_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3541_, v___x_3542_, v___f_3543_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3570_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
lean_inc(v___y_3559_);
lean_inc_ref(v___y_3558_);
v___x_3572_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3544_, v_inv_3545_, v_arg_3546_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___x_3572_);
if (lean_obj_tag(v_a_3573_) == 1)
{
lean_object* v_val_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_4054_; 
lean_dec_ref(v_arg_3546_);
v_val_3574_ = lean_ctor_get(v_a_3573_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v_a_3573_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_3576_ = v_a_3573_;
v_isShared_3577_ = v_isSharedCheck_4054_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_val_3574_);
lean_dec(v_a_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_4054_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
if (lean_obj_tag(v_a_3571_) == 1)
{
lean_object* v_val_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3977_; 
lean_del_object(v___x_3576_);
v_val_3578_ = lean_ctor_get(v_a_3571_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_a_3571_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3580_ = v_a_3571_;
v_isShared_3581_ = v_isSharedCheck_3977_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_val_3578_);
lean_dec(v_a_3571_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3977_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_snd_3582_; lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3976_; 
v_snd_3582_ = lean_ctor_get(v_val_3578_, 1);
lean_inc(v_snd_3582_);
v_fst_3583_ = lean_ctor_get(v_val_3574_, 0);
v_snd_3584_ = lean_ctor_get(v_val_3574_, 1);
v_isSharedCheck_3976_ = !lean_is_exclusive(v_val_3574_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3586_ = v_val_3574_;
v_isShared_3587_ = v_isSharedCheck_3976_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_snd_3584_);
lean_inc(v_fst_3583_);
lean_dec(v_val_3574_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3976_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v_fst_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3974_; 
v_fst_3588_ = lean_ctor_get(v_val_3578_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_val_3578_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; 
v_unused_3975_ = lean_ctor_get(v_val_3578_, 1);
lean_dec(v_unused_3975_);
v___x_3590_ = v_val_3578_;
v_isShared_3591_ = v_isSharedCheck_3974_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_fst_3588_);
lean_dec(v_val_3578_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3974_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v_fst_3592_; lean_object* v_snd_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3973_; 
v_fst_3592_ = lean_ctor_get(v_snd_3582_, 0);
v_snd_3593_ = lean_ctor_get(v_snd_3582_, 1);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_snd_3582_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3595_ = v_snd_3582_;
v_isShared_3596_ = v_isSharedCheck_3973_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_snd_3593_);
lean_inc(v_fst_3592_);
lean_dec(v_snd_3582_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3973_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3597_; lean_object* v___f_3598_; lean_object* v___x_3599_; 
v___x_3597_ = lean_box(v___x_3547_);
lean_inc(v___x_3549_);
v___f_3598_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3598_, 0, v_fst_3583_);
lean_closure_set(v___f_3598_, 1, v___x_3597_);
lean_closure_set(v___f_3598_, 2, v___x_3548_);
lean_closure_set(v___f_3598_, 3, v___x_3549_);
lean_closure_set(v___f_3598_, 4, v_fst_3588_);
lean_closure_set(v___f_3598_, 5, v_fst_3592_);
lean_closure_set(v___f_3598_, 6, v_snd_3584_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
lean_inc(v___y_3559_);
lean_inc_ref(v___y_3558_);
lean_inc(v___x_3541_);
v___x_3599_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3541_, v___x_3542_, v___f_3598_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v_fst_3601_; lean_object* v_snd_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3964_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref(v___x_3599_);
v_fst_3601_ = lean_ctor_get(v_a_3600_, 0);
v_snd_3602_ = lean_ctor_get(v_a_3600_, 1);
v_isSharedCheck_3964_ = !lean_is_exclusive(v_a_3600_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3604_ = v_a_3600_;
v_isShared_3605_ = v_isSharedCheck_3964_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_snd_3602_);
lean_inc(v_fst_3601_);
lean_dec(v_a_3600_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3964_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v_points_3606_; lean_object* v_default_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3963_; 
v_points_3606_ = lean_ctor_get(v_snd_3593_, 0);
v_default_3607_ = lean_ctor_get(v_snd_3593_, 1);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_snd_3593_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3609_ = v_snd_3593_;
v_isShared_3610_ = v_isSharedCheck_3963_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_default_3607_);
lean_inc(v_points_3606_);
lean_dec(v_snd_3593_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3963_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3611_ = lean_array_get_size(v_points_3606_);
v___x_3612_ = lean_nat_dec_eq(v___x_3611_, v___x_3549_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; size_t v_sz_3614_; size_t v___x_3615_; lean_object* v___x_3616_; 
lean_del_object(v___x_3580_);
v___x_3613_ = lean_mk_empty_array_with_capacity(v___x_3549_);
lean_dec(v___x_3549_);
v_sz_3614_ = lean_array_size(v_points_3606_);
v___x_3615_ = ((size_t)0ULL);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
lean_inc(v___y_3559_);
lean_inc_ref(v___y_3558_);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3606_, v_sz_3614_, v___x_3615_, v___x_3613_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec_ref(v_points_3606_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref(v___x_3616_);
lean_inc_ref(v___y_3560_);
v___x_3618_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3617_, v_default_3607_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v_a_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3701_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3621_ = v___x_3618_;
v_isShared_3622_ = v_isSharedCheck_3701_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3701_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v_ref_3623_; lean_object* v_quotContext_3624_; lean_object* v_currMacroScope_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v_ref_3623_ = lean_ctor_get(v___y_3560_, 5);
lean_inc(v_ref_3623_);
v_quotContext_3624_ = lean_ctor_get(v___y_3560_, 10);
lean_inc(v_quotContext_3624_);
v_currMacroScope_3625_ = lean_ctor_get(v___y_3560_, 11);
lean_inc(v_currMacroScope_3625_);
lean_dec_ref(v___y_3560_);
v___x_3626_ = l_Lean_SourceInfo_fromRef(v_ref_3623_, v___x_3612_);
lean_dec(v_ref_3623_);
v___x_3627_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3628_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3629_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3550_);
v___x_3630_ = l_Lean_Name_mkStr2(v___x_3550_, v___x_3629_);
lean_inc(v_currMacroScope_3625_);
lean_inc(v_quotContext_3624_);
v___x_3631_ = l_Lean_addMacroScope(v_quotContext_3624_, v___x_3630_, v_currMacroScope_3625_);
v___x_3632_ = l_Lean_Name_mkStr4(v___x_3551_, v___x_3552_, v___x_3550_, v___x_3629_);
v___x_3633_ = lean_box(0);
lean_inc(v___x_3632_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 1);
lean_ctor_set(v___x_3609_, 1, v___x_3633_);
lean_ctor_set(v___x_3609_, 0, v___x_3632_);
v___x_3635_ = v___x_3609_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
lean_object* v___x_3637_; 
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v___x_3632_);
v___x_3637_ = v___x_3621_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3632_);
v___x_3637_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 1);
lean_ctor_set(v___x_3604_, 1, v___x_3633_);
lean_ctor_set(v___x_3604_, 0, v___x_3637_);
v___x_3639_ = v___x_3604_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v___x_3633_);
v___x_3639_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3641_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set_tag(v___x_3595_, 1);
lean_ctor_set(v___x_3595_, 1, v___x_3639_);
lean_ctor_set(v___x_3595_, 0, v___x_3635_);
v___x_3641_ = v___x_3595_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
lean_inc(v___x_3626_);
v___x_3642_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3626_);
lean_ctor_set(v___x_3642_, 1, v___x_3628_);
lean_ctor_set(v___x_3642_, 2, v___x_3631_);
lean_ctor_set(v___x_3642_, 3, v___x_3641_);
v___x_3643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3644_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3645_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
lean_inc(v___x_3626_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 2);
lean_ctor_set(v___x_3590_, 1, v___x_3645_);
lean_ctor_set(v___x_3590_, 0, v___x_3626_);
v___x_3647_ = v___x_3590_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3648_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3649_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3625_);
lean_inc(v_quotContext_3624_);
v___x_3650_ = l_Lean_addMacroScope(v_quotContext_3624_, v___x_3649_, v_currMacroScope_3625_);
lean_inc(v___x_3626_);
v___x_3651_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3626_);
lean_ctor_set(v___x_3651_, 1, v___x_3648_);
lean_ctor_set(v___x_3651_, 2, v___x_3650_);
lean_ctor_set(v___x_3651_, 3, v___x_3633_);
v___x_3652_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
lean_inc(v___x_3626_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 2);
lean_ctor_set(v___x_3586_, 1, v___x_3652_);
lean_ctor_set(v___x_3586_, 0, v___x_3626_);
v___x_3654_ = v___x_3586_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3655_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3656_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3626_);
v___x_3657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3626_);
lean_ctor_set(v___x_3657_, 1, v___x_3655_);
v___x_3658_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3659_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3660_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc(v_currMacroScope_3625_);
lean_inc(v_quotContext_3624_);
v___x_3661_ = l_Lean_addMacroScope(v_quotContext_3624_, v___x_3660_, v_currMacroScope_3625_);
lean_inc(v___x_3626_);
v___x_3662_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3626_);
lean_ctor_set(v___x_3662_, 1, v___x_3659_);
lean_ctor_set(v___x_3662_, 2, v___x_3661_);
lean_ctor_set(v___x_3662_, 3, v___x_3633_);
v___x_3663_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3664_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
lean_inc(v_currMacroScope_3625_);
lean_inc(v_quotContext_3624_);
v___x_3665_ = l_Lean_addMacroScope(v_quotContext_3624_, v___x_3664_, v_currMacroScope_3625_);
lean_inc(v___x_3626_);
v___x_3666_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3626_);
lean_ctor_set(v___x_3666_, 1, v___x_3663_);
lean_ctor_set(v___x_3666_, 2, v___x_3665_);
lean_ctor_set(v___x_3666_, 3, v___x_3633_);
lean_inc_ref(v___x_3666_);
lean_inc(v___x_3626_);
v___x_3667_ = l_Lean_Syntax_node2(v___x_3626_, v___x_3643_, v___x_3662_, v___x_3666_);
v___x_3668_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_3626_);
v___x_3669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3626_);
lean_ctor_set(v___x_3669_, 1, v___x_3643_);
lean_ctor_set(v___x_3669_, 2, v___x_3668_);
v___x_3670_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_3626_);
v___x_3671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3626_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
lean_inc_ref(v___x_3671_);
lean_inc_ref(v___x_3669_);
lean_inc(v___x_3626_);
v___x_3672_ = l_Lean_Syntax_node4(v___x_3626_, v___x_3658_, v___x_3667_, v___x_3669_, v___x_3671_, v_snd_3602_);
lean_inc_ref(v___x_3657_);
lean_inc(v___x_3626_);
v___x_3673_ = l_Lean_Syntax_node2(v___x_3626_, v___x_3656_, v___x_3657_, v___x_3672_);
v___x_3674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
lean_inc(v___x_3626_);
v___x_3675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3626_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
lean_inc_ref(v___x_3675_);
lean_inc_ref(v___x_3654_);
lean_inc_ref(v___x_3647_);
lean_inc(v___x_3626_);
v___x_3676_ = l_Lean_Syntax_node5(v___x_3626_, v___x_3644_, v___x_3647_, v___x_3651_, v___x_3654_, v___x_3673_, v___x_3675_);
v___x_3677_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3678_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
lean_inc(v_currMacroScope_3625_);
lean_inc(v_quotContext_3624_);
v___x_3679_ = l_Lean_addMacroScope(v_quotContext_3624_, v___x_3678_, v_currMacroScope_3625_);
lean_inc(v___x_3626_);
v___x_3680_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3626_);
lean_ctor_set(v___x_3680_, 1, v___x_3677_);
lean_ctor_set(v___x_3680_, 2, v___x_3679_);
lean_ctor_set(v___x_3680_, 3, v___x_3633_);
v___x_3681_ = l_String_toRawSubstring_x27(v___x_3553_);
lean_inc(v_currMacroScope_3625_);
lean_inc(v_quotContext_3624_);
v___x_3682_ = l_Lean_addMacroScope(v_quotContext_3624_, v___x_3541_, v_currMacroScope_3625_);
lean_inc(v___x_3626_);
v___x_3683_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3626_);
lean_ctor_set(v___x_3683_, 1, v___x_3681_);
lean_ctor_set(v___x_3683_, 2, v___x_3682_);
lean_ctor_set(v___x_3683_, 3, v___x_3633_);
lean_inc(v___x_3626_);
v___x_3684_ = l_Lean_Syntax_node2(v___x_3626_, v___x_3643_, v___x_3683_, v___x_3666_);
lean_inc(v___x_3626_);
v___x_3685_ = l_Lean_Syntax_node4(v___x_3626_, v___x_3658_, v___x_3684_, v___x_3669_, v___x_3671_, v_fst_3601_);
lean_inc(v___x_3626_);
v___x_3686_ = l_Lean_Syntax_node2(v___x_3626_, v___x_3656_, v___x_3657_, v___x_3685_);
lean_inc_ref(v___x_3675_);
lean_inc_ref(v___x_3654_);
lean_inc_ref(v___x_3647_);
lean_inc(v___x_3626_);
v___x_3687_ = l_Lean_Syntax_node5(v___x_3626_, v___x_3644_, v___x_3647_, v___x_3680_, v___x_3654_, v___x_3686_, v___x_3675_);
v___x_3688_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3689_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3690_ = l_Lean_addMacroScope(v_quotContext_3624_, v___x_3689_, v_currMacroScope_3625_);
lean_inc(v___x_3626_);
v___x_3691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3626_);
lean_ctor_set(v___x_3691_, 1, v___x_3688_);
lean_ctor_set(v___x_3691_, 2, v___x_3690_);
lean_ctor_set(v___x_3691_, 3, v___x_3633_);
lean_inc(v___x_3626_);
v___x_3692_ = l_Lean_Syntax_node5(v___x_3626_, v___x_3644_, v___x_3647_, v___x_3691_, v___x_3654_, v_a_3619_, v___x_3675_);
lean_inc(v___x_3626_);
v___x_3693_ = l_Lean_Syntax_node3(v___x_3626_, v___x_3643_, v___x_3676_, v___x_3687_, v___x_3692_);
v___x_3694_ = l_Lean_Syntax_node2(v___x_3626_, v___x_3627_, v___x_3642_, v___x_3693_);
v_a_3564_ = v___x_3694_;
goto v___jp_3563_;
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
lean_del_object(v___x_3609_);
lean_del_object(v___x_3604_);
lean_dec(v_snd_3602_);
lean_dec(v_fst_3601_);
lean_del_object(v___x_3595_);
lean_del_object(v___x_3590_);
lean_del_object(v___x_3586_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v___x_3553_);
lean_dec_ref(v___x_3552_);
lean_dec_ref(v___x_3551_);
lean_dec_ref(v___x_3550_);
lean_dec(v___x_3541_);
v___y_3568_ = v___x_3618_;
goto v___jp_3567_;
}
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
lean_del_object(v___x_3609_);
lean_dec(v_default_3607_);
lean_del_object(v___x_3604_);
lean_dec(v_snd_3602_);
lean_dec(v_fst_3601_);
lean_del_object(v___x_3595_);
lean_del_object(v___x_3590_);
lean_del_object(v___x_3586_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___x_3553_);
lean_dec_ref(v___x_3552_);
lean_dec_ref(v___x_3551_);
lean_dec_ref(v___x_3550_);
lean_dec(v___x_3541_);
v_a_3702_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3616_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3616_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
else
{
lean_dec_ref(v_points_3606_);
lean_dec(v___x_3549_);
switch(lean_obj_tag(v_default_3607_))
{
case 2:
{
lean_object* v_ref_3710_; lean_object* v_quotContext_3711_; lean_object* v_currMacroScope_3712_; uint8_t v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
lean_dec(v___y_3561_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
v_ref_3710_ = lean_ctor_get(v___y_3560_, 5);
lean_inc(v_ref_3710_);
v_quotContext_3711_ = lean_ctor_get(v___y_3560_, 10);
lean_inc(v_quotContext_3711_);
v_currMacroScope_3712_ = lean_ctor_get(v___y_3560_, 11);
lean_inc(v_currMacroScope_3712_);
lean_dec_ref(v___y_3560_);
v___x_3713_ = 0;
v___x_3714_ = l_Lean_SourceInfo_fromRef(v_ref_3710_, v___x_3713_);
lean_dec(v_ref_3710_);
v___x_3715_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3716_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3717_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3550_);
v___x_3718_ = l_Lean_Name_mkStr2(v___x_3550_, v___x_3717_);
lean_inc(v_currMacroScope_3712_);
lean_inc(v_quotContext_3711_);
v___x_3719_ = l_Lean_addMacroScope(v_quotContext_3711_, v___x_3718_, v_currMacroScope_3712_);
lean_inc_ref(v___x_3552_);
lean_inc_ref(v___x_3551_);
v___x_3720_ = l_Lean_Name_mkStr4(v___x_3551_, v___x_3552_, v___x_3550_, v___x_3717_);
v___x_3721_ = lean_box(0);
lean_inc(v___x_3720_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 1);
lean_ctor_set(v___x_3609_, 1, v___x_3721_);
lean_ctor_set(v___x_3609_, 0, v___x_3720_);
v___x_3723_ = v___x_3609_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set_tag(v___x_3580_, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3720_);
v___x_3725_ = v___x_3580_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3720_);
v___x_3725_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3727_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 1);
lean_ctor_set(v___x_3604_, 1, v___x_3721_);
lean_ctor_set(v___x_3604_, 0, v___x_3725_);
v___x_3727_ = v___x_3604_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v___x_3721_);
v___x_3727_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set_tag(v___x_3595_, 1);
lean_ctor_set(v___x_3595_, 1, v___x_3727_);
lean_ctor_set(v___x_3595_, 0, v___x_3723_);
v___x_3729_ = v___x_3595_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
lean_inc(v___x_3714_);
v___x_3730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3714_);
lean_ctor_set(v___x_3730_, 1, v___x_3716_);
lean_ctor_set(v___x_3730_, 2, v___x_3719_);
lean_ctor_set(v___x_3730_, 3, v___x_3729_);
v___x_3731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3733_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
lean_inc(v___x_3714_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 2);
lean_ctor_set(v___x_3590_, 1, v___x_3733_);
lean_ctor_set(v___x_3590_, 0, v___x_3714_);
v___x_3735_ = v___x_3590_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3736_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3737_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3712_);
lean_inc(v_quotContext_3711_);
v___x_3738_ = l_Lean_addMacroScope(v_quotContext_3711_, v___x_3737_, v_currMacroScope_3712_);
lean_inc(v___x_3714_);
v___x_3739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3714_);
lean_ctor_set(v___x_3739_, 1, v___x_3736_);
lean_ctor_set(v___x_3739_, 2, v___x_3738_);
lean_ctor_set(v___x_3739_, 3, v___x_3721_);
v___x_3740_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
lean_inc(v___x_3714_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 2);
lean_ctor_set(v___x_3586_, 1, v___x_3740_);
lean_ctor_set(v___x_3586_, 0, v___x_3714_);
v___x_3742_ = v___x_3586_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3743_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3744_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3714_);
v___x_3745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3714_);
lean_ctor_set(v___x_3745_, 1, v___x_3743_);
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3747_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3748_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc(v_currMacroScope_3712_);
lean_inc(v_quotContext_3711_);
v___x_3749_ = l_Lean_addMacroScope(v_quotContext_3711_, v___x_3748_, v_currMacroScope_3712_);
lean_inc(v___x_3714_);
v___x_3750_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3714_);
lean_ctor_set(v___x_3750_, 1, v___x_3747_);
lean_ctor_set(v___x_3750_, 2, v___x_3749_);
lean_ctor_set(v___x_3750_, 3, v___x_3721_);
v___x_3751_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3752_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
lean_inc(v_currMacroScope_3712_);
lean_inc(v_quotContext_3711_);
v___x_3753_ = l_Lean_addMacroScope(v_quotContext_3711_, v___x_3752_, v_currMacroScope_3712_);
lean_inc(v___x_3714_);
v___x_3754_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3714_);
lean_ctor_set(v___x_3754_, 1, v___x_3751_);
lean_ctor_set(v___x_3754_, 2, v___x_3753_);
lean_ctor_set(v___x_3754_, 3, v___x_3721_);
lean_inc_ref(v___x_3754_);
lean_inc(v___x_3714_);
v___x_3755_ = l_Lean_Syntax_node2(v___x_3714_, v___x_3731_, v___x_3750_, v___x_3754_);
v___x_3756_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_3714_);
v___x_3757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3714_);
lean_ctor_set(v___x_3757_, 1, v___x_3731_);
lean_ctor_set(v___x_3757_, 2, v___x_3756_);
v___x_3758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_3714_);
v___x_3759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3714_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
lean_inc_ref(v___x_3759_);
lean_inc_ref(v___x_3757_);
lean_inc(v___x_3714_);
v___x_3760_ = l_Lean_Syntax_node4(v___x_3714_, v___x_3746_, v___x_3755_, v___x_3757_, v___x_3759_, v_snd_3602_);
lean_inc_ref(v___x_3745_);
lean_inc(v___x_3714_);
v___x_3761_ = l_Lean_Syntax_node2(v___x_3714_, v___x_3744_, v___x_3745_, v___x_3760_);
v___x_3762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
lean_inc(v___x_3714_);
v___x_3763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3714_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
lean_inc_ref(v___x_3763_);
lean_inc_ref(v___x_3742_);
lean_inc_ref(v___x_3735_);
lean_inc(v___x_3714_);
v___x_3764_ = l_Lean_Syntax_node5(v___x_3714_, v___x_3732_, v___x_3735_, v___x_3739_, v___x_3742_, v___x_3761_, v___x_3763_);
v___x_3765_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3766_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
lean_inc(v_currMacroScope_3712_);
lean_inc(v_quotContext_3711_);
v___x_3767_ = l_Lean_addMacroScope(v_quotContext_3711_, v___x_3766_, v_currMacroScope_3712_);
lean_inc(v___x_3714_);
v___x_3768_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3714_);
lean_ctor_set(v___x_3768_, 1, v___x_3765_);
lean_ctor_set(v___x_3768_, 2, v___x_3767_);
lean_ctor_set(v___x_3768_, 3, v___x_3721_);
v___x_3769_ = l_String_toRawSubstring_x27(v___x_3553_);
lean_inc(v_currMacroScope_3712_);
lean_inc(v_quotContext_3711_);
v___x_3770_ = l_Lean_addMacroScope(v_quotContext_3711_, v___x_3541_, v_currMacroScope_3712_);
lean_inc(v___x_3714_);
v___x_3771_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3714_);
lean_ctor_set(v___x_3771_, 1, v___x_3769_);
lean_ctor_set(v___x_3771_, 2, v___x_3770_);
lean_ctor_set(v___x_3771_, 3, v___x_3721_);
lean_inc(v___x_3714_);
v___x_3772_ = l_Lean_Syntax_node2(v___x_3714_, v___x_3731_, v___x_3771_, v___x_3754_);
v___x_3773_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
lean_inc(v_currMacroScope_3712_);
lean_inc(v_quotContext_3711_);
v___x_3775_ = l_Lean_addMacroScope(v_quotContext_3711_, v___x_3774_, v_currMacroScope_3712_);
lean_inc(v___x_3714_);
v___x_3776_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3714_);
lean_ctor_set(v___x_3776_, 1, v___x_3773_);
lean_ctor_set(v___x_3776_, 2, v___x_3775_);
lean_ctor_set(v___x_3776_, 3, v___x_3721_);
v___x_3777_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3781_ = l_Lean_addMacroScope(v_quotContext_3711_, v___x_3780_, v_currMacroScope_3712_);
v___x_3782_ = l_Lean_Name_mkStr4(v___x_3551_, v___x_3552_, v___x_3778_, v___x_3779_);
v___x_3783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
lean_ctor_set(v___x_3783_, 1, v___x_3721_);
v___x_3784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set(v___x_3784_, 1, v___x_3721_);
lean_inc(v___x_3714_);
v___x_3785_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3714_);
lean_ctor_set(v___x_3785_, 1, v___x_3777_);
lean_ctor_set(v___x_3785_, 2, v___x_3781_);
lean_ctor_set(v___x_3785_, 3, v___x_3784_);
lean_inc_ref(v___x_3763_);
lean_inc_ref(v___x_3742_);
lean_inc_ref(v___x_3735_);
lean_inc(v___x_3714_);
v___x_3786_ = l_Lean_Syntax_node5(v___x_3714_, v___x_3732_, v___x_3735_, v___x_3776_, v___x_3742_, v___x_3785_, v___x_3763_);
lean_inc(v___x_3714_);
v___x_3787_ = l_Lean_Syntax_node1(v___x_3714_, v___x_3731_, v___x_3786_);
lean_inc(v___x_3714_);
v___x_3788_ = l_Lean_Syntax_node2(v___x_3714_, v___x_3715_, v_fst_3601_, v___x_3787_);
lean_inc(v___x_3714_);
v___x_3789_ = l_Lean_Syntax_node4(v___x_3714_, v___x_3746_, v___x_3772_, v___x_3757_, v___x_3759_, v___x_3788_);
lean_inc(v___x_3714_);
v___x_3790_ = l_Lean_Syntax_node2(v___x_3714_, v___x_3744_, v___x_3745_, v___x_3789_);
lean_inc(v___x_3714_);
v___x_3791_ = l_Lean_Syntax_node5(v___x_3714_, v___x_3732_, v___x_3735_, v___x_3768_, v___x_3742_, v___x_3790_, v___x_3763_);
lean_inc(v___x_3714_);
v___x_3792_ = l_Lean_Syntax_node2(v___x_3714_, v___x_3731_, v___x_3764_, v___x_3791_);
v___x_3793_ = l_Lean_Syntax_node2(v___x_3714_, v___x_3715_, v___x_3730_, v___x_3792_);
v_a_3564_ = v___x_3793_;
goto v___jp_3563_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_del_object(v___x_3580_);
v_e_3800_ = lean_ctor_get(v_default_3607_, 0);
lean_inc_ref(v_e_3800_);
lean_dec_ref(v_default_3607_);
v___x_3801_ = lean_box(1);
lean_inc_ref(v___y_3560_);
v___x_3802_ = l_Lean_PrettyPrinter_delab(v_e_3800_, v___x_3801_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3888_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3888_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3888_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v_ref_3807_; lean_object* v_quotContext_3808_; lean_object* v_currMacroScope_3809_; uint8_t v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3820_; 
v_ref_3807_ = lean_ctor_get(v___y_3560_, 5);
lean_inc(v_ref_3807_);
v_quotContext_3808_ = lean_ctor_get(v___y_3560_, 10);
lean_inc(v_quotContext_3808_);
v_currMacroScope_3809_ = lean_ctor_get(v___y_3560_, 11);
lean_inc(v_currMacroScope_3809_);
lean_dec_ref(v___y_3560_);
v___x_3810_ = 0;
v___x_3811_ = l_Lean_SourceInfo_fromRef(v_ref_3807_, v___x_3810_);
lean_dec(v_ref_3807_);
v___x_3812_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3813_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3814_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3550_);
v___x_3815_ = l_Lean_Name_mkStr2(v___x_3550_, v___x_3814_);
lean_inc(v_currMacroScope_3809_);
lean_inc(v_quotContext_3808_);
v___x_3816_ = l_Lean_addMacroScope(v_quotContext_3808_, v___x_3815_, v_currMacroScope_3809_);
v___x_3817_ = l_Lean_Name_mkStr4(v___x_3551_, v___x_3552_, v___x_3550_, v___x_3814_);
v___x_3818_ = lean_box(0);
lean_inc(v___x_3817_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 1);
lean_ctor_set(v___x_3609_, 1, v___x_3818_);
lean_ctor_set(v___x_3609_, 0, v___x_3817_);
v___x_3820_ = v___x_3609_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3822_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3817_);
v___x_3822_ = v___x_3805_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3817_);
v___x_3822_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3824_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 1);
lean_ctor_set(v___x_3604_, 1, v___x_3818_);
lean_ctor_set(v___x_3604_, 0, v___x_3822_);
v___x_3824_ = v___x_3604_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___x_3818_);
v___x_3824_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3826_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set_tag(v___x_3595_, 1);
lean_ctor_set(v___x_3595_, 1, v___x_3824_);
lean_ctor_set(v___x_3595_, 0, v___x_3820_);
v___x_3826_ = v___x_3595_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
lean_inc(v___x_3811_);
v___x_3827_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3811_);
lean_ctor_set(v___x_3827_, 1, v___x_3813_);
lean_ctor_set(v___x_3827_, 2, v___x_3816_);
lean_ctor_set(v___x_3827_, 3, v___x_3826_);
v___x_3828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3829_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3830_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
lean_inc(v___x_3811_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 2);
lean_ctor_set(v___x_3590_, 1, v___x_3830_);
lean_ctor_set(v___x_3590_, 0, v___x_3811_);
v___x_3832_ = v___x_3590_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3833_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3834_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3809_);
lean_inc(v_quotContext_3808_);
v___x_3835_ = l_Lean_addMacroScope(v_quotContext_3808_, v___x_3834_, v_currMacroScope_3809_);
lean_inc(v___x_3811_);
v___x_3836_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3811_);
lean_ctor_set(v___x_3836_, 1, v___x_3833_);
lean_ctor_set(v___x_3836_, 2, v___x_3835_);
lean_ctor_set(v___x_3836_, 3, v___x_3818_);
v___x_3837_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
lean_inc(v___x_3811_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 2);
lean_ctor_set(v___x_3586_, 1, v___x_3837_);
lean_ctor_set(v___x_3586_, 0, v___x_3811_);
v___x_3839_ = v___x_3586_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3840_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3841_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3811_);
v___x_3842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3811_);
lean_ctor_set(v___x_3842_, 1, v___x_3840_);
v___x_3843_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3844_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3845_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc(v_currMacroScope_3809_);
lean_inc(v_quotContext_3808_);
v___x_3846_ = l_Lean_addMacroScope(v_quotContext_3808_, v___x_3845_, v_currMacroScope_3809_);
lean_inc(v___x_3811_);
v___x_3847_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3811_);
lean_ctor_set(v___x_3847_, 1, v___x_3844_);
lean_ctor_set(v___x_3847_, 2, v___x_3846_);
lean_ctor_set(v___x_3847_, 3, v___x_3818_);
v___x_3848_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3849_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
lean_inc(v_currMacroScope_3809_);
lean_inc(v_quotContext_3808_);
v___x_3850_ = l_Lean_addMacroScope(v_quotContext_3808_, v___x_3849_, v_currMacroScope_3809_);
lean_inc(v___x_3811_);
v___x_3851_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3811_);
lean_ctor_set(v___x_3851_, 1, v___x_3848_);
lean_ctor_set(v___x_3851_, 2, v___x_3850_);
lean_ctor_set(v___x_3851_, 3, v___x_3818_);
lean_inc_ref(v___x_3851_);
lean_inc(v___x_3811_);
v___x_3852_ = l_Lean_Syntax_node2(v___x_3811_, v___x_3828_, v___x_3847_, v___x_3851_);
v___x_3853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_3811_);
v___x_3854_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3811_);
lean_ctor_set(v___x_3854_, 1, v___x_3828_);
lean_ctor_set(v___x_3854_, 2, v___x_3853_);
v___x_3855_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_3811_);
v___x_3856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3811_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
lean_inc_ref(v___x_3856_);
lean_inc_ref(v___x_3854_);
lean_inc(v___x_3811_);
v___x_3857_ = l_Lean_Syntax_node4(v___x_3811_, v___x_3843_, v___x_3852_, v___x_3854_, v___x_3856_, v_snd_3602_);
lean_inc_ref(v___x_3842_);
lean_inc(v___x_3811_);
v___x_3858_ = l_Lean_Syntax_node2(v___x_3811_, v___x_3841_, v___x_3842_, v___x_3857_);
v___x_3859_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
lean_inc(v___x_3811_);
v___x_3860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3811_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
lean_inc_ref(v___x_3860_);
lean_inc_ref(v___x_3839_);
lean_inc_ref(v___x_3832_);
lean_inc(v___x_3811_);
v___x_3861_ = l_Lean_Syntax_node5(v___x_3811_, v___x_3829_, v___x_3832_, v___x_3836_, v___x_3839_, v___x_3858_, v___x_3860_);
v___x_3862_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3863_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
lean_inc(v_currMacroScope_3809_);
lean_inc(v_quotContext_3808_);
v___x_3864_ = l_Lean_addMacroScope(v_quotContext_3808_, v___x_3863_, v_currMacroScope_3809_);
lean_inc(v___x_3811_);
v___x_3865_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3811_);
lean_ctor_set(v___x_3865_, 1, v___x_3862_);
lean_ctor_set(v___x_3865_, 2, v___x_3864_);
lean_ctor_set(v___x_3865_, 3, v___x_3818_);
v___x_3866_ = l_String_toRawSubstring_x27(v___x_3553_);
lean_inc(v_currMacroScope_3809_);
lean_inc(v_quotContext_3808_);
v___x_3867_ = l_Lean_addMacroScope(v_quotContext_3808_, v___x_3541_, v_currMacroScope_3809_);
lean_inc(v___x_3811_);
v___x_3868_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3811_);
lean_ctor_set(v___x_3868_, 1, v___x_3866_);
lean_ctor_set(v___x_3868_, 2, v___x_3867_);
lean_ctor_set(v___x_3868_, 3, v___x_3818_);
lean_inc(v___x_3811_);
v___x_3869_ = l_Lean_Syntax_node2(v___x_3811_, v___x_3828_, v___x_3868_, v___x_3851_);
v___x_3870_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3871_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3872_ = l_Lean_addMacroScope(v_quotContext_3808_, v___x_3871_, v_currMacroScope_3809_);
lean_inc(v___x_3811_);
v___x_3873_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3811_);
lean_ctor_set(v___x_3873_, 1, v___x_3870_);
lean_ctor_set(v___x_3873_, 2, v___x_3872_);
lean_ctor_set(v___x_3873_, 3, v___x_3818_);
lean_inc_ref(v___x_3860_);
lean_inc_ref(v___x_3839_);
lean_inc_ref(v___x_3832_);
lean_inc(v___x_3811_);
v___x_3874_ = l_Lean_Syntax_node5(v___x_3811_, v___x_3829_, v___x_3832_, v___x_3873_, v___x_3839_, v_a_3803_, v___x_3860_);
lean_inc(v___x_3811_);
v___x_3875_ = l_Lean_Syntax_node1(v___x_3811_, v___x_3828_, v___x_3874_);
lean_inc(v___x_3811_);
v___x_3876_ = l_Lean_Syntax_node2(v___x_3811_, v___x_3812_, v_fst_3601_, v___x_3875_);
lean_inc(v___x_3811_);
v___x_3877_ = l_Lean_Syntax_node4(v___x_3811_, v___x_3843_, v___x_3869_, v___x_3854_, v___x_3856_, v___x_3876_);
lean_inc(v___x_3811_);
v___x_3878_ = l_Lean_Syntax_node2(v___x_3811_, v___x_3841_, v___x_3842_, v___x_3877_);
lean_inc(v___x_3811_);
v___x_3879_ = l_Lean_Syntax_node5(v___x_3811_, v___x_3829_, v___x_3832_, v___x_3865_, v___x_3839_, v___x_3878_, v___x_3860_);
lean_inc(v___x_3811_);
v___x_3880_ = l_Lean_Syntax_node2(v___x_3811_, v___x_3828_, v___x_3861_, v___x_3879_);
v___x_3881_ = l_Lean_Syntax_node2(v___x_3811_, v___x_3812_, v___x_3827_, v___x_3880_);
v_a_3564_ = v___x_3881_;
goto v___jp_3563_;
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
lean_del_object(v___x_3609_);
lean_del_object(v___x_3604_);
lean_dec(v_snd_3602_);
lean_dec(v_fst_3601_);
lean_del_object(v___x_3595_);
lean_del_object(v___x_3590_);
lean_del_object(v___x_3586_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v___x_3553_);
lean_dec_ref(v___x_3552_);
lean_dec_ref(v___x_3551_);
lean_dec_ref(v___x_3550_);
lean_dec(v___x_3541_);
v___y_3568_ = v___x_3802_;
goto v___jp_3567_;
}
}
default: 
{
lean_object* v_ref_3889_; lean_object* v_quotContext_3890_; lean_object* v_currMacroScope_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
lean_dec(v_default_3607_);
lean_dec(v___y_3561_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
v_ref_3889_ = lean_ctor_get(v___y_3560_, 5);
lean_inc(v_ref_3889_);
v_quotContext_3890_ = lean_ctor_get(v___y_3560_, 10);
lean_inc(v_quotContext_3890_);
v_currMacroScope_3891_ = lean_ctor_get(v___y_3560_, 11);
lean_inc(v_currMacroScope_3891_);
lean_dec_ref(v___y_3560_);
v___x_3892_ = 0;
v___x_3893_ = l_Lean_SourceInfo_fromRef(v_ref_3889_, v___x_3892_);
lean_dec(v_ref_3889_);
v___x_3894_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3895_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3550_);
v___x_3897_ = l_Lean_Name_mkStr2(v___x_3550_, v___x_3896_);
lean_inc(v_currMacroScope_3891_);
lean_inc(v_quotContext_3890_);
v___x_3898_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3897_, v_currMacroScope_3891_);
v___x_3899_ = l_Lean_Name_mkStr4(v___x_3551_, v___x_3552_, v___x_3550_, v___x_3896_);
v___x_3900_ = lean_box(0);
lean_inc(v___x_3899_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 1);
lean_ctor_set(v___x_3609_, 1, v___x_3900_);
lean_ctor_set(v___x_3609_, 0, v___x_3899_);
v___x_3902_ = v___x_3609_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3899_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set_tag(v___x_3580_, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3899_);
v___x_3904_ = v___x_3580_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3899_);
v___x_3904_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3906_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 1);
lean_ctor_set(v___x_3604_, 1, v___x_3900_);
lean_ctor_set(v___x_3604_, 0, v___x_3904_);
v___x_3906_ = v___x_3604_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3900_);
v___x_3906_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3908_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set_tag(v___x_3595_, 1);
lean_ctor_set(v___x_3595_, 1, v___x_3906_);
lean_ctor_set(v___x_3595_, 0, v___x_3902_);
v___x_3908_ = v___x_3595_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3914_; 
lean_inc(v___x_3893_);
v___x_3909_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3893_);
lean_ctor_set(v___x_3909_, 1, v___x_3895_);
lean_ctor_set(v___x_3909_, 2, v___x_3898_);
lean_ctor_set(v___x_3909_, 3, v___x_3908_);
v___x_3910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3912_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
lean_inc(v___x_3893_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 2);
lean_ctor_set(v___x_3590_, 1, v___x_3912_);
lean_ctor_set(v___x_3590_, 0, v___x_3893_);
v___x_3914_ = v___x_3590_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3915_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3916_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3891_);
lean_inc(v_quotContext_3890_);
v___x_3917_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3916_, v_currMacroScope_3891_);
lean_inc(v___x_3893_);
v___x_3918_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3893_);
lean_ctor_set(v___x_3918_, 1, v___x_3915_);
lean_ctor_set(v___x_3918_, 2, v___x_3917_);
lean_ctor_set(v___x_3918_, 3, v___x_3900_);
v___x_3919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
lean_inc(v___x_3893_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 2);
lean_ctor_set(v___x_3586_, 1, v___x_3919_);
lean_ctor_set(v___x_3586_, 0, v___x_3893_);
v___x_3921_ = v___x_3586_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3922_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3923_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3893_);
v___x_3924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3893_);
lean_ctor_set(v___x_3924_, 1, v___x_3922_);
v___x_3925_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3926_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3927_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc(v_currMacroScope_3891_);
lean_inc(v_quotContext_3890_);
v___x_3928_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3927_, v_currMacroScope_3891_);
lean_inc(v___x_3893_);
v___x_3929_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3893_);
lean_ctor_set(v___x_3929_, 1, v___x_3926_);
lean_ctor_set(v___x_3929_, 2, v___x_3928_);
lean_ctor_set(v___x_3929_, 3, v___x_3900_);
v___x_3930_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3931_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
lean_inc(v_currMacroScope_3891_);
lean_inc(v_quotContext_3890_);
v___x_3932_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3931_, v_currMacroScope_3891_);
lean_inc(v___x_3893_);
v___x_3933_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3893_);
lean_ctor_set(v___x_3933_, 1, v___x_3930_);
lean_ctor_set(v___x_3933_, 2, v___x_3932_);
lean_ctor_set(v___x_3933_, 3, v___x_3900_);
lean_inc_ref(v___x_3933_);
lean_inc(v___x_3893_);
v___x_3934_ = l_Lean_Syntax_node2(v___x_3893_, v___x_3910_, v___x_3929_, v___x_3933_);
v___x_3935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_3893_);
v___x_3936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3893_);
lean_ctor_set(v___x_3936_, 1, v___x_3910_);
lean_ctor_set(v___x_3936_, 2, v___x_3935_);
v___x_3937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_3893_);
v___x_3938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3893_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
lean_inc_ref(v___x_3938_);
lean_inc_ref(v___x_3936_);
lean_inc(v___x_3893_);
v___x_3939_ = l_Lean_Syntax_node4(v___x_3893_, v___x_3925_, v___x_3934_, v___x_3936_, v___x_3938_, v_snd_3602_);
lean_inc_ref(v___x_3924_);
lean_inc(v___x_3893_);
v___x_3940_ = l_Lean_Syntax_node2(v___x_3893_, v___x_3923_, v___x_3924_, v___x_3939_);
v___x_3941_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
lean_inc(v___x_3893_);
v___x_3942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3893_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
lean_inc_ref(v___x_3942_);
lean_inc_ref(v___x_3921_);
lean_inc_ref(v___x_3914_);
lean_inc(v___x_3893_);
v___x_3943_ = l_Lean_Syntax_node5(v___x_3893_, v___x_3911_, v___x_3914_, v___x_3918_, v___x_3921_, v___x_3940_, v___x_3942_);
v___x_3944_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3945_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
lean_inc(v_currMacroScope_3891_);
lean_inc(v_quotContext_3890_);
v___x_3946_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3945_, v_currMacroScope_3891_);
lean_inc(v___x_3893_);
v___x_3947_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3893_);
lean_ctor_set(v___x_3947_, 1, v___x_3944_);
lean_ctor_set(v___x_3947_, 2, v___x_3946_);
lean_ctor_set(v___x_3947_, 3, v___x_3900_);
v___x_3948_ = l_String_toRawSubstring_x27(v___x_3553_);
v___x_3949_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3541_, v_currMacroScope_3891_);
lean_inc(v___x_3893_);
v___x_3950_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3893_);
lean_ctor_set(v___x_3950_, 1, v___x_3948_);
lean_ctor_set(v___x_3950_, 2, v___x_3949_);
lean_ctor_set(v___x_3950_, 3, v___x_3900_);
lean_inc(v___x_3893_);
v___x_3951_ = l_Lean_Syntax_node2(v___x_3893_, v___x_3910_, v___x_3950_, v___x_3933_);
lean_inc(v___x_3893_);
v___x_3952_ = l_Lean_Syntax_node4(v___x_3893_, v___x_3925_, v___x_3951_, v___x_3936_, v___x_3938_, v_fst_3601_);
lean_inc(v___x_3893_);
v___x_3953_ = l_Lean_Syntax_node2(v___x_3893_, v___x_3923_, v___x_3924_, v___x_3952_);
lean_inc(v___x_3893_);
v___x_3954_ = l_Lean_Syntax_node5(v___x_3893_, v___x_3911_, v___x_3914_, v___x_3947_, v___x_3921_, v___x_3953_, v___x_3942_);
lean_inc(v___x_3893_);
v___x_3955_ = l_Lean_Syntax_node2(v___x_3893_, v___x_3910_, v___x_3943_, v___x_3954_);
v___x_3956_ = l_Lean_Syntax_node2(v___x_3893_, v___x_3894_, v___x_3909_, v___x_3955_);
v_a_3564_ = v___x_3956_;
goto v___jp_3563_;
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
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_del_object(v___x_3595_);
lean_dec(v_snd_3593_);
lean_del_object(v___x_3590_);
lean_del_object(v___x_3586_);
lean_del_object(v___x_3580_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___x_3553_);
lean_dec_ref(v___x_3552_);
lean_dec_ref(v___x_3551_);
lean_dec_ref(v___x_3550_);
lean_dec(v___x_3549_);
lean_dec(v___x_3541_);
v_a_3965_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3599_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3599_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
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
lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4051_; 
lean_dec(v_a_3571_);
lean_dec(v___y_3561_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___x_3549_);
lean_dec(v___x_3548_);
lean_dec_ref(v___x_3542_);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_val_3574_);
if (v_isSharedCheck_4051_ == 0)
{
lean_object* v_unused_4052_; lean_object* v_unused_4053_; 
v_unused_4052_ = lean_ctor_get(v_val_3574_, 1);
lean_dec(v_unused_4052_);
v_unused_4053_ = lean_ctor_get(v_val_3574_, 0);
lean_dec(v_unused_4053_);
v___x_3979_ = v_val_3574_;
v_isShared_3980_ = v_isSharedCheck_4051_;
goto v_resetjp_3978_;
}
else
{
lean_dec(v_val_3574_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4051_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v_ref_3981_; lean_object* v_quotContext_3982_; lean_object* v_currMacroScope_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v_ref_3981_ = lean_ctor_get(v___y_3560_, 5);
lean_inc(v_ref_3981_);
v_quotContext_3982_ = lean_ctor_get(v___y_3560_, 10);
lean_inc(v_quotContext_3982_);
v_currMacroScope_3983_ = lean_ctor_get(v___y_3560_, 11);
lean_inc(v_currMacroScope_3983_);
lean_dec_ref(v___y_3560_);
v___x_3984_ = 0;
v___x_3985_ = l_Lean_SourceInfo_fromRef(v_ref_3981_, v___x_3984_);
lean_dec(v_ref_3981_);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3987_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3988_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3550_);
v___x_3989_ = l_Lean_Name_mkStr2(v___x_3550_, v___x_3988_);
lean_inc(v_currMacroScope_3983_);
lean_inc(v_quotContext_3982_);
v___x_3990_ = l_Lean_addMacroScope(v_quotContext_3982_, v___x_3989_, v_currMacroScope_3983_);
v___x_3991_ = l_Lean_Name_mkStr4(v___x_3551_, v___x_3552_, v___x_3550_, v___x_3988_);
v___x_3992_ = lean_box(0);
lean_inc(v___x_3991_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set_tag(v___x_3979_, 1);
lean_ctor_set(v___x_3979_, 1, v___x_3992_);
lean_ctor_set(v___x_3979_, 0, v___x_3991_);
v___x_3994_ = v___x_3979_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_4050_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set_tag(v___x_3576_, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3991_);
v___x_3996_ = v___x_3576_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_3991_);
v___x_3996_ = v_reuseFailAlloc_4049_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_3997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
lean_ctor_set(v___x_3997_, 1, v___x_3992_);
v___x_3998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3994_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
lean_inc(v___x_3985_);
v___x_3999_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3985_);
lean_ctor_set(v___x_3999_, 1, v___x_3987_);
lean_ctor_set(v___x_3999_, 2, v___x_3990_);
lean_ctor_set(v___x_3999_, 3, v___x_3998_);
v___x_4000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4001_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4002_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
lean_inc(v___x_3985_);
v___x_4003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_3985_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3983_);
lean_inc(v_quotContext_3982_);
v___x_4006_ = l_Lean_addMacroScope(v_quotContext_3982_, v___x_4005_, v_currMacroScope_3983_);
lean_inc(v___x_3985_);
v___x_4007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4007_, 0, v___x_3985_);
lean_ctor_set(v___x_4007_, 1, v___x_4004_);
lean_ctor_set(v___x_4007_, 2, v___x_4006_);
lean_ctor_set(v___x_4007_, 3, v___x_3992_);
v___x_4008_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
lean_inc(v___x_3985_);
v___x_4009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_3985_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4011_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3985_);
v___x_4012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_3985_);
lean_ctor_set(v___x_4012_, 1, v___x_4010_);
v___x_4013_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4014_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4015_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc(v_currMacroScope_3983_);
lean_inc(v_quotContext_3982_);
v___x_4016_ = l_Lean_addMacroScope(v_quotContext_3982_, v___x_4015_, v_currMacroScope_3983_);
lean_inc(v___x_3985_);
v___x_4017_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4017_, 0, v___x_3985_);
lean_ctor_set(v___x_4017_, 1, v___x_4014_);
lean_ctor_set(v___x_4017_, 2, v___x_4016_);
lean_ctor_set(v___x_4017_, 3, v___x_3992_);
v___x_4018_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4019_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
lean_inc(v_currMacroScope_3983_);
lean_inc(v_quotContext_3982_);
v___x_4020_ = l_Lean_addMacroScope(v_quotContext_3982_, v___x_4019_, v_currMacroScope_3983_);
lean_inc(v___x_3985_);
v___x_4021_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4021_, 0, v___x_3985_);
lean_ctor_set(v___x_4021_, 1, v___x_4018_);
lean_ctor_set(v___x_4021_, 2, v___x_4020_);
lean_ctor_set(v___x_4021_, 3, v___x_3992_);
lean_inc_ref(v___x_4021_);
lean_inc(v___x_3985_);
v___x_4022_ = l_Lean_Syntax_node2(v___x_3985_, v___x_4000_, v___x_4017_, v___x_4021_);
v___x_4023_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_3985_);
v___x_4024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4024_, 0, v___x_3985_);
lean_ctor_set(v___x_4024_, 1, v___x_4000_);
lean_ctor_set(v___x_4024_, 2, v___x_4023_);
v___x_4025_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_3985_);
v___x_4026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_3985_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4028_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
lean_inc(v___x_3985_);
v___x_4029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_3985_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
lean_inc(v___x_3985_);
v___x_4030_ = l_Lean_Syntax_node1(v___x_3985_, v___x_4027_, v___x_4029_);
lean_inc(v___x_4030_);
lean_inc_ref(v___x_4026_);
lean_inc_ref(v___x_4024_);
lean_inc(v___x_3985_);
v___x_4031_ = l_Lean_Syntax_node4(v___x_3985_, v___x_4013_, v___x_4022_, v___x_4024_, v___x_4026_, v___x_4030_);
lean_inc_ref(v___x_4012_);
lean_inc(v___x_3985_);
v___x_4032_ = l_Lean_Syntax_node2(v___x_3985_, v___x_4011_, v___x_4012_, v___x_4031_);
v___x_4033_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
lean_inc(v___x_3985_);
v___x_4034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_3985_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
lean_inc_ref(v___x_4034_);
lean_inc_ref(v___x_4009_);
lean_inc_ref(v___x_4003_);
lean_inc(v___x_3985_);
v___x_4035_ = l_Lean_Syntax_node5(v___x_3985_, v___x_4001_, v___x_4003_, v___x_4007_, v___x_4009_, v___x_4032_, v___x_4034_);
v___x_4036_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4037_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
lean_inc(v_currMacroScope_3983_);
lean_inc(v_quotContext_3982_);
v___x_4038_ = l_Lean_addMacroScope(v_quotContext_3982_, v___x_4037_, v_currMacroScope_3983_);
lean_inc(v___x_3985_);
v___x_4039_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4039_, 0, v___x_3985_);
lean_ctor_set(v___x_4039_, 1, v___x_4036_);
lean_ctor_set(v___x_4039_, 2, v___x_4038_);
lean_ctor_set(v___x_4039_, 3, v___x_3992_);
v___x_4040_ = l_String_toRawSubstring_x27(v___x_3553_);
v___x_4041_ = l_Lean_addMacroScope(v_quotContext_3982_, v___x_3541_, v_currMacroScope_3983_);
lean_inc(v___x_3985_);
v___x_4042_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4042_, 0, v___x_3985_);
lean_ctor_set(v___x_4042_, 1, v___x_4040_);
lean_ctor_set(v___x_4042_, 2, v___x_4041_);
lean_ctor_set(v___x_4042_, 3, v___x_3992_);
lean_inc(v___x_3985_);
v___x_4043_ = l_Lean_Syntax_node2(v___x_3985_, v___x_4000_, v___x_4042_, v___x_4021_);
lean_inc(v___x_3985_);
v___x_4044_ = l_Lean_Syntax_node4(v___x_3985_, v___x_4013_, v___x_4043_, v___x_4024_, v___x_4026_, v___x_4030_);
lean_inc(v___x_3985_);
v___x_4045_ = l_Lean_Syntax_node2(v___x_3985_, v___x_4011_, v___x_4012_, v___x_4044_);
lean_inc(v___x_3985_);
v___x_4046_ = l_Lean_Syntax_node5(v___x_3985_, v___x_4001_, v___x_4003_, v___x_4039_, v___x_4009_, v___x_4045_, v___x_4034_);
lean_inc(v___x_3985_);
v___x_4047_ = l_Lean_Syntax_node2(v___x_3985_, v___x_4000_, v___x_4035_, v___x_4046_);
v___x_4048_ = l_Lean_Syntax_node2(v___x_3985_, v___x_3986_, v___x_3999_, v___x_4047_);
v_a_3564_ = v___x_4048_;
goto v___jp_3563_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3573_);
lean_dec_ref(v___x_3550_);
if (lean_obj_tag(v_a_3571_) == 1)
{
lean_object* v_val_4055_; lean_object* v_snd_4056_; lean_object* v_fst_4057_; lean_object* v_snd_4058_; lean_object* v___x_4059_; lean_object* v___f_4060_; lean_object* v___x_4061_; 
v_val_4055_ = lean_ctor_get(v_a_3571_, 0);
lean_inc(v_val_4055_);
lean_dec_ref(v_a_3571_);
v_snd_4056_ = lean_ctor_get(v_val_4055_, 1);
lean_inc(v_snd_4056_);
v_fst_4057_ = lean_ctor_get(v_val_4055_, 0);
lean_inc(v_fst_4057_);
lean_dec(v_val_4055_);
v_snd_4058_ = lean_ctor_get(v_snd_4056_, 1);
lean_inc(v_snd_4058_);
lean_dec(v_snd_4056_);
v___x_4059_ = lean_box(v___x_3547_);
lean_inc(v___x_3541_);
v___f_4060_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4060_, 0, v_fst_4057_);
lean_closure_set(v___f_4060_, 1, v_snd_4058_);
lean_closure_set(v___f_4060_, 2, v___x_3551_);
lean_closure_set(v___f_4060_, 3, v___x_3552_);
lean_closure_set(v___f_4060_, 4, v___x_3553_);
lean_closure_set(v___f_4060_, 5, v___x_3541_);
lean_closure_set(v___f_4060_, 6, v___x_3548_);
lean_closure_set(v___f_4060_, 7, v___x_4059_);
lean_closure_set(v___f_4060_, 8, v___x_3549_);
lean_closure_set(v___f_4060_, 9, v_arg_3546_);
v___x_4061_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3541_, v___x_3542_, v___f_4060_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
v___y_3568_ = v___x_4061_;
goto v___jp_3567_;
}
else
{
lean_object* v_ref_4062_; lean_object* v_quotContext_4063_; lean_object* v_currMacroScope_4064_; uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_dec(v_a_3571_);
lean_dec(v___y_3561_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___x_3549_);
lean_dec(v___x_3548_);
lean_dec_ref(v_arg_3546_);
lean_dec_ref(v___x_3542_);
v_ref_4062_ = lean_ctor_get(v___y_3560_, 5);
lean_inc(v_ref_4062_);
v_quotContext_4063_ = lean_ctor_get(v___y_3560_, 10);
lean_inc(v_quotContext_4063_);
v_currMacroScope_4064_ = lean_ctor_get(v___y_3560_, 11);
lean_inc(v_currMacroScope_4064_);
lean_dec_ref(v___y_3560_);
v___x_4065_ = 0;
v___x_4066_ = l_Lean_SourceInfo_fromRef(v_ref_4062_, v___x_4065_);
lean_dec(v_ref_4062_);
v___x_4067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4068_ = l_Lean_Name_mkStr3(v___x_3551_, v___x_3552_, v___x_4067_);
v___x_4069_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4070_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc(v___x_4066_);
v___x_4071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4066_);
lean_ctor_set(v___x_4071_, 1, v___x_4069_);
lean_ctor_set(v___x_4071_, 2, v___x_4070_);
v___x_4072_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
lean_inc(v___x_4066_);
v___x_4073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4066_);
lean_ctor_set(v___x_4073_, 1, v___x_4072_);
v___x_4074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4075_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc(v___x_4066_);
v___x_4077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4066_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = l_String_toRawSubstring_x27(v___x_3553_);
lean_inc(v_currMacroScope_4064_);
lean_inc(v_quotContext_4063_);
v___x_4079_ = l_Lean_addMacroScope(v_quotContext_4063_, v___x_3541_, v_currMacroScope_4064_);
v___x_4080_ = lean_box(0);
lean_inc(v___x_4066_);
v___x_4081_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4066_);
lean_ctor_set(v___x_4081_, 1, v___x_4078_);
lean_ctor_set(v___x_4081_, 2, v___x_4079_);
lean_ctor_set(v___x_4081_, 3, v___x_4080_);
v___x_4082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
lean_inc(v___x_4066_);
v___x_4083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4066_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4085_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4086_ = l_Lean_addMacroScope(v_quotContext_4063_, v___x_4085_, v_currMacroScope_4064_);
lean_inc(v___x_4066_);
v___x_4087_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4066_);
lean_ctor_set(v___x_4087_, 1, v___x_4084_);
lean_ctor_set(v___x_4087_, 2, v___x_4086_);
lean_ctor_set(v___x_4087_, 3, v___x_4080_);
lean_inc(v___x_4066_);
v___x_4088_ = l_Lean_Syntax_node3(v___x_4066_, v___x_4074_, v___x_4081_, v___x_4083_, v___x_4087_);
v___x_4089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
lean_inc(v___x_4066_);
v___x_4090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4066_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
lean_inc(v___x_4066_);
v___x_4091_ = l_Lean_Syntax_node3(v___x_4066_, v___x_4075_, v___x_4077_, v___x_4088_, v___x_4090_);
lean_inc(v___x_4066_);
v___x_4092_ = l_Lean_Syntax_node1(v___x_4066_, v___x_4074_, v___x_4091_);
v___x_4093_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
lean_inc(v___x_4066_);
v___x_4094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4066_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4096_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
lean_inc(v___x_4066_);
v___x_4097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4066_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
lean_inc(v___x_4066_);
v___x_4098_ = l_Lean_Syntax_node1(v___x_4066_, v___x_4095_, v___x_4097_);
v___x_4099_ = l_Lean_Syntax_node5(v___x_4066_, v___x_4068_, v___x_4071_, v___x_4073_, v___x_4092_, v___x_4094_, v___x_4098_);
v_a_3564_ = v___x_4099_;
goto v___jp_3563_;
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_a_3571_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v___x_3553_);
lean_dec_ref(v___x_3552_);
lean_dec_ref(v___x_3551_);
lean_dec_ref(v___x_3550_);
lean_dec(v___x_3549_);
lean_dec(v___x_3548_);
lean_dec_ref(v_arg_3546_);
lean_dec_ref(v___x_3542_);
lean_dec(v___x_3541_);
v_a_4100_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_3572_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_3572_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v___x_3553_);
lean_dec_ref(v___x_3552_);
lean_dec_ref(v___x_3551_);
lean_dec_ref(v___x_3550_);
lean_dec(v___x_3549_);
lean_dec(v___x_3548_);
lean_dec_ref(v_arg_3546_);
lean_dec(v_inv_3545_);
lean_dec_ref(v___x_3542_);
lean_dec(v___x_3541_);
v_a_4108_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_3570_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_3570_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
v___jp_3563_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3564_);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
}
v___jp_3567_:
{
if (lean_obj_tag(v___y_3568_) == 0)
{
lean_object* v_a_3569_; 
v_a_3569_ = lean_ctor_get(v___y_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___y_3568_);
v_a_3564_ = v_a_3569_;
goto v___jp_3563_;
}
else
{
return v___y_3568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4116_ = _args[0];
lean_object* v___x_4117_ = _args[1];
lean_object* v___f_4118_ = _args[2];
lean_object* v_a_4119_ = _args[3];
lean_object* v_inv_4120_ = _args[4];
lean_object* v_arg_4121_ = _args[5];
lean_object* v___x_4122_ = _args[6];
lean_object* v___x_4123_ = _args[7];
lean_object* v___x_4124_ = _args[8];
lean_object* v___x_4125_ = _args[9];
lean_object* v___x_4126_ = _args[10];
lean_object* v___x_4127_ = _args[11];
lean_object* v___x_4128_ = _args[12];
lean_object* v___y_4129_ = _args[13];
lean_object* v___y_4130_ = _args[14];
lean_object* v___y_4131_ = _args[15];
lean_object* v___y_4132_ = _args[16];
lean_object* v___y_4133_ = _args[17];
lean_object* v___y_4134_ = _args[18];
lean_object* v___y_4135_ = _args[19];
lean_object* v___y_4136_ = _args[20];
lean_object* v___y_4137_ = _args[21];
_start:
{
uint8_t v___x_95403__boxed_4138_; lean_object* v_res_4139_; 
v___x_95403__boxed_4138_ = lean_unbox(v___x_4122_);
v_res_4139_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4116_, v___x_4117_, v___f_4118_, v_a_4119_, v_inv_4120_, v_arg_4121_, v___x_95403__boxed_4138_, v___x_4123_, v___x_4124_, v___x_4125_, v___x_4126_, v___x_4127_, v___x_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec_ref(v_a_4119_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; lean_object* v_env_4147_; lean_object* v___x_4148_; lean_object* v_mctx_4149_; lean_object* v_lctx_4150_; lean_object* v_options_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4146_ = lean_st_ref_get(v___y_4144_);
v_env_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc_ref(v_env_4147_);
lean_dec(v___x_4146_);
v___x_4148_ = lean_st_ref_get(v___y_4142_);
v_mctx_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc_ref(v_mctx_4149_);
lean_dec(v___x_4148_);
v_lctx_4150_ = lean_ctor_get(v___y_4141_, 2);
v_options_4151_ = lean_ctor_get(v___y_4143_, 2);
lean_inc_ref(v_options_4151_);
lean_inc_ref(v_lctx_4150_);
v___x_4152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4152_, 0, v_env_4147_);
lean_ctor_set(v___x_4152_, 1, v_mctx_4149_);
lean_ctor_set(v___x_4152_, 2, v_lctx_4150_);
lean_ctor_set(v___x_4152_, 3, v_options_4151_);
v___x_4153_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
lean_ctor_set(v___x_4153_, 1, v_msgData_4140_);
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_ref_4168_; lean_object* v___x_4169_; lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4178_; 
v_ref_4168_ = lean_ctor_get(v___y_4165_, 5);
v___x_4169_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4178_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4178_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4174_; lean_object* v___x_4176_; 
lean_inc(v_ref_4168_);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v_ref_4168_);
lean_ctor_set(v___x_4174_, 1, v_a_4170_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set_tag(v___x_4172_, 1);
lean_ctor_set(v___x_4172_, 0, v___x_4174_);
v___x_4176_ = v___x_4172_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4192_, size_t v_i_4193_, size_t v_stop_4194_, lean_object* v_b_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_a_4206_; lean_object* v_a_4211_; uint8_t v___x_4213_; 
v___x_4213_ = lean_usize_dec_eq(v_i_4193_, v_stop_4194_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4197_, v___y_4199_, v___y_4201_, v___y_4203_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4216_; lean_object* v___y_4218_; uint8_t v___y_4219_; lean_object* v___y_4234_; lean_object* v_a_4235_; lean_object* v___x_4238_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref(v___x_4214_);
v___x_4216_ = lean_array_uget_borrowed(v_as_4192_, v_i_4193_);
lean_inc(v___x_4216_);
v___x_4238_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4216_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v_ref_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
lean_dec_ref(v___x_4238_);
v_ref_4240_ = lean_ctor_get(v___y_4202_, 5);
v___x_4241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
v___x_4243_ = l_Lean_SourceInfo_fromRef(v_ref_4240_, v___x_4213_);
lean_inc(v___x_4243_);
v___x_4244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4243_);
lean_ctor_set(v___x_4244_, 1, v___x_4241_);
v___x_4245_ = l_Lean_Syntax_node1(v___x_4243_, v___x_4242_, v___x_4244_);
lean_inc(v___y_4203_);
lean_inc_ref(v___y_4202_);
lean_inc(v___y_4201_);
lean_inc_ref(v___y_4200_);
lean_inc(v___y_4199_);
lean_inc_ref(v___y_4198_);
lean_inc(v___y_4197_);
lean_inc_ref(v___y_4196_);
v___x_4246_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4245_, v_a_4239_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; lean_object* v___x_4248_; 
lean_dec(v_a_4215_);
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_a_4247_);
lean_dec_ref(v___x_4246_);
v___x_4248_ = lean_array_mk(v_a_4247_);
v_a_4211_ = v___x_4248_;
goto v___jp_4210_;
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
v_a_4249_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4246_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4246_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
lean_inc(v_a_4249_);
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
v___y_4234_ = v___x_4254_;
v_a_4235_ = v_a_4249_;
goto v___jp_4233_;
}
}
}
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
v_a_4257_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4238_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4238_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
lean_inc(v_a_4257_);
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
v___y_4234_ = v___x_4262_;
v_a_4235_ = v_a_4257_;
goto v___jp_4233_;
}
}
}
v___jp_4217_:
{
if (v___y_4219_ == 0)
{
lean_object* v___x_4220_; 
lean_dec_ref(v___y_4218_);
v___x_4220_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4215_, v___y_4219_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
lean_dec_ref(v___x_4220_);
v___x_4221_ = lean_unsigned_to_nat(1u);
v___x_4222_ = lean_mk_empty_array_with_capacity(v___x_4221_);
lean_inc(v___x_4216_);
v___x_4223_ = lean_array_push(v___x_4222_, v___x_4216_);
v_a_4211_ = v___x_4223_;
goto v___jp_4210_;
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_b_4195_);
v_a_4224_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4220_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4220_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_dec(v_a_4215_);
lean_dec_ref(v_b_4195_);
if (lean_obj_tag(v___y_4218_) == 0)
{
lean_object* v_a_4232_; 
v_a_4232_ = lean_ctor_get(v___y_4218_, 0);
lean_inc(v_a_4232_);
lean_dec_ref(v___y_4218_);
v_a_4206_ = v_a_4232_;
goto v___jp_4205_;
}
else
{
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
return v___y_4218_;
}
}
}
v___jp_4233_:
{
uint8_t v___x_4236_; 
v___x_4236_ = l_Lean_Exception_isInterrupt(v_a_4235_);
if (v___x_4236_ == 0)
{
uint8_t v___x_4237_; 
v___x_4237_ = l_Lean_Exception_isRuntime(v_a_4235_);
v___y_4218_ = v___y_4234_;
v___y_4219_ = v___x_4237_;
goto v___jp_4217_;
}
else
{
lean_dec_ref(v_a_4235_);
v___y_4218_ = v___y_4234_;
v___y_4219_ = v___x_4236_;
goto v___jp_4217_;
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_b_4195_);
v_a_4265_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4214_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4214_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
else
{
lean_object* v___x_4273_; 
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v_b_4195_);
return v___x_4273_;
}
v___jp_4205_:
{
size_t v___x_4207_; size_t v___x_4208_; 
v___x_4207_ = ((size_t)1ULL);
v___x_4208_ = lean_usize_add(v_i_4193_, v___x_4207_);
v_i_4193_ = v___x_4208_;
v_b_4195_ = v_a_4206_;
goto _start;
}
v___jp_4210_:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Array_append___redArg(v_b_4195_, v_a_4211_);
lean_dec_ref(v_a_4211_);
v_a_4206_ = v___x_4212_;
goto v___jp_4205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4274_, lean_object* v_i_4275_, lean_object* v_stop_4276_, lean_object* v_b_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
size_t v_i_boxed_4287_; size_t v_stop_boxed_4288_; lean_object* v_res_4289_; 
v_i_boxed_4287_ = lean_unbox_usize(v_i_4275_);
lean_dec(v_i_4275_);
v_stop_boxed_4288_ = lean_unbox_usize(v_stop_4276_);
lean_dec(v_stop_4276_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4274_, v_i_boxed_4287_, v_stop_boxed_4288_, v_b_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec_ref(v_as_4274_);
return v_res_4289_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4292_ = l_Lean_stringToMessageData(v___x_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4308_, lean_object* v_inv_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v___x_4319_; 
lean_inc(v_inv_4309_);
v___x_4319_ = l_Lean_MVarId_getType(v_inv_4309_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; lean_object* v_a_4322_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref(v___x_4319_);
v___x_4321_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4320_, v_a_4315_);
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref(v___x_4321_);
lean_inc(v_a_4322_);
v___x_4336_ = l_Lean_Expr_cleanupAnnotations(v_a_4322_);
v___x_4337_ = l_Lean_Expr_isApp(v___x_4336_);
if (v___x_4337_ == 0)
{
lean_dec_ref(v___x_4336_);
lean_dec(v_inv_4309_);
v___y_4324_ = v_a_4310_;
v___y_4325_ = v_a_4311_;
v___y_4326_ = v_a_4312_;
v___y_4327_ = v_a_4313_;
v___y_4328_ = v_a_4314_;
v___y_4329_ = v_a_4315_;
v___y_4330_ = v_a_4316_;
v___y_4331_ = v_a_4317_;
goto v___jp_4323_;
}
else
{
lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4336_);
v___x_4339_ = l_Lean_Expr_isApp(v___x_4338_);
if (v___x_4339_ == 0)
{
lean_dec_ref(v___x_4338_);
lean_dec(v_inv_4309_);
v___y_4324_ = v_a_4310_;
v___y_4325_ = v_a_4311_;
v___y_4326_ = v_a_4312_;
v___y_4327_ = v_a_4313_;
v___y_4328_ = v_a_4314_;
v___y_4329_ = v_a_4315_;
v___y_4330_ = v_a_4316_;
v___y_4331_ = v_a_4317_;
goto v___jp_4323_;
}
else
{
lean_object* v_arg_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v_arg_4340_ = lean_ctor_get(v___x_4338_, 1);
lean_inc_ref(v_arg_4340_);
v___x_4341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4338_);
v___x_4342_ = l_Lean_Expr_isApp(v___x_4341_);
if (v___x_4342_ == 0)
{
lean_dec_ref(v___x_4341_);
lean_dec_ref(v_arg_4340_);
lean_dec(v_inv_4309_);
v___y_4324_ = v_a_4310_;
v___y_4325_ = v_a_4311_;
v___y_4326_ = v_a_4312_;
v___y_4327_ = v_a_4313_;
v___y_4328_ = v_a_4314_;
v___y_4329_ = v_a_4315_;
v___y_4330_ = v_a_4316_;
v___y_4331_ = v_a_4317_;
goto v___jp_4323_;
}
else
{
lean_object* v_arg_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v_arg_4343_ = lean_ctor_get(v___x_4341_, 1);
lean_inc_ref(v_arg_4343_);
v___x_4344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4341_);
v___x_4345_ = l_Lean_Expr_isApp(v___x_4344_);
if (v___x_4345_ == 0)
{
lean_dec_ref(v___x_4344_);
lean_dec_ref(v_arg_4343_);
lean_dec_ref(v_arg_4340_);
lean_dec(v_inv_4309_);
v___y_4324_ = v_a_4310_;
v___y_4325_ = v_a_4311_;
v___y_4326_ = v_a_4312_;
v___y_4327_ = v_a_4313_;
v___y_4328_ = v_a_4314_;
v___y_4329_ = v_a_4315_;
v___y_4330_ = v_a_4316_;
v___y_4331_ = v_a_4317_;
goto v___jp_4323_;
}
else
{
lean_object* v_arg_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v_arg_4346_ = lean_ctor_get(v___x_4344_, 1);
lean_inc_ref(v_arg_4346_);
v___x_4347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4344_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4350_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4351_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4352_ = l_Lean_Expr_isConstOf(v___x_4347_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_dec_ref(v___x_4347_);
lean_dec_ref(v_arg_4346_);
lean_dec_ref(v_arg_4343_);
lean_dec_ref(v_arg_4340_);
lean_dec(v_inv_4309_);
v___y_4324_ = v_a_4310_;
v___y_4325_ = v_a_4311_;
v___y_4326_ = v_a_4312_;
v___y_4327_ = v_a_4313_;
v___y_4328_ = v_a_4314_;
v___y_4329_ = v_a_4315_;
v___y_4330_ = v_a_4316_;
v___y_4331_ = v_a_4317_;
goto v___jp_4323_;
}
else
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v_a_4359_; lean_object* v___y_4371_; lean_object* v___x_4381_; lean_object* v___x_4382_; uint8_t v___x_4383_; 
lean_dec(v_a_4322_);
v___x_4353_ = lean_unsigned_to_nat(1u);
v___x_4354_ = l_Lean_Expr_constLevels_x21(v___x_4347_);
lean_dec_ref(v___x_4347_);
v___x_4355_ = lean_unsigned_to_nat(0u);
v___x_4356_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4354_);
v___x_4357_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4354_, v___x_4354_, v___x_4353_, v___x_4356_);
lean_dec(v___x_4354_);
v___x_4381_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4382_ = lean_array_get_size(v_vcs_4308_);
v___x_4383_ = lean_nat_dec_lt(v___x_4355_, v___x_4382_);
if (v___x_4383_ == 0)
{
v_a_4359_ = v___x_4381_;
goto v___jp_4358_;
}
else
{
uint8_t v___x_4384_; 
v___x_4384_ = lean_nat_dec_le(v___x_4382_, v___x_4382_);
if (v___x_4384_ == 0)
{
if (v___x_4383_ == 0)
{
v_a_4359_ = v___x_4381_;
goto v___jp_4358_;
}
else
{
size_t v___x_4385_; size_t v___x_4386_; lean_object* v___x_4387_; 
v___x_4385_ = ((size_t)0ULL);
v___x_4386_ = lean_usize_of_nat(v___x_4382_);
lean_inc(v_a_4317_);
lean_inc_ref(v_a_4316_);
lean_inc(v_a_4315_);
lean_inc_ref(v_a_4314_);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
v___x_4387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4308_, v___x_4385_, v___x_4386_, v___x_4381_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
v___y_4371_ = v___x_4387_;
goto v___jp_4370_;
}
}
else
{
size_t v___x_4388_; size_t v___x_4389_; lean_object* v___x_4390_; 
v___x_4388_ = ((size_t)0ULL);
v___x_4389_ = lean_usize_of_nat(v___x_4382_);
lean_inc(v_a_4317_);
lean_inc_ref(v_a_4316_);
lean_inc(v_a_4315_);
lean_inc_ref(v_a_4314_);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
v___x_4390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4308_, v___x_4388_, v___x_4389_, v___x_4381_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
v___y_4371_ = v___x_4390_;
goto v___jp_4370_;
}
}
v___jp_4358_:
{
lean_object* v___x_4360_; lean_object* v___f_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___f_4368_; lean_object* v___x_4369_; 
v___x_4360_ = lean_box(v___x_4352_);
lean_inc_ref(v_arg_4340_);
lean_inc(v_inv_4309_);
lean_inc_ref(v_a_4359_);
v___f_4361_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4361_, 0, v_a_4359_);
lean_closure_set(v___f_4361_, 1, v_inv_4309_);
lean_closure_set(v___f_4361_, 2, v___x_4360_);
lean_closure_set(v___f_4361_, 3, v___x_4353_);
lean_closure_set(v___f_4361_, 4, v_arg_4340_);
v___x_4362_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4363_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4364_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4365_ = l_Lean_mkConst(v___x_4364_, v___x_4357_);
v___x_4366_ = l_Lean_mkAppB(v___x_4365_, v_arg_4346_, v_arg_4343_);
v___x_4367_ = lean_box(v___x_4352_);
lean_inc(v_inv_4309_);
v___f_4368_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4368_, 0, v___x_4363_);
lean_closure_set(v___f_4368_, 1, v___x_4366_);
lean_closure_set(v___f_4368_, 2, v___f_4361_);
lean_closure_set(v___f_4368_, 3, v_a_4359_);
lean_closure_set(v___f_4368_, 4, v_inv_4309_);
lean_closure_set(v___f_4368_, 5, v_arg_4340_);
lean_closure_set(v___f_4368_, 6, v___x_4367_);
lean_closure_set(v___f_4368_, 7, v___x_4353_);
lean_closure_set(v___f_4368_, 8, v___x_4355_);
lean_closure_set(v___f_4368_, 9, v___x_4350_);
lean_closure_set(v___f_4368_, 10, v___x_4348_);
lean_closure_set(v___f_4368_, 11, v___x_4349_);
lean_closure_set(v___f_4368_, 12, v___x_4362_);
v___x_4369_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4309_, v___f_4368_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
return v___x_4369_;
}
v___jp_4370_:
{
if (lean_obj_tag(v___y_4371_) == 0)
{
lean_object* v_a_4372_; 
v_a_4372_ = lean_ctor_get(v___y_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref(v___y_4371_);
v_a_4359_ = v_a_4372_;
goto v___jp_4358_;
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v___x_4357_);
lean_dec_ref(v_arg_4346_);
lean_dec_ref(v_arg_4343_);
lean_dec_ref(v_arg_4340_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec(v_inv_4309_);
v_a_4373_ = lean_ctor_get(v___y_4371_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___y_4371_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___y_4371_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___y_4371_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
}
}
}
}
}
v___jp_4323_:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
v___x_4332_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4333_ = l_Lean_MessageData_ofExpr(v_a_4322_);
v___x_4334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4332_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_4335_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4334_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
return v___x_4335_;
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec(v_inv_4309_);
v_a_4391_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4319_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4319_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4399_, lean_object* v_inv_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4399_, v_inv_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_);
lean_dec_ref(v_vcs_4399_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4411_, lean_object* v_msg_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4412_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4423_, lean_object* v_msg_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4423_, v_msg_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4435_, lean_object* v_name_4436_, uint8_t v_bi_4437_, lean_object* v_type_4438_, lean_object* v_k_4439_, uint8_t v_kind_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v___x_4450_; 
v___x_4450_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4436_, v_bi_4437_, v_type_4438_, v_k_4439_, v_kind_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4451_, lean_object* v_name_4452_, lean_object* v_bi_4453_, lean_object* v_type_4454_, lean_object* v_k_4455_, lean_object* v_kind_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
uint8_t v_bi_boxed_4466_; uint8_t v_kind_boxed_4467_; lean_object* v_res_4468_; 
v_bi_boxed_4466_ = lean_unbox(v_bi_4453_);
v_kind_boxed_4467_ = lean_unbox(v_kind_4456_);
v_res_4468_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4451_, v_name_4452_, v_bi_boxed_4466_, v_type_4454_, v_k_4455_, v_kind_boxed_4467_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4469_, lean_object* v_name_4470_, lean_object* v_type_4471_, lean_object* v_k_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4470_, v_type_4471_, v_k_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4483_, lean_object* v_name_4484_, lean_object* v_type_4485_, lean_object* v_k_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4483_, v_name_4484_, v_type_4485_, v_k_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4497_, size_t v_sz_4498_, size_t v_i_4499_, lean_object* v_b_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4497_, v_sz_4498_, v_i_4499_, v_b_4500_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4511_, lean_object* v_sz_4512_, lean_object* v_i_4513_, lean_object* v_b_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
size_t v_sz_boxed_4524_; size_t v_i_boxed_4525_; lean_object* v_res_4526_; 
v_sz_boxed_4524_ = lean_unbox_usize(v_sz_4512_);
lean_dec(v_sz_4512_);
v_i_boxed_4525_ = lean_unbox_usize(v_i_4513_);
lean_dec(v_i_4513_);
v_res_4526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4511_, v_sz_boxed_4524_, v_i_boxed_4525_, v_b_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec_ref(v_as_4511_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4527_, size_t v_sz_4528_, size_t v_i_4529_, lean_object* v_b_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4527_, v_sz_4528_, v_i_4529_, v_b_4530_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4541_, lean_object* v_sz_4542_, lean_object* v_i_4543_, lean_object* v_b_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
size_t v_sz_boxed_4554_; size_t v_i_boxed_4555_; lean_object* v_res_4556_; 
v_sz_boxed_4554_ = lean_unbox_usize(v_sz_4542_);
lean_dec(v_sz_4542_);
v_i_boxed_4555_ = lean_unbox_usize(v_i_4543_);
lean_dec(v_i_4543_);
v_res_4556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4541_, v_sz_boxed_4554_, v_i_boxed_4555_, v_b_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec_ref(v_as_4541_);
return v_res_4556_;
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
