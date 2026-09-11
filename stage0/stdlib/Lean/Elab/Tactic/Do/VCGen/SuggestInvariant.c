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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_nbuckets_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_804_ = lean_array_get_size(v_data_803_);
v___x_805_ = lean_unsigned_to_nat(2u);
v_nbuckets_806_ = lean_nat_mul(v___x_804_, v___x_805_);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_box(0);
v___x_809_ = lean_mk_array(v_nbuckets_806_, v___x_808_);
v___x_810_ = lean_array_propagate_mark(v_data_803_, v___x_809_);
v___x_811_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v___x_807_, v_data_803_, v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_812_, lean_object* v_a_813_, lean_object* v_b_814_){
_start:
{
lean_object* v_size_815_; lean_object* v_buckets_816_; lean_object* v___x_817_; uint64_t v___x_818_; uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v_fold_821_; uint64_t v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v___x_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v_bkt_830_; uint8_t v___x_831_; 
v_size_815_ = lean_ctor_get(v_m_812_, 0);
v_buckets_816_ = lean_ctor_get(v_m_812_, 1);
v___x_817_ = lean_array_get_size(v_buckets_816_);
v___x_818_ = l_Lean_Expr_hash(v_a_813_);
v___x_819_ = 32ULL;
v___x_820_ = lean_uint64_shift_right(v___x_818_, v___x_819_);
v_fold_821_ = lean_uint64_xor(v___x_818_, v___x_820_);
v___x_822_ = 16ULL;
v___x_823_ = lean_uint64_shift_right(v_fold_821_, v___x_822_);
v___x_824_ = lean_uint64_xor(v_fold_821_, v___x_823_);
v___x_825_ = lean_uint64_to_usize(v___x_824_);
v___x_826_ = lean_usize_of_nat(v___x_817_);
v___x_827_ = ((size_t)1ULL);
v___x_828_ = lean_usize_sub(v___x_826_, v___x_827_);
v___x_829_ = lean_usize_land(v___x_825_, v___x_828_);
v_bkt_830_ = lean_array_uget_borrowed(v_buckets_816_, v___x_829_);
v___x_831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_813_, v_bkt_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_852_; 
lean_inc_ref(v_buckets_816_);
lean_inc(v_size_815_);
v_isSharedCheck_852_ = !lean_is_exclusive(v_m_812_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; lean_object* v_unused_854_; 
v_unused_853_ = lean_ctor_get(v_m_812_, 1);
lean_dec(v_unused_853_);
v_unused_854_ = lean_ctor_get(v_m_812_, 0);
lean_dec(v_unused_854_);
v___x_833_ = v_m_812_;
v_isShared_834_ = v_isSharedCheck_852_;
goto v_resetjp_832_;
}
else
{
lean_dec(v_m_812_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_852_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v_size_x27_836_; lean_object* v___x_837_; lean_object* v_buckets_x27_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_835_ = lean_unsigned_to_nat(1u);
v_size_x27_836_ = lean_nat_add(v_size_815_, v___x_835_);
lean_dec(v_size_815_);
lean_inc(v_bkt_830_);
v___x_837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_837_, 0, v_a_813_);
lean_ctor_set(v___x_837_, 1, v_b_814_);
lean_ctor_set(v___x_837_, 2, v_bkt_830_);
v_buckets_x27_838_ = lean_array_uset(v_buckets_816_, v___x_829_, v___x_837_);
v___x_839_ = lean_unsigned_to_nat(4u);
v___x_840_ = lean_nat_mul(v_size_x27_836_, v___x_839_);
v___x_841_ = lean_unsigned_to_nat(3u);
v___x_842_ = lean_nat_div(v___x_840_, v___x_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_array_get_size(v_buckets_x27_838_);
v___x_844_ = lean_nat_dec_le(v___x_842_, v___x_843_);
lean_dec(v___x_842_);
if (v___x_844_ == 0)
{
lean_object* v_val_845_; lean_object* v___x_847_; 
v_val_845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_buckets_x27_838_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_val_845_);
lean_ctor_set(v___x_833_, 0, v_size_x27_836_);
v___x_847_ = v___x_833_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_size_x27_836_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_val_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
else
{
lean_object* v___x_850_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_buckets_x27_838_);
lean_ctor_set(v___x_833_, 0, v_size_x27_836_);
v___x_850_ = v___x_833_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_size_x27_836_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_buckets_x27_838_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_dec(v_b_814_);
lean_dec_ref(v_a_813_);
return v_m_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_as_855_, size_t v_sz_856_, size_t v_i_857_, lean_object* v_b_858_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = lean_usize_dec_lt(v_i_857_, v_sz_856_);
if (v___x_859_ == 0)
{
return v_b_858_;
}
else
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v_r_862_; size_t v___x_863_; size_t v___x_864_; 
v_a_860_ = lean_array_uget_borrowed(v_as_855_, v_i_857_);
v___x_861_ = lean_box(0);
lean_inc(v_a_860_);
v_r_862_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_858_, v_a_860_, v___x_861_);
v___x_863_ = ((size_t)1ULL);
v___x_864_ = lean_usize_add(v_i_857_, v___x_863_);
v_i_857_ = v___x_864_;
v_b_858_ = v_r_862_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_as_866_, lean_object* v_sz_867_, lean_object* v_i_868_, lean_object* v_b_869_){
_start:
{
size_t v_sz_boxed_870_; size_t v_i_boxed_871_; lean_object* v_res_872_; 
v_sz_boxed_870_ = lean_unbox_usize(v_sz_867_);
lean_dec(v_sz_867_);
v_i_boxed_871_ = lean_unbox_usize(v_i_868_);
lean_dec(v_i_868_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_866_, v_sz_boxed_870_, v_i_boxed_871_, v_b_869_);
lean_dec_ref(v_as_866_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_873_, lean_object* v_l_874_){
_start:
{
size_t v_sz_875_; size_t v___x_876_; lean_object* v___x_877_; 
v_sz_875_ = lean_array_size(v_l_874_);
v___x_876_ = ((size_t)0ULL);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_l_874_, v_sz_875_, v___x_876_, v_m_873_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_878_, lean_object* v_l_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_878_, v_l_879_);
lean_dec_ref(v_l_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_881_, size_t v_i_882_, size_t v_stop_883_, lean_object* v_b_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = lean_usize_dec_eq(v_i_882_, v_stop_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; size_t v___x_888_; size_t v___x_889_; 
v___x_886_ = lean_array_uget_borrowed(v_as_881_, v_i_882_);
lean_inc(v___x_886_);
v___x_887_ = l_Lean_collectFVars(v_b_884_, v___x_886_);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_add(v_i_882_, v___x_888_);
v_i_882_ = v___x_889_;
v_b_884_ = v___x_887_;
goto _start;
}
else
{
return v_b_884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_891_, lean_object* v_i_892_, lean_object* v_stop_893_, lean_object* v_b_894_){
_start:
{
size_t v_i_boxed_895_; size_t v_stop_boxed_896_; lean_object* v_res_897_; 
v_i_boxed_895_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_stop_boxed_896_ = lean_unbox_usize(v_stop_893_);
lean_dec(v_stop_893_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_891_, v_i_boxed_895_, v_stop_boxed_896_, v_b_894_);
lean_dec_ref(v_as_891_);
return v_res_897_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_box(0);
v___x_901_ = lean_unsigned_to_nat(16u);
v___x_902_ = lean_mk_array(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object* v_dontRevert_906_, lean_object* v_a_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
uint8_t v___x_913_; uint8_t v___x_914_; lean_object* v___x_915_; 
v___x_913_ = 0;
v___x_914_ = 1;
lean_inc_ref(v_a_907_);
v___x_915_ = l_Lean_Meta_collectForwardDeps(v_a_907_, v___x_913_, v___x_914_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_989_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_989_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_989_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_989_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___y_922_; size_t v___y_923_; lean_object* v___y_924_; lean_object* v___x_934_; lean_object* v___x_935_; size_t v___y_937_; lean_object* v___y_938_; lean_object* v_fvarIds_939_; size_t v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_953_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_box(1);
v___x_935_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_980_ = lean_array_get_size(v_a_916_);
v___x_981_ = lean_nat_dec_lt(v___x_920_, v___x_980_);
if (v___x_981_ == 0)
{
lean_dec(v_a_916_);
v___y_953_ = v___x_935_;
goto v___jp_952_;
}
else
{
uint8_t v___x_982_; 
v___x_982_ = lean_nat_dec_le(v___x_980_, v___x_980_);
if (v___x_982_ == 0)
{
if (v___x_981_ == 0)
{
lean_dec(v_a_916_);
v___y_953_ = v___x_935_;
goto v___jp_952_;
}
else
{
size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lean_usize_of_nat(v___x_980_);
lean_inc_ref(v_dontRevert_906_);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_906_, v_a_916_, v___x_983_, v___x_984_, v___x_935_);
lean_dec(v_a_916_);
v___y_953_ = v___x_985_;
goto v___jp_952_;
}
}
else
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_980_);
lean_inc_ref(v_dontRevert_906_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_906_, v_a_916_, v___x_986_, v___x_987_, v___x_935_);
lean_dec(v_a_916_);
v___y_953_ = v___x_988_;
goto v___jp_952_;
}
}
v___jp_921_:
{
size_t v_sz_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_sz_925_ = lean_array_size(v___y_924_);
lean_inc_ref(v___y_924_);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_925_, v___y_923_, v___y_924_);
v___x_927_ = l_Array_append___redArg(v___y_922_, v___x_926_);
lean_dec_ref(v___x_926_);
v___x_928_ = lean_array_get_size(v___y_924_);
lean_dec_ref(v___y_924_);
v___x_929_ = lean_nat_dec_eq(v___x_928_, v___x_920_);
if (v___x_929_ == 0)
{
lean_del_object(v___x_918_);
v_a_907_ = v___x_927_;
goto _start;
}
else
{
lean_object* v___x_932_; 
lean_dec_ref(v_dontRevert_906_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_927_);
v___x_932_ = v___x_918_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
v___jp_936_:
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_array_get_size(v_fvarIds_939_);
v___x_941_ = lean_nat_dec_lt(v___x_920_, v___x_940_);
if (v___x_941_ == 0)
{
lean_dec_ref(v_fvarIds_939_);
v___y_922_ = v___y_938_;
v___y_923_ = v___y_937_;
v___y_924_ = v___x_935_;
goto v___jp_921_;
}
else
{
uint8_t v___x_942_; 
v___x_942_ = lean_nat_dec_le(v___x_940_, v___x_940_);
if (v___x_942_ == 0)
{
if (v___x_941_ == 0)
{
lean_dec_ref(v_fvarIds_939_);
v___y_922_ = v___y_938_;
v___y_923_ = v___y_937_;
v___y_924_ = v___x_935_;
goto v___jp_921_;
}
else
{
size_t v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_usize_of_nat(v___x_940_);
lean_inc_ref(v_dontRevert_906_);
v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_906_, v_fvarIds_939_, v___y_937_, v___x_943_, v___x_935_);
lean_dec_ref(v_fvarIds_939_);
v___y_922_ = v___y_938_;
v___y_923_ = v___y_937_;
v___y_924_ = v___x_944_;
goto v___jp_921_;
}
}
else
{
size_t v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_usize_of_nat(v___x_940_);
lean_inc_ref(v_dontRevert_906_);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_906_, v_fvarIds_939_, v___y_937_, v___x_945_, v___x_935_);
lean_dec_ref(v_fvarIds_939_);
v___y_922_ = v___y_938_;
v___y_923_ = v___y_937_;
v___y_924_ = v___x_946_;
goto v___jp_921_;
}
}
}
v___jp_947_:
{
lean_object* v_fvarIds_951_; 
v_fvarIds_951_ = lean_ctor_get(v___y_950_, 2);
lean_inc_ref(v_fvarIds_951_);
lean_dec_ref(v___y_950_);
v___y_937_ = v___y_948_;
v___y_938_ = v___y_949_;
v_fvarIds_939_ = v_fvarIds_951_;
goto v___jp_936_;
}
v___jp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_954_ = lean_array_get_size(v___y_953_);
v___x_955_ = lean_array_get_size(v_a_907_);
lean_dec_ref(v_a_907_);
v___x_956_ = lean_nat_dec_eq(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
size_t v_sz_957_; size_t v___x_958_; lean_object* v___x_959_; 
v_sz_957_ = lean_array_size(v___y_953_);
v___x_958_ = ((size_t)0ULL);
lean_inc_ref(v___y_953_);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_957_, v___x_958_, v___y_953_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = lean_array_get_size(v_a_960_);
v___x_962_ = lean_nat_dec_lt(v___x_920_, v___x_961_);
if (v___x_962_ == 0)
{
lean_dec(v_a_960_);
v___y_937_ = v___x_958_;
v___y_938_ = v___y_953_;
v_fvarIds_939_ = v___x_935_;
goto v___jp_936_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_963_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_963_, v___y_953_);
v___x_965_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_934_);
lean_ctor_set(v___x_965_, 2, v___x_935_);
v___x_966_ = lean_nat_dec_le(v___x_961_, v___x_961_);
if (v___x_966_ == 0)
{
if (v___x_962_ == 0)
{
lean_dec_ref_known(v___x_965_, 3);
lean_dec(v_a_960_);
v___y_937_ = v___x_958_;
v___y_938_ = v___y_953_;
v_fvarIds_939_ = v___x_935_;
goto v___jp_936_;
}
else
{
size_t v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_usize_of_nat(v___x_961_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_960_, v___x_958_, v___x_967_, v___x_965_);
lean_dec(v_a_960_);
v___y_948_ = v___x_958_;
v___y_949_ = v___y_953_;
v___y_950_ = v___x_968_;
goto v___jp_947_;
}
}
else
{
size_t v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_usize_of_nat(v___x_961_);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_960_, v___x_958_, v___x_969_, v___x_965_);
lean_dec(v_a_960_);
v___y_948_ = v___x_958_;
v___y_949_ = v___y_953_;
v___y_950_ = v___x_970_;
goto v___jp_947_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v___y_953_);
lean_del_object(v___x_918_);
lean_dec_ref(v_dontRevert_906_);
v_a_971_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_959_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_959_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v___x_979_; 
lean_del_object(v___x_918_);
lean_dec_ref(v_dontRevert_906_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___y_953_);
return v___x_979_;
}
}
}
}
else
{
lean_dec_ref(v_a_907_);
lean_dec_ref(v_dontRevert_906_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object* v_dontRevert_990_, lean_object* v_a_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_990_, v_a_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_997_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_998_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_999_ = lean_box(1);
v___x_1000_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_1001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
lean_ctor_set(v___x_1001_, 2, v___x_998_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_1002_, lean_object* v_dontRevert_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___y_1010_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_fvarIds_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1017_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_1018_ = l_Lean_collectFVars(v___x_1017_, v_e_1002_);
v_fvarIds_1019_ = lean_ctor_get(v___x_1018_, 2);
lean_inc_ref(v_fvarIds_1019_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = lean_array_get_size(v_fvarIds_1019_);
v___x_1021_ = lean_nat_dec_lt(v___x_1015_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_dec_ref(v_fvarIds_1019_);
v___y_1010_ = v___x_1016_;
goto v___jp_1009_;
}
else
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_nat_dec_le(v___x_1020_, v___x_1020_);
if (v___x_1022_ == 0)
{
if (v___x_1021_ == 0)
{
lean_dec_ref(v_fvarIds_1019_);
v___y_1010_ = v___x_1016_;
goto v___jp_1009_;
}
else
{
size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = lean_usize_of_nat(v___x_1020_);
lean_inc_ref(v_dontRevert_1003_);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1003_, v_fvarIds_1019_, v___x_1023_, v___x_1024_, v___x_1016_);
lean_dec_ref(v_fvarIds_1019_);
v___y_1010_ = v___x_1025_;
goto v___jp_1009_;
}
}
else
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = lean_usize_of_nat(v___x_1020_);
lean_inc_ref(v_dontRevert_1003_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1003_, v_fvarIds_1019_, v___x_1026_, v___x_1027_, v___x_1016_);
lean_dec_ref(v_fvarIds_1019_);
v___y_1010_ = v___x_1028_;
goto v___jp_1009_;
}
}
v___jp_1009_:
{
size_t v_sz_1011_; size_t v___x_1012_; lean_object* v_xs_1013_; lean_object* v___x_1014_; 
v_sz_1011_ = lean_array_size(v___y_1010_);
v___x_1012_ = ((size_t)0ULL);
v_xs_1013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1011_, v___x_1012_, v___y_1010_);
v___x_1014_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1003_, v_xs_1013_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1029_, lean_object* v_dontRevert_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1029_, v_dontRevert_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_1037_, lean_object* v_inst_1038_, lean_object* v_a_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1037_, v_a_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_1046_, lean_object* v_inst_1047_, lean_object* v_a_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1046_, v_inst_1047_, v_a_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1055_, lean_object* v_m_1056_, lean_object* v_a_1057_, lean_object* v_b_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1056_, v_a_1057_, v_b_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1060_, lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_1061_, v_x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1064_, lean_object* v_a_1065_, lean_object* v_x_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1064_, v_a_1065_, v_x_1066_);
lean_dec(v_x_1066_);
lean_dec_ref(v_a_1065_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1069_, lean_object* v_data_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_data_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1072_, lean_object* v_i_1073_, lean_object* v_source_1074_, lean_object* v_target_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v_i_1073_, v_source_1074_, v_target_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1087_, lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v_i_1090_, lean_object* v_a_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_zero_1097_; uint8_t v_isZero_1098_; 
v_zero_1097_ = lean_unsigned_to_nat(0u);
v_isZero_1098_ = lean_nat_dec_eq(v_i_1090_, v_zero_1097_);
if (v_isZero_1098_ == 1)
{
lean_object* v___x_1099_; 
lean_dec(v_i_1090_);
lean_dec(v___x_1089_);
lean_dec_ref(v___x_1088_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1091_);
return v___x_1099_;
}
else
{
lean_object* v_one_1100_; lean_object* v_n_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_one_1100_ = lean_unsigned_to_nat(1u);
v_n_1101_ = lean_nat_sub(v_i_1090_, v_one_1100_);
lean_dec(v_i_1090_);
v___x_1102_ = lean_array_fget_borrowed(v_a_1087_, v_n_1101_);
lean_inc_ref(v___x_1088_);
v___x_1103_ = l_Lean_LocalContext_getFVar_x21(v___x_1088_, v___x_1102_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_userName_1104_; lean_object* v_type_1105_; uint8_t v_bi_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_userName_1104_ = lean_ctor_get(v___x_1103_, 2);
lean_inc(v_userName_1104_);
v_type_1105_ = lean_ctor_get(v___x_1103_, 3);
lean_inc_ref(v_type_1105_);
v_bi_1106_ = lean_ctor_get_uint8(v___x_1103_, sizeof(void*)*4);
lean_dec_ref_known(v___x_1103_, 4);
v___x_1107_ = l_Lean_Expr_headBeta(v_type_1105_);
v___x_1108_ = lean_expr_abstract_range(v___x_1107_, v_n_1101_, v_a_1087_);
lean_dec_ref(v___x_1107_);
lean_inc_ref(v___x_1108_);
v___x_1109_ = l_Lean_Meta_getLevel(v___x_1108_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1112_ = lean_box(0);
lean_inc_n(v___x_1089_, 2);
v___x_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1089_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_a_1110_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_mkConst(v___x_1111_, v___x_1114_);
v___x_1116_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1089_);
lean_inc_ref(v___x_1108_);
v___x_1117_ = l_Lean_mkLambda(v_userName_1104_, v_bi_1106_, v___x_1108_, v_a_1091_);
v___x_1118_ = l_Lean_mkApp3(v___x_1115_, v___x_1108_, v___x_1116_, v___x_1117_);
v_i_1090_ = v_n_1101_;
v_a_1091_ = v___x_1118_;
goto _start;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___x_1108_);
lean_dec(v_userName_1104_);
lean_dec(v_n_1101_);
lean_dec_ref(v_a_1091_);
lean_dec(v___x_1089_);
lean_dec_ref(v___x_1088_);
v_a_1120_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1109_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1109_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
uint8_t v_nondep_1128_; 
v_nondep_1128_ = lean_ctor_get_uint8(v___x_1103_, sizeof(void*)*5);
if (v_nondep_1128_ == 0)
{
lean_object* v_userName_1129_; lean_object* v_type_1130_; lean_object* v_value_1131_; uint8_t v___x_1132_; 
v_userName_1129_ = lean_ctor_get(v___x_1103_, 2);
lean_inc(v_userName_1129_);
v_type_1130_ = lean_ctor_get(v___x_1103_, 3);
lean_inc_ref(v_type_1130_);
v_value_1131_ = lean_ctor_get(v___x_1103_, 4);
lean_inc_ref(v_value_1131_);
lean_dec_ref_known(v___x_1103_, 5);
v___x_1132_ = lean_expr_has_loose_bvar(v_a_1091_, v_zero_1097_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec_ref(v_value_1131_);
lean_dec_ref(v_type_1130_);
lean_dec(v_userName_1129_);
v___x_1133_ = lean_expr_lower_loose_bvars(v_a_1091_, v_one_1100_, v_one_1100_);
lean_dec_ref(v_a_1091_);
v_i_1090_ = v_n_1101_;
v_a_1091_ = v___x_1133_;
goto _start;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = l_Lean_Expr_headBeta(v_type_1130_);
v___x_1136_ = lean_expr_abstract_range(v___x_1135_, v_n_1101_, v_a_1087_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = lean_expr_abstract_range(v_value_1131_, v_n_1101_, v_a_1087_);
lean_dec_ref(v_value_1131_);
v___x_1138_ = l_Lean_Expr_letE___override(v_userName_1129_, v___x_1136_, v___x_1137_, v_a_1091_, v_nondep_1128_);
v_i_1090_ = v_n_1101_;
v_a_1091_ = v___x_1138_;
goto _start;
}
}
else
{
lean_object* v_userName_1140_; lean_object* v_type_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_userName_1140_ = lean_ctor_get(v___x_1103_, 2);
lean_inc(v_userName_1140_);
v_type_1141_ = lean_ctor_get(v___x_1103_, 3);
lean_inc_ref(v_type_1141_);
lean_dec_ref_known(v___x_1103_, 5);
v___x_1142_ = l_Lean_Expr_headBeta(v_type_1141_);
v___x_1143_ = lean_expr_abstract_range(v___x_1142_, v_n_1101_, v_a_1087_);
lean_dec_ref(v___x_1142_);
lean_inc_ref(v___x_1143_);
v___x_1144_ = l_Lean_Meta_getLevel(v___x_1143_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1147_ = lean_box(0);
lean_inc_n(v___x_1089_, 2);
v___x_1148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1089_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_mkConst(v___x_1146_, v___x_1149_);
v___x_1151_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1089_);
v___x_1152_ = 0;
lean_inc_ref(v___x_1143_);
v___x_1153_ = l_Lean_mkLambda(v_userName_1140_, v___x_1152_, v___x_1143_, v_a_1091_);
v___x_1154_ = l_Lean_mkApp3(v___x_1150_, v___x_1143_, v___x_1151_, v___x_1153_);
v_i_1090_ = v_n_1101_;
v_a_1091_ = v___x_1154_;
goto _start;
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v___x_1143_);
lean_dec(v_userName_1140_);
lean_dec(v_n_1101_);
lean_dec_ref(v_a_1091_);
lean_dec(v___x_1089_);
lean_dec_ref(v___x_1088_);
v_a_1156_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1144_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1144_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1164_, lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v_i_1167_, lean_object* v_a_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1164_, v___x_1165_, v___x_1166_, v_i_1167_, v_a_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_a_1164_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1179_, lean_object* v_dontRevert_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; 
lean_inc_ref(v_e_1179_);
v___x_1186_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1179_, v_dontRevert_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_lctx_1188_; lean_object* v___x_1189_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v_lctx_1188_ = lean_ctor_get(v_a_1181_, 2);
lean_inc(v_a_1184_);
lean_inc_ref(v_a_1183_);
lean_inc(v_a_1182_);
lean_inc_ref(v_a_1181_);
lean_inc_ref(v_e_1179_);
v___x_1189_ = lean_infer_type(v_e_1179_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1212_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1212_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1212_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = l_Lean_Expr_cleanupAnnotations(v_a_1190_);
v___x_1195_ = l_Lean_Expr_isApp(v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v___x_1194_);
lean_dec(v_a_1187_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v_e_1179_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_e_1179_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1199_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1194_);
v___x_1200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1201_ = l_Lean_Expr_isConstOf(v___x_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1203_; 
lean_dec_ref(v___x_1199_);
lean_dec(v_a_1187_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v_e_1179_);
v___x_1203_ = v___x_1192_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_e_1179_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_del_object(v___x_1192_);
v___x_1205_ = lean_box(0);
v___x_1206_ = l_Lean_Expr_constLevels_x21(v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = l_List_get_x21Internal___redArg(v___x_1205_, v___x_1206_, v___x_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_array_get_size(v_a_1187_);
v___x_1210_ = lean_expr_abstract(v_e_1179_, v_a_1187_);
lean_dec_ref(v_e_1179_);
lean_inc_ref(v_lctx_1188_);
v___x_1211_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1187_, v_lctx_1188_, v___x_1208_, v___x_1209_, v___x_1210_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1187_);
return v___x_1211_;
}
}
}
}
else
{
lean_dec(v_a_1187_);
lean_dec_ref(v_e_1179_);
return v___x_1189_;
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v_e_1179_);
v_a_1213_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1186_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1186_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1221_, lean_object* v_dontRevert_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1221_, v_dontRevert_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1229_, lean_object* v___x_1230_, lean_object* v___x_1231_, lean_object* v_n_1232_, lean_object* v_i_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1229_, v___x_1230_, v___x_1231_, v_i_1233_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1242_, lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v_n_1245_, lean_object* v_i_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1242_, v___x_1243_, v___x_1244_, v_n_1245_, v_i_1246_, v_a_1247_, v_a_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v_n_1245_);
lean_dec_ref(v_a_1242_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1261_, lean_object* v_lhs_1262_, lean_object* v_rhs_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1276_, lean_object* v_lhs_1277_, lean_object* v_rhs_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1280_ = lean_box(0);
lean_inc(v_lvl_1276_);
v___x_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1281_, 0, v_lvl_1276_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_mkConst(v___x_1279_, v___x_1281_);
v___x_1283_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1276_);
v___x_1284_ = l_Lean_mkApp3(v___x_1282_, v___x_1283_, v_lhs_1277_, v_rhs_1278_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1285_){
_start:
{
lean_object* v_lvl_1286_; lean_object* v_cursorPred_1287_; lean_object* v_letMutsPred_1288_; lean_object* v___x_1289_; 
v_lvl_1286_ = lean_ctor_get(v_p_1285_, 0);
lean_inc(v_lvl_1286_);
v_cursorPred_1287_ = lean_ctor_get(v_p_1285_, 1);
lean_inc_ref(v_cursorPred_1287_);
v_letMutsPred_1288_ = lean_ctor_get(v_p_1285_, 2);
lean_inc_ref(v_letMutsPred_1288_);
lean_dec_ref(v_p_1285_);
v___x_1289_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1286_, v_cursorPred_1287_, v_letMutsPred_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(lean_object* v_x_1290_){
_start:
{
switch(lean_obj_tag(v_x_1290_))
{
case 0:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_unsigned_to_nat(0u);
return v___x_1291_;
}
case 1:
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_unsigned_to_nat(1u);
return v___x_1292_;
}
case 2:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_unsigned_to_nat(2u);
return v___x_1293_;
}
default: 
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_unsigned_to_nat(3u);
return v___x_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___boxed(lean_object* v_x_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(v_x_1295_);
lean_dec(v_x_1295_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1297_, lean_object* v_k_1298_){
_start:
{
if (lean_obj_tag(v_t_1297_) == 3)
{
lean_object* v_e_1299_; lean_object* v___x_1300_; 
v_e_1299_ = lean_ctor_get(v_t_1297_, 0);
lean_inc_ref(v_e_1299_);
lean_dec_ref_known(v_t_1297_, 1);
v___x_1300_ = lean_apply_1(v_k_1298_, v_e_1299_);
return v___x_1300_;
}
else
{
lean_dec(v_t_1297_);
return v_k_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1301_, lean_object* v_ctorIdx_1302_, lean_object* v_t_1303_, lean_object* v_h_1304_, lean_object* v_k_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1303_, v_k_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1307_, lean_object* v_ctorIdx_1308_, lean_object* v_t_1309_, lean_object* v_h_1310_, lean_object* v_k_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1307_, v_ctorIdx_1308_, v_t_1309_, v_h_1310_, v_k_1311_);
lean_dec(v_ctorIdx_1308_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1313_, lean_object* v_punit_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1313_, v_punit_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1316_, lean_object* v_t_1317_, lean_object* v_h_1318_, lean_object* v_punit_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1317_, v_punit_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1321_, lean_object* v_false_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1321_, v_false_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1324_, lean_object* v_t_1325_, lean_object* v_h_1326_, lean_object* v_false_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1325_, v_false_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1329_, lean_object* v_true_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1329_, v_true_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1332_, lean_object* v_t_1333_, lean_object* v_h_1334_, lean_object* v_true_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1333_, v_true_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1337_, lean_object* v_other_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1337_, v_other_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1340_, lean_object* v_t_1341_, lean_object* v_h_1342_, lean_object* v_other_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1341_, v_other_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1345_){
_start:
{
lean_object* v_snd_1347_; lean_object* v_fst_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1387_; 
v_snd_1347_ = lean_ctor_get(v_a_1345_, 1);
v_fst_1348_ = lean_ctor_get(v_a_1345_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_a_1345_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1350_ = v_a_1345_;
v_isShared_1351_ = v_isSharedCheck_1387_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_snd_1347_);
lean_inc(v_fst_1348_);
lean_dec(v_a_1345_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1387_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_fst_1352_; lean_object* v_snd_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1386_; 
v_fst_1352_ = lean_ctor_get(v_snd_1347_, 0);
v_snd_1353_ = lean_ctor_get(v_snd_1347_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_snd_1347_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1355_ = v_snd_1347_;
v_isShared_1356_ = v_isSharedCheck_1386_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_snd_1353_);
lean_inc(v_fst_1352_);
lean_dec(v_snd_1347_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1386_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1358_ = lean_unsigned_to_nat(4u);
v___x_1359_ = l_Lean_Expr_isAppOfArity(v_fst_1352_, v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1361_; 
if (v_isShared_1356_ == 0)
{
v___x_1361_ = v___x_1355_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_fst_1352_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_snd_1353_);
v___x_1361_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1361_);
v___x_1363_ = v___x_1350_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_fst_1348_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1367_ = lean_unsigned_to_nat(3u);
v___x_1368_ = lean_unsigned_to_nat(2u);
v___x_1369_ = l_Lean_Expr_getAppNumArgs(v_fst_1352_);
v___x_1370_ = lean_nat_sub(v___x_1369_, v___x_1368_);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_sub(v___x_1370_, v___x_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = l_Lean_Expr_getRevArg_x21(v_fst_1352_, v___x_1372_);
v___x_1374_ = lean_array_push(v_snd_1353_, v___x_1373_);
v___x_1375_ = lean_nat_add(v_fst_1348_, v___x_1371_);
lean_dec(v_fst_1348_);
v___x_1376_ = lean_nat_sub(v___x_1369_, v___x_1367_);
lean_dec(v___x_1369_);
v___x_1377_ = lean_nat_sub(v___x_1376_, v___x_1371_);
lean_dec(v___x_1376_);
v___x_1378_ = l_Lean_Expr_getRevArg_x21(v_fst_1352_, v___x_1377_);
lean_dec(v_fst_1352_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1374_);
lean_ctor_set(v___x_1355_, 0, v___x_1378_);
v___x_1380_ = v___x_1355_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1374_);
v___x_1380_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1380_);
lean_ctor_set(v___x_1350_, 0, v___x_1375_);
v___x_1382_ = v___x_1350_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
v_a_1345_ = v___x_1382_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1388_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_fst_1391_, lean_object* v_p_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_inc(v_fst_1391_);
v___x_1393_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1391_);
v___x_1394_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1391_, v___x_1393_, v_p_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_letMutsTuple_1395_, lean_object* v___x_1396_, uint8_t v___x_1397_, lean_object* v_fvarId_1398_){
_start:
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1395_);
v___x_1400_ = l_Lean_instBEqFVarId_beq(v_fvarId_1398_, v___x_1399_);
lean_dec(v___x_1399_);
if (v___x_1400_ == 0)
{
uint8_t v___x_1401_; 
v___x_1401_ = l_Lean_LocalContext_contains(v___x_1396_, v_fvarId_1398_);
return v___x_1401_;
}
else
{
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1402_, lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v_fvarId_1405_){
_start:
{
uint8_t v___x_9659__boxed_1406_; uint8_t v_res_1407_; lean_object* v_r_1408_; 
v___x_9659__boxed_1406_ = lean_unbox(v___x_1404_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1402_, v___x_1403_, v___x_9659__boxed_1406_, v_fvarId_1405_);
lean_dec(v_fvarId_1405_);
lean_dec_ref(v___x_1403_);
lean_dec_ref(v_letMutsTuple_1402_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1428_, lean_object* v___x_1429_, lean_object* v_xs_1430_, lean_object* v_letMuts_1431_, lean_object* v_as_1432_, size_t v_sz_1433_, size_t v_i_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_a_1442_; uint8_t v___x_1446_; 
v___x_1446_ = lean_usize_dec_lt(v_i_1434_, v_sz_1433_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_b_1435_);
return v___x_1447_;
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1449_; 
v_a_1448_ = lean_array_uget_borrowed(v_as_1432_, v_i_1434_);
lean_inc(v_a_1448_);
v___x_1449_ = l_Lean_MVarId_getType(v_a_1448_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_snd_1450_; lean_object* v_a_1451_; lean_object* v_fst_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1786_; 
v_snd_1450_ = lean_ctor_get(v_b_1435_, 1);
lean_inc(v_snd_1450_);
v_a_1451_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1449_, 1);
v_fst_1452_ = lean_ctor_get(v_b_1435_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_b_1435_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v_b_1435_, 1);
lean_dec(v_unused_1787_);
v___x_1454_ = v_b_1435_;
v_isShared_1455_ = v_isSharedCheck_1786_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_fst_1452_);
lean_dec(v_b_1435_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1786_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v_fst_1456_; lean_object* v_snd_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1785_; 
v_fst_1456_ = lean_ctor_get(v_snd_1450_, 0);
v_snd_1457_ = lean_ctor_get(v_snd_1450_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_snd_1450_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1459_ = v_snd_1450_;
v_isShared_1460_ = v_isSharedCheck_1785_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_snd_1457_);
lean_inc(v_fst_1456_);
lean_dec(v_snd_1450_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1785_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; uint8_t v___y_1475_; lean_object* v___y_1575_; lean_object* v_prefixPoint_x3f_1576_; lean_object* v_suffixPoint_x3f_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v_prefixPoint_x3f_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v_a_1695_; lean_object* v_a_1700_; lean_object* v___x_1773_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1463_ = lean_box(0);
v___x_1773_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1451_, v___y_1437_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = l_Lean_Expr_consumeMData(v_a_1774_);
lean_dec(v_a_1774_);
v_a_1700_ = v___x_1775_;
goto v___jp_1699_;
}
else
{
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1776_; 
v_a_1776_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1773_, 1);
v_a_1700_ = v_a_1776_;
goto v___jp_1699_;
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1454_);
lean_dec(v_fst_1452_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1777_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1773_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1773_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
v___jp_1464_:
{
if (v___y_1475_ == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref(v___y_1467_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___y_1471_);
v___x_1477_ = v___x_1459_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___y_1471_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_snd_1457_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v___x_1477_);
lean_ctor_set(v___x_1454_, 0, v___y_1468_);
v___x_1479_ = v___x_1454_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___y_1468_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v_a_1442_ = v___x_1479_;
goto v___jp_1441_;
}
}
}
else
{
lean_object* v___x_1483_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v___x_1462_);
lean_ctor_set(v___x_1459_, 0, v___y_1467_);
v___x_1483_ = v___x_1459_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___y_1467_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___x_1462_);
v___x_1483_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v___x_1483_);
lean_ctor_set(v___x_1454_, 0, v___x_1461_);
v___x_1485_ = v___x_1454_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v_snd_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1562_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v_snd_1488_ = lean_ctor_get(v_a_1487_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_a_1487_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v_a_1487_, 0);
lean_dec(v_unused_1563_);
v___x_1490_ = v_a_1487_;
v_isShared_1491_ = v_isSharedCheck_1562_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_snd_1488_);
lean_dec(v_a_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1562_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1561_; 
v_fst_1492_ = lean_ctor_get(v_snd_1488_, 0);
v_snd_1493_ = lean_ctor_get(v_snd_1488_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_snd_1488_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1495_ = v_snd_1488_;
v_isShared_1496_ = v_isSharedCheck_1561_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1493_);
lean_inc(v_fst_1492_);
lean_dec(v_snd_1488_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1561_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_points_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_points_1497_ = lean_ctor_get(v_snd_1457_, 0);
v___x_1498_ = lean_array_get_size(v_points_1497_);
v___x_1499_ = lean_array_get_size(v_snd_1493_);
v___x_1500_ = lean_nat_dec_lt(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1502_; 
lean_dec(v_snd_1493_);
lean_dec(v_fst_1492_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v_snd_1457_);
lean_ctor_set(v___x_1495_, 0, v___y_1471_);
v___x_1502_ = v___x_1495_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___y_1471_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_snd_1457_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1502_);
lean_ctor_set(v___x_1490_, 0, v___y_1468_);
v___x_1504_ = v___x_1490_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___y_1468_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
v_a_1442_ = v___x_1504_;
goto v___jp_1441_;
}
}
}
else
{
lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1558_; 
v_isSharedCheck_1558_ = !lean_is_exclusive(v_snd_1457_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; lean_object* v_unused_1560_; 
v_unused_1559_ = lean_ctor_get(v_snd_1457_, 1);
lean_dec(v_unused_1559_);
v_unused_1560_ = lean_ctor_get(v_snd_1457_, 0);
lean_dec(v_unused_1560_);
v___x_1508_ = v_snd_1457_;
v_isShared_1509_ = v_isSharedCheck_1558_;
goto v_resetjp_1507_;
}
else
{
lean_dec(v_snd_1457_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1558_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2));
v___x_1511_ = l_Lean_Expr_isConstOf(v_fst_1492_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3));
lean_inc_ref(v___y_1465_);
lean_inc_ref(v___y_1470_);
lean_inc_ref(v___y_1473_);
v___x_1513_ = l_Lean_Name_mkStr4(v___y_1473_, v___y_1470_, v___y_1465_, v___x_1512_);
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = l_Lean_Expr_isAppOfArity(v_fst_1492_, v___x_1513_, v___x_1514_);
lean_dec(v___x_1513_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
lean_inc_ref(v___y_1465_);
lean_inc_ref(v___y_1470_);
lean_inc_ref(v___y_1473_);
v___x_1517_ = l_Lean_Name_mkStr4(v___y_1473_, v___y_1470_, v___y_1465_, v___x_1516_);
v___x_1518_ = l_Lean_Expr_isAppOfArity(v_fst_1492_, v___x_1517_, v___x_1514_);
lean_dec(v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_fst_1492_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1519_);
lean_ctor_set(v___x_1508_, 0, v_snd_1493_);
v___x_1521_ = v___x_1508_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_snd_1493_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1521_);
lean_ctor_set(v___x_1495_, 0, v___y_1471_);
v___x_1523_ = v___x_1495_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___y_1471_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1523_);
lean_ctor_set(v___x_1490_, 0, v___y_1468_);
v___x_1525_ = v___x_1490_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___y_1468_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
v_a_1442_ = v___x_1525_;
goto v___jp_1441_;
}
}
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
lean_dec(v_fst_1492_);
v___x_1529_ = lean_box(2);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1529_);
lean_ctor_set(v___x_1508_, 0, v_snd_1493_);
v___x_1531_ = v___x_1508_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_snd_1493_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1531_);
lean_ctor_set(v___x_1495_, 0, v___y_1471_);
v___x_1533_ = v___x_1495_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___y_1471_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1533_);
lean_ctor_set(v___x_1490_, 0, v___y_1468_);
v___x_1535_ = v___x_1490_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___y_1468_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
v_a_1442_ = v___x_1535_;
goto v___jp_1441_;
}
}
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_dec(v_fst_1492_);
v___x_1539_ = lean_box(1);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1539_);
lean_ctor_set(v___x_1508_, 0, v_snd_1493_);
v___x_1541_ = v___x_1508_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_snd_1493_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1541_);
lean_ctor_set(v___x_1495_, 0, v___y_1471_);
v___x_1543_ = v___x_1495_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___y_1471_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1543_);
lean_ctor_set(v___x_1490_, 0, v___y_1468_);
v___x_1545_ = v___x_1490_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___y_1468_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v_a_1442_ = v___x_1545_;
goto v___jp_1441_;
}
}
}
}
}
else
{
lean_object* v___x_1550_; 
lean_dec(v_fst_1492_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1463_);
lean_ctor_set(v___x_1508_, 0, v_snd_1493_);
v___x_1550_ = v___x_1508_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_snd_1493_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1463_);
v___x_1550_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1550_);
lean_ctor_set(v___x_1495_, 0, v___y_1471_);
v___x_1552_ = v___x_1495_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___y_1471_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1552_);
lean_ctor_set(v___x_1490_, 0, v___y_1468_);
v___x_1554_ = v___x_1490_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___y_1468_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
v_a_1442_ = v___x_1554_;
goto v___jp_1441_;
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
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v___y_1471_);
lean_dec(v___y_1468_);
lean_dec(v_snd_1457_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1564_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1486_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1486_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
}
v___jp_1574_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_1583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_1584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1586_ = lean_unsigned_to_nat(3u);
v___x_1587_ = l_Lean_Expr_isAppOfArity(v___y_1575_, v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v___y_1575_);
lean_del_object(v___x_1459_);
lean_del_object(v___x_1454_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_suffixPoint_x3f_1577_);
lean_ctor_set(v___x_1588_, 1, v_snd_1457_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_prefixPoint_x3f_1576_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v_a_1442_ = v___x_1589_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1590_ = l_Lean_Expr_appFn_x21(v___y_1575_);
v___x_1591_ = l_Lean_Expr_appArg_x21(v___x_1590_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = l_Lean_Expr_appArg_x21(v___y_1575_);
lean_dec_ref(v___y_1575_);
v___x_1593_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1594_ = l_Lean_Expr_isAppOfArity(v___x_1591_, v___x_1593_, v___x_1586_);
if (v___x_1594_ == 0)
{
lean_dec_ref(v___x_1591_);
v___y_1465_ = v___x_1584_;
v___y_1466_ = v___y_1581_;
v___y_1467_ = v___x_1592_;
v___y_1468_ = v_prefixPoint_x3f_1576_;
v___y_1469_ = v___y_1579_;
v___y_1470_ = v___x_1583_;
v___y_1471_ = v_suffixPoint_x3f_1577_;
v___y_1472_ = v___y_1578_;
v___y_1473_ = v___x_1582_;
v___y_1474_ = v___y_1580_;
v___y_1475_ = v___x_1594_;
goto v___jp_1464_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1595_ = lean_unsigned_to_nat(2u);
v___x_1596_ = l_Lean_Expr_getAppNumArgs(v___x_1591_);
v___x_1597_ = lean_nat_sub(v___x_1596_, v___x_1595_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_unsigned_to_nat(1u);
v___x_1599_ = lean_nat_sub(v___x_1597_, v___x_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = l_Lean_Expr_getRevArg_x21(v___x_1591_, v___x_1599_);
lean_dec_ref(v___x_1591_);
lean_inc(v_inv_1428_);
v___x_1601_ = l_Lean_mkMVar(v_inv_1428_);
v___x_1602_ = lean_expr_eqv(v___x_1600_, v___x_1601_);
lean_dec_ref(v___x_1601_);
lean_dec_ref(v___x_1600_);
v___y_1465_ = v___x_1584_;
v___y_1466_ = v___y_1581_;
v___y_1467_ = v___x_1592_;
v___y_1468_ = v_prefixPoint_x3f_1576_;
v___y_1469_ = v___y_1579_;
v___y_1470_ = v___x_1583_;
v___y_1471_ = v_suffixPoint_x3f_1577_;
v___y_1472_ = v___y_1578_;
v___y_1473_ = v___x_1582_;
v___y_1474_ = v___y_1580_;
v___y_1475_ = v___x_1602_;
goto v___jp_1464_;
}
}
}
v___jp_1603_:
{
lean_object* v___x_1614_; 
lean_inc(v_inv_1428_);
v___x_1614_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v___y_1604_, v_inv_1428_);
lean_dec_ref(v___y_1604_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_invariantUse_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1687_; 
v_invariantUse_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1687_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_invariantUse_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1687_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v_conditionIdx_1619_; lean_object* v_cursorSuffix_1620_; lean_object* v_letMutsTuple_1621_; uint8_t v___x_1622_; 
v_conditionIdx_1619_ = lean_ctor_get(v_invariantUse_1615_, 0);
lean_inc(v_conditionIdx_1619_);
v_cursorSuffix_1620_ = lean_ctor_get(v_invariantUse_1615_, 2);
lean_inc_ref(v_cursorSuffix_1620_);
v_letMutsTuple_1621_ = lean_ctor_get(v_invariantUse_1615_, 4);
lean_inc_ref(v_letMutsTuple_1621_);
lean_dec_ref(v_invariantUse_1615_);
v___x_1622_ = lean_nat_dec_eq(v_conditionIdx_1619_, v___x_1461_);
lean_dec(v_conditionIdx_1619_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v_letMutsTuple_1621_);
lean_dec_ref(v_cursorSuffix_1620_);
lean_del_object(v___x_1617_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_del_object(v___x_1459_);
lean_del_object(v___x_1454_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_fst_1456_);
lean_ctor_set(v___x_1623_, 1, v_snd_1457_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_prefixPoint_x3f_1609_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v_a_1442_ = v___x_1624_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1626_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1620_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_dec_ref(v_letMutsTuple_1621_);
lean_dec_ref(v_cursorSuffix_1620_);
lean_del_object(v___x_1617_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1605_);
v___y_1575_ = v___y_1606_;
v_prefixPoint_x3f_1576_ = v_prefixPoint_x3f_1609_;
v_suffixPoint_x3f_1577_ = v_fst_1456_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1613_;
goto v___jp_1574_;
}
else
{
uint8_t v___x_1627_; 
v___x_1627_ = l_Lean_Expr_isFVar(v_letMutsTuple_1621_);
if (v___x_1627_ == 0)
{
lean_dec_ref(v_letMutsTuple_1621_);
lean_dec_ref(v_cursorSuffix_1620_);
lean_del_object(v___x_1617_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1605_);
v___y_1575_ = v___y_1606_;
v_prefixPoint_x3f_1576_ = v_prefixPoint_x3f_1609_;
v_suffixPoint_x3f_1577_ = v_fst_1456_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1613_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc_ref(v_xs_1430_);
v___x_1629_ = l_Lean_Meta_mkProjection(v_xs_1430_, v___x_1628_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = l_Lean_Meta_mkEq(v_a_1630_, v_cursorSuffix_1620_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___f_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = lean_box(v___x_1622_);
lean_inc_ref(v___x_1429_);
lean_inc_ref(v_letMutsTuple_1621_);
v___f_1634_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1634_, 0, v_letMutsTuple_1621_);
lean_closure_set(v___f_1634_, 1, v___x_1429_);
lean_closure_set(v___f_1634_, 2, v___x_1633_);
v___x_1635_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1635_, 0, v___y_1607_);
lean_closure_set(v___x_1635_, 1, v___f_1634_);
lean_inc(v_a_1448_);
v___x_1636_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1448_, v___x_1635_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = l_Lean_Expr_replaceFVar(v_a_1637_, v_letMutsTuple_1621_, v_letMuts_1431_);
lean_dec(v_a_1637_);
if (lean_obj_tag(v_fst_1456_) == 1)
{
lean_object* v_val_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_a_1632_);
lean_del_object(v___x_1617_);
lean_dec_ref(v___y_1608_);
v_val_1639_ = lean_ctor_get(v_fst_1456_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_fst_1456_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1641_ = v_fst_1456_;
v_isShared_1642_ = v_isSharedCheck_1657_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_dec(v_fst_1456_);
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
v___x_1649_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1605_, v_letMutsPred_1645_, v___x_1638_);
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
v___y_1575_ = v___y_1606_;
v_prefixPoint_x3f_1576_ = v_prefixPoint_x3f_1609_;
v_suffixPoint_x3f_1577_ = v___x_1653_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1613_;
goto v___jp_1574_;
}
}
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_dec(v_fst_1456_);
v___x_1658_ = lean_apply_1(v___y_1608_, v_a_1632_);
v___x_1659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___y_1605_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
lean_ctor_set(v___x_1659_, 2, v___x_1638_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1659_);
v___x_1661_ = v___x_1617_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v___y_1575_ = v___y_1606_;
v_prefixPoint_x3f_1576_ = v_prefixPoint_x3f_1609_;
v_suffixPoint_x3f_1577_ = v___x_1661_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1613_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_a_1632_);
lean_dec_ref(v_letMutsTuple_1621_);
lean_del_object(v___x_1617_);
lean_dec(v_prefixPoint_x3f_1609_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1454_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1663_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1636_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1636_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v_letMutsTuple_1621_);
lean_del_object(v___x_1617_);
lean_dec(v_prefixPoint_x3f_1609_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1454_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1671_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1631_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1631_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_letMutsTuple_1621_);
lean_dec_ref(v_cursorSuffix_1620_);
lean_del_object(v___x_1617_);
lean_dec(v_prefixPoint_x3f_1609_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1454_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1679_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1629_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1629_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
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
lean_dec(v___x_1614_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1605_);
v___y_1575_ = v___y_1606_;
v_prefixPoint_x3f_1576_ = v_prefixPoint_x3f_1609_;
v_suffixPoint_x3f_1577_ = v_fst_1456_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___y_1611_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___y_1613_;
goto v___jp_1574_;
}
}
v___jp_1688_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_inc_ref(v___y_1694_);
v___x_1696_ = lean_apply_1(v___y_1694_, v___y_1690_);
lean_inc(v___y_1691_);
v___x_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1697_, 0, v___y_1691_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
lean_ctor_set(v___x_1697_, 2, v_a_1695_);
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
v___y_1604_ = v___y_1689_;
v___y_1605_ = v___y_1691_;
v___y_1606_ = v___y_1692_;
v___y_1607_ = v___y_1693_;
v___y_1608_ = v___y_1694_;
v_prefixPoint_x3f_1609_ = v___x_1698_;
v___y_1610_ = v___y_1436_;
v___y_1611_ = v___y_1437_;
v___y_1612_ = v___y_1438_;
v___y_1613_ = v___y_1439_;
goto v___jp_1603_;
}
v___jp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_inc_ref(v_a_1700_);
v___x_1701_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1701_, 0, v_a_1700_);
lean_inc(v_a_1448_);
v___x_1702_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1448_, v___x_1701_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
if (lean_obj_tag(v_a_1703_) == 1)
{
lean_object* v_val_1704_; lean_object* v_snd_1705_; lean_object* v_fst_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1764_; 
v_val_1704_ = lean_ctor_get(v_a_1703_, 0);
lean_inc(v_val_1704_);
lean_dec_ref_known(v_a_1703_, 1);
v_snd_1705_ = lean_ctor_get(v_val_1704_, 1);
v_fst_1706_ = lean_ctor_get(v_val_1704_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_val_1704_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1708_ = v_val_1704_;
v_isShared_1709_ = v_isSharedCheck_1764_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snd_1705_);
lean_inc(v_fst_1706_);
lean_dec(v_val_1704_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1764_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_fst_1710_; lean_object* v_snd_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1763_; 
v_fst_1710_ = lean_ctor_get(v_snd_1705_, 0);
v_snd_1711_ = lean_ctor_get(v_snd_1705_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_snd_1705_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1713_ = v_snd_1705_;
v_isShared_1714_ = v_isSharedCheck_1763_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_snd_1711_);
lean_inc(v_fst_1710_);
lean_dec(v_snd_1705_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1763_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___f_1715_; lean_object* v___x_1716_; 
lean_inc(v_fst_1706_);
v___f_1715_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_1715_, 0, v_fst_1706_);
lean_inc(v_inv_1428_);
v___x_1716_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1711_, v_inv_1428_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_invariantUse_1717_; lean_object* v_conditionIdx_1718_; lean_object* v_cursorPrefix_1719_; lean_object* v_letMutsTuple_1720_; uint8_t v___x_1721_; 
v_invariantUse_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc_ref(v_invariantUse_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v_conditionIdx_1718_ = lean_ctor_get(v_invariantUse_1717_, 0);
lean_inc(v_conditionIdx_1718_);
v_cursorPrefix_1719_ = lean_ctor_get(v_invariantUse_1717_, 1);
lean_inc_ref(v_cursorPrefix_1719_);
v_letMutsTuple_1720_ = lean_ctor_get(v_invariantUse_1717_, 4);
lean_inc_ref(v_letMutsTuple_1720_);
lean_dec_ref(v_invariantUse_1717_);
v___x_1721_ = lean_nat_dec_eq(v_conditionIdx_1718_, v___x_1461_);
lean_dec(v_conditionIdx_1718_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1723_; 
lean_dec_ref(v_letMutsTuple_1720_);
lean_dec_ref(v_cursorPrefix_1719_);
lean_dec_ref(v___f_1715_);
lean_dec(v_snd_1711_);
lean_dec(v_fst_1710_);
lean_dec(v_fst_1706_);
lean_dec_ref(v_a_1700_);
lean_del_object(v___x_1459_);
lean_del_object(v___x_1454_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v_snd_1457_);
lean_ctor_set(v___x_1713_, 0, v_fst_1456_);
v___x_1723_ = v___x_1713_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_fst_1456_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_snd_1457_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v___x_1723_);
lean_ctor_set(v___x_1708_, 0, v_fst_1452_);
v___x_1725_ = v___x_1708_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_fst_1452_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v_a_1442_ = v___x_1725_;
goto v___jp_1441_;
}
}
}
else
{
lean_object* v___x_1728_; uint8_t v___x_1729_; 
lean_del_object(v___x_1713_);
lean_del_object(v___x_1708_);
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__2));
v___x_1729_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1719_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec_ref(v_letMutsTuple_1720_);
lean_dec_ref(v_cursorPrefix_1719_);
v___y_1604_ = v_fst_1710_;
v___y_1605_ = v_fst_1706_;
v___y_1606_ = v_a_1700_;
v___y_1607_ = v_snd_1711_;
v___y_1608_ = v___f_1715_;
v_prefixPoint_x3f_1609_ = v_fst_1452_;
v___y_1610_ = v___y_1436_;
v___y_1611_ = v___y_1437_;
v___y_1612_ = v___y_1438_;
v___y_1613_ = v___y_1439_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_fst_1452_);
v___x_1730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1430_);
v___x_1731_ = l_Lean_Meta_mkProjection(v_xs_1430_, v___x_1730_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1733_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
v___x_1733_ = l_Lean_Meta_mkEq(v_a_1732_, v_cursorPrefix_1719_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1735_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
lean_inc_ref(v_letMuts_1431_);
v___x_1735_ = l_Lean_Meta_mkEq(v_letMuts_1431_, v_letMutsTuple_1720_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
lean_inc(v_fst_1706_);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_fst_1706_, v_a_1736_);
v___y_1689_ = v_fst_1710_;
v___y_1690_ = v_a_1734_;
v___y_1691_ = v_fst_1706_;
v___y_1692_ = v_a_1700_;
v___y_1693_ = v_snd_1711_;
v___y_1694_ = v___f_1715_;
v_a_1695_ = v___x_1737_;
goto v___jp_1688_;
}
else
{
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1735_, 1);
v___y_1689_ = v_fst_1710_;
v___y_1690_ = v_a_1734_;
v___y_1691_ = v_fst_1706_;
v___y_1692_ = v_a_1700_;
v___y_1693_ = v_snd_1711_;
v___y_1694_ = v___f_1715_;
v_a_1695_ = v_a_1738_;
goto v___jp_1688_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_a_1734_);
lean_dec_ref(v___f_1715_);
lean_dec(v_snd_1711_);
lean_dec(v_fst_1710_);
lean_dec(v_fst_1706_);
lean_dec_ref(v_a_1700_);
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1454_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1739_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1735_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1735_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v_letMutsTuple_1720_);
lean_dec_ref(v___f_1715_);
lean_dec(v_snd_1711_);
lean_dec(v_fst_1710_);
lean_dec(v_fst_1706_);
lean_dec_ref(v_a_1700_);
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1454_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1747_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1733_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1733_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v_letMutsTuple_1720_);
lean_dec_ref(v_cursorPrefix_1719_);
lean_dec_ref(v___f_1715_);
lean_dec(v_snd_1711_);
lean_dec(v_fst_1710_);
lean_dec(v_fst_1706_);
lean_dec_ref(v_a_1700_);
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1454_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1755_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1731_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1731_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1716_);
lean_del_object(v___x_1713_);
lean_del_object(v___x_1708_);
v___y_1604_ = v_fst_1710_;
v___y_1605_ = v_fst_1706_;
v___y_1606_ = v_a_1700_;
v___y_1607_ = v_snd_1711_;
v___y_1608_ = v___f_1715_;
v_prefixPoint_x3f_1609_ = v_fst_1452_;
v___y_1610_ = v___y_1436_;
v___y_1611_ = v___y_1437_;
v___y_1612_ = v___y_1438_;
v___y_1613_ = v___y_1439_;
goto v___jp_1603_;
}
}
}
}
else
{
lean_dec(v_a_1703_);
v___y_1575_ = v_a_1700_;
v_prefixPoint_x3f_1576_ = v_fst_1452_;
v_suffixPoint_x3f_1577_ = v_fst_1456_;
v___y_1578_ = v___y_1436_;
v___y_1579_ = v___y_1437_;
v___y_1580_ = v___y_1438_;
v___y_1581_ = v___y_1439_;
goto v___jp_1574_;
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v_a_1700_);
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1454_);
lean_dec(v_fst_1452_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1765_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1702_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1702_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_b_1435_);
lean_dec_ref(v_letMuts_1431_);
lean_dec_ref(v_xs_1430_);
lean_dec_ref(v___x_1429_);
lean_dec(v_inv_1428_);
v_a_1788_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1449_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1449_);
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
v___jp_1441_:
{
size_t v___x_1443_; size_t v___x_1444_; 
v___x_1443_ = ((size_t)1ULL);
v___x_1444_ = lean_usize_add(v_i_1434_, v___x_1443_);
v_i_1434_ = v___x_1444_;
v_b_1435_ = v_a_1442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1796_, lean_object* v___x_1797_, lean_object* v_xs_1798_, lean_object* v_letMuts_1799_, lean_object* v_as_1800_, lean_object* v_sz_1801_, lean_object* v_i_1802_, lean_object* v_b_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
size_t v_sz_boxed_1809_; size_t v_i_boxed_1810_; lean_object* v_res_1811_; 
v_sz_boxed_1809_ = lean_unbox_usize(v_sz_1801_);
lean_dec(v_sz_1801_);
v_i_boxed_1810_ = lean_unbox_usize(v_i_1802_);
lean_dec(v_i_1802_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1796_, v___x_1797_, v_xs_1798_, v_letMuts_1799_, v_as_1800_, v_sz_boxed_1809_, v_i_boxed_1810_, v_b_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec_ref(v_as_1800_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1821_, lean_object* v_inv_1822_, lean_object* v_xs_1823_, lean_object* v_letMuts_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_lctx_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; size_t v_sz_1833_; size_t v___x_1834_; lean_object* v___x_1835_; 
v_lctx_1830_ = lean_ctor_get(v_a_1825_, 2);
v___x_1831_ = lean_box(0);
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1833_ = lean_array_size(v_vcs_1821_);
v___x_1834_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1830_);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1822_, v_lctx_1830_, v_xs_1823_, v_letMuts_1824_, v_vcs_1821_, v_sz_1833_, v___x_1834_, v___x_1832_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1879_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1879_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1879_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v_snd_1844_; lean_object* v_fst_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1878_; 
v_snd_1844_ = lean_ctor_get(v_a_1836_, 1);
v_fst_1845_ = lean_ctor_get(v_a_1836_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_a_1836_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1847_ = v_a_1836_;
v_isShared_1848_ = v_isSharedCheck_1878_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_snd_1844_);
lean_inc(v_fst_1845_);
lean_dec(v_a_1836_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1878_;
goto v_resetjp_1846_;
}
v___jp_1840_:
{
lean_object* v___x_1842_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1831_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1831_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
v_resetjp_1846_:
{
if (lean_obj_tag(v_fst_1845_) == 0)
{
lean_del_object(v___x_1847_);
lean_dec(v_snd_1844_);
goto v___jp_1840_;
}
else
{
lean_object* v_fst_1849_; 
v_fst_1849_ = lean_ctor_get(v_snd_1844_, 0);
lean_inc(v_fst_1849_);
if (lean_obj_tag(v_fst_1849_) == 0)
{
lean_dec_ref_known(v_fst_1845_, 1);
lean_del_object(v___x_1847_);
lean_dec(v_snd_1844_);
goto v___jp_1840_;
}
else
{
lean_object* v_snd_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1876_; 
lean_del_object(v___x_1838_);
v_snd_1850_ = lean_ctor_get(v_snd_1844_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_snd_1844_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; 
v_unused_1877_ = lean_ctor_get(v_snd_1844_, 0);
lean_dec(v_unused_1877_);
v___x_1852_ = v_snd_1844_;
v_isShared_1853_ = v_isSharedCheck_1876_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_snd_1850_);
lean_dec(v_snd_1844_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1876_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_val_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1875_; 
v_val_1854_ = lean_ctor_get(v_fst_1845_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_fst_1845_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1856_ = v_fst_1845_;
v_isShared_1857_ = v_isSharedCheck_1875_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_val_1854_);
lean_dec(v_fst_1845_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1875_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_val_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1874_; 
v_val_1858_ = lean_ctor_get(v_fst_1849_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_fst_1849_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1860_ = v_fst_1849_;
v_isShared_1861_ = v_isSharedCheck_1874_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_val_1858_);
lean_dec(v_fst_1849_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1874_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_val_1858_);
v___x_1863_ = v___x_1852_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_val_1858_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_snd_1850_);
v___x_1863_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1865_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1863_);
lean_ctor_set(v___x_1847_, 0, v_val_1854_);
v___x_1865_ = v___x_1847_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_val_1854_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1865_);
v___x_1867_ = v___x_1860_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set_tag(v___x_1856_, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1867_);
v___x_1869_ = v___x_1856_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
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
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1835_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1835_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1888_, lean_object* v_inv_1889_, lean_object* v_xs_1890_, lean_object* v_letMuts_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1888_, v_inv_1889_, v_xs_1890_, v_letMuts_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec_ref(v_vcs_1888_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_1898_, lean_object* v_a_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1899_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_1906_, lean_object* v_a_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_1906_, v_a_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_MVarId_getDecl(v_m_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_userName_1922_; lean_object* v_lctx_1923_; lean_object* v_type_1924_; lean_object* v_localInstances_1925_; uint8_t v_kind_1926_; lean_object* v_numScopeArgs_1927_; lean_object* v___x_1928_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v_userName_1922_ = lean_ctor_get(v_a_1921_, 0);
lean_inc(v_userName_1922_);
v_lctx_1923_ = lean_ctor_get(v_a_1921_, 1);
lean_inc_ref(v_lctx_1923_);
v_type_1924_ = lean_ctor_get(v_a_1921_, 2);
lean_inc_ref(v_type_1924_);
v_localInstances_1925_ = lean_ctor_get(v_a_1921_, 4);
lean_inc_ref(v_localInstances_1925_);
v_kind_1926_ = lean_ctor_get_uint8(v_a_1921_, sizeof(void*)*7);
v_numScopeArgs_1927_ = lean_ctor_get(v_a_1921_, 5);
lean_inc(v_numScopeArgs_1927_);
lean_dec(v_a_1921_);
v___x_1928_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1923_, v_localInstances_1925_, v_type_1924_, v_kind_1926_, v_userName_1922_, v_numScopeArgs_1927_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1937_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = l_Lean_Expr_mvarId_x21(v_a_1929_);
lean_dec(v_a_1929_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_a_1938_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1928_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1928_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1920_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1920_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_1961_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = l_String_instInhabitedSlice;
v___x_1963_ = lean_panic_fn_borrowed(v___x_1962_, v_msg_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_1964_, lean_object* v_a_1965_, uint8_t v_b_1966_){
_start:
{
lean_object* v_str_1967_; lean_object* v_startInclusive_1968_; lean_object* v_endExclusive_1969_; lean_object* v___x_1970_; uint8_t v_decide_1971_; 
v_str_1967_ = lean_ctor_get(v_s_1964_, 0);
v_startInclusive_1968_ = lean_ctor_get(v_s_1964_, 1);
v_endExclusive_1969_ = lean_ctor_get(v_s_1964_, 2);
v___x_1970_ = lean_nat_sub(v_endExclusive_1969_, v_startInclusive_1968_);
v_decide_1971_ = lean_nat_dec_eq(v_a_1965_, v___x_1970_);
lean_dec(v___x_1970_);
if (v_decide_1971_ == 0)
{
uint32_t v___x_1972_; lean_object* v___x_1973_; uint32_t v___x_1974_; uint8_t v___x_1975_; 
v___x_1972_ = 64;
v___x_1973_ = lean_nat_add(v_startInclusive_1968_, v_a_1965_);
lean_dec(v_a_1965_);
v___x_1974_ = lean_string_utf8_get_fast(v_str_1967_, v___x_1973_);
v___x_1975_ = lean_uint32_dec_eq(v___x_1974_, v___x_1972_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_string_utf8_next_fast(v_str_1967_, v___x_1973_);
lean_dec(v___x_1973_);
v___x_1977_ = lean_nat_sub(v___x_1976_, v_startInclusive_1968_);
v_a_1965_ = v___x_1977_;
v_b_1966_ = v___x_1975_;
goto _start;
}
else
{
lean_dec(v___x_1973_);
return v___x_1975_;
}
}
else
{
lean_dec(v_a_1965_);
return v_b_1966_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object* v_s_1979_, lean_object* v_a_1980_, lean_object* v_b_1981_){
_start:
{
uint8_t v_b_boxed_1982_; uint8_t v_res_1983_; lean_object* v_r_1984_; 
v_b_boxed_1982_ = lean_unbox(v_b_1981_);
v_res_1983_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1979_, v_a_1980_, v_b_boxed_1982_);
lean_dec_ref(v_s_1979_);
v_r_1984_ = lean_box(v_res_1983_);
return v_r_1984_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_1985_){
_start:
{
lean_object* v_searcher_1986_; uint8_t v___x_1987_; uint8_t v___x_1988_; 
v_searcher_1986_ = lean_unsigned_to_nat(0u);
v___x_1987_ = 0;
v___x_1988_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1985_, v_searcher_1986_, v___x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_1989_);
lean_dec_ref(v_s_1989_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_1996_ = lean_unsigned_to_nat(14u);
v___x_1997_ = lean_unsigned_to_nat(22u);
v___x_1998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_1999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_2000_ = l_mkPanicMessageWithDecl(v___x_1999_, v___x_1998_, v___x_1997_, v___x_1996_, v___x_1995_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_2001_){
_start:
{
switch(lean_obj_tag(v_x_2001_))
{
case 1:
{
lean_object* v_info_2002_; lean_object* v_kind_2003_; lean_object* v_args_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2014_; 
v_info_2002_ = lean_ctor_get(v_x_2001_, 0);
v_kind_2003_ = lean_ctor_get(v_x_2001_, 1);
v_args_2004_ = lean_ctor_get(v_x_2001_, 2);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_x_2001_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2006_ = v_x_2001_;
v_isShared_2007_ = v_isSharedCheck_2014_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_args_2004_);
lean_inc(v_kind_2003_);
lean_inc(v_info_2002_);
lean_dec(v_x_2001_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2014_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
size_t v_sz_2008_; size_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v_sz_2008_ = lean_array_size(v_args_2004_);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_2008_, v___x_2009_, v_args_2004_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 2, v___x_2010_);
v___x_2012_ = v___x_2006_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_info_2002_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_kind_2003_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
case 3:
{
lean_object* v_info_2015_; lean_object* v_rawVal_2016_; lean_object* v_val_2017_; lean_object* v_preresolved_2018_; uint8_t v___y_2020_; lean_object* v_str_2033_; lean_object* v_startPos_2034_; lean_object* v_stopPos_2035_; uint8_t v___y_2037_; uint8_t v___x_2043_; uint8_t v___y_2045_; uint8_t v___x_2046_; 
v_info_2015_ = lean_ctor_get(v_x_2001_, 0);
v_rawVal_2016_ = lean_ctor_get(v_x_2001_, 1);
v_val_2017_ = lean_ctor_get(v_x_2001_, 2);
v_preresolved_2018_ = lean_ctor_get(v_x_2001_, 3);
v_str_2033_ = lean_ctor_get(v_rawVal_2016_, 0);
v_startPos_2034_ = lean_ctor_get(v_rawVal_2016_, 1);
v_stopPos_2035_ = lean_ctor_get(v_rawVal_2016_, 2);
v___x_2043_ = lean_string_is_valid_pos(v_str_2033_, v_startPos_2034_);
v___x_2046_ = lean_string_is_valid_pos(v_str_2033_, v_stopPos_2035_);
if (v___x_2046_ == 0)
{
v___y_2045_ = v___x_2046_;
goto v___jp_2044_;
}
else
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_nat_dec_le(v_startPos_2034_, v_stopPos_2035_);
v___y_2045_ = v___x_2047_;
goto v___jp_2044_;
}
v___jp_2019_:
{
if (v___y_2020_ == 0)
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
lean_inc(v_preresolved_2018_);
lean_inc(v_val_2017_);
lean_inc_ref(v_rawVal_2016_);
lean_inc(v_info_2015_);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_x_2001_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; 
v_unused_2029_ = lean_ctor_get(v_x_2001_, 3);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_x_2001_, 2);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_x_2001_, 1);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_x_2001_, 0);
lean_dec(v_unused_2032_);
v___x_2022_ = v_x_2001_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v_x_2001_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = l_Lean_Name_eraseMacroScopes(v_val_2017_);
lean_dec(v_val_2017_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 2, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_info_2015_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_rawVal_2016_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_preresolved_2018_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
return v_x_2001_;
}
}
v___jp_2036_:
{
if (v___y_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2038_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_2039_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_2038_);
v___x_2040_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2039_);
lean_dec_ref(v___x_2039_);
v___y_2020_ = v___x_2040_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2041_; uint8_t v___x_2042_; 
lean_inc(v_stopPos_2035_);
lean_inc(v_startPos_2034_);
lean_inc_ref(v_str_2033_);
v___x_2041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2041_, 0, v_str_2033_);
lean_ctor_set(v___x_2041_, 1, v_startPos_2034_);
lean_ctor_set(v___x_2041_, 2, v_stopPos_2035_);
v___x_2042_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2041_);
lean_dec_ref_known(v___x_2041_, 3);
v___y_2020_ = v___x_2042_;
goto v___jp_2019_;
}
}
v___jp_2044_:
{
if (v___x_2043_ == 0)
{
v___y_2037_ = v___x_2043_;
goto v___jp_2036_;
}
else
{
v___y_2037_ = v___y_2045_;
goto v___jp_2036_;
}
}
}
default: 
{
return v_x_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_2048_, size_t v_i_2049_, lean_object* v_bs_2050_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2049_, v_sz_2048_);
if (v___x_2051_ == 0)
{
return v_bs_2050_;
}
else
{
lean_object* v_v_2052_; lean_object* v___x_2053_; lean_object* v_bs_x27_2054_; lean_object* v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v_v_2052_ = lean_array_uget(v_bs_2050_, v_i_2049_);
v___x_2053_ = lean_unsigned_to_nat(0u);
v_bs_x27_2054_ = lean_array_uset(v_bs_2050_, v_i_2049_, v___x_2053_);
v___x_2055_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_2052_);
v___x_2056_ = ((size_t)1ULL);
v___x_2057_ = lean_usize_add(v_i_2049_, v___x_2056_);
v___x_2058_ = lean_array_uset(v_bs_x27_2054_, v_i_2049_, v___x_2055_);
v_i_2049_ = v___x_2057_;
v_bs_2050_ = v___x_2058_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2060_, lean_object* v_i_2061_, lean_object* v_bs_2062_){
_start:
{
size_t v_sz_boxed_2063_; size_t v_i_boxed_2064_; lean_object* v_res_2065_; 
v_sz_boxed_2063_ = lean_unbox_usize(v_sz_2060_);
lean_dec(v_sz_2060_);
v_i_boxed_2064_ = lean_unbox_usize(v_i_2061_);
lean_dec(v_i_2061_);
v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2063_, v_i_boxed_2064_, v_bs_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2066_, lean_object* v_inst_2067_, lean_object* v_R_2068_, lean_object* v_a_2069_, uint8_t v_b_2070_, lean_object* v_c_2071_){
_start:
{
uint8_t v___x_2072_; 
v___x_2072_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2066_, v_a_2069_, v_b_2070_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2073_, lean_object* v_inst_2074_, lean_object* v_R_2075_, lean_object* v_a_2076_, lean_object* v_b_2077_, lean_object* v_c_2078_){
_start:
{
uint8_t v_b_boxed_2079_; uint8_t v_res_2080_; lean_object* v_r_2081_; 
v_b_boxed_2079_ = lean_unbox(v_b_2077_);
v_res_2080_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2073_, v_inst_2074_, v_R_2075_, v_a_2076_, v_b_boxed_2079_, v_c_2078_);
lean_dec_ref(v_s_2073_);
v_r_2081_ = lean_box(v_res_2080_);
return v_r_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2082_, lean_object* v_h__1_2083_, lean_object* v_h__2_2084_, lean_object* v_h__3_2085_, lean_object* v_h__4_2086_){
_start:
{
switch(lean_obj_tag(v_x_2082_))
{
case 0:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v_h__3_2085_);
lean_dec(v_h__2_2084_);
lean_dec(v_h__1_2083_);
v___x_2087_ = lean_box(0);
v___x_2088_ = lean_apply_1(v_h__4_2086_, v___x_2087_);
return v___x_2088_;
}
case 1:
{
lean_object* v_info_2089_; lean_object* v_kind_2090_; lean_object* v_args_2091_; lean_object* v___x_2092_; 
lean_dec(v_h__4_2086_);
lean_dec(v_h__3_2085_);
lean_dec(v_h__1_2083_);
v_info_2089_ = lean_ctor_get(v_x_2082_, 0);
lean_inc(v_info_2089_);
v_kind_2090_ = lean_ctor_get(v_x_2082_, 1);
lean_inc(v_kind_2090_);
v_args_2091_ = lean_ctor_get(v_x_2082_, 2);
lean_inc_ref(v_args_2091_);
lean_dec_ref_known(v_x_2082_, 3);
v___x_2092_ = lean_apply_3(v_h__2_2084_, v_info_2089_, v_kind_2090_, v_args_2091_);
return v___x_2092_;
}
case 2:
{
lean_object* v_info_2093_; lean_object* v_val_2094_; lean_object* v___x_2095_; 
lean_dec(v_h__4_2086_);
lean_dec(v_h__2_2084_);
lean_dec(v_h__1_2083_);
v_info_2093_ = lean_ctor_get(v_x_2082_, 0);
lean_inc(v_info_2093_);
v_val_2094_ = lean_ctor_get(v_x_2082_, 1);
lean_inc_ref(v_val_2094_);
lean_dec_ref_known(v_x_2082_, 2);
v___x_2095_ = lean_apply_2(v_h__3_2085_, v_info_2093_, v_val_2094_);
return v___x_2095_;
}
default: 
{
lean_object* v_info_2096_; lean_object* v_rawVal_2097_; lean_object* v_val_2098_; lean_object* v_preresolved_2099_; lean_object* v___x_2100_; 
lean_dec(v_h__4_2086_);
lean_dec(v_h__3_2085_);
lean_dec(v_h__2_2084_);
v_info_2096_ = lean_ctor_get(v_x_2082_, 0);
lean_inc(v_info_2096_);
v_rawVal_2097_ = lean_ctor_get(v_x_2082_, 1);
lean_inc_ref(v_rawVal_2097_);
v_val_2098_ = lean_ctor_get(v_x_2082_, 2);
lean_inc(v_val_2098_);
v_preresolved_2099_ = lean_ctor_get(v_x_2082_, 3);
lean_inc(v_preresolved_2099_);
lean_dec_ref_known(v_x_2082_, 4);
v___x_2100_ = lean_apply_4(v_h__1_2083_, v_info_2096_, v_rawVal_2097_, v_val_2098_, v_preresolved_2099_);
return v___x_2100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2101_, lean_object* v_x_2102_, lean_object* v_h__1_2103_, lean_object* v_h__2_2104_, lean_object* v_h__3_2105_, lean_object* v_h__4_2106_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2121_, lean_object* v_h__1_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_apply_2(v_h__1_2122_, v_x_2121_, lean_box(0));
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2124_, lean_object* v_P_2125_, lean_object* v_motive_2126_, lean_object* v_x_2127_, lean_object* v_h__1_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_apply_2(v_h__1_2128_, v_x_2127_, lean_box(0));
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2132_, lean_object* v_syn_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2135_, lean_object* v_syn_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2135_, v_syn_2136_);
lean_dec(v_name_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2144_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2172_ = lean_unsigned_to_nat(2u);
v___x_2173_ = l_Lean_Expr_isAppOfArity(v_e_2144_, v___x_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2175_ = lean_unsigned_to_nat(3u);
v___x_2176_ = l_Lean_Expr_isAppOfArity(v_e_2144_, v___x_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2178_ = l_Lean_Expr_isAppOfArity(v_e_2144_, v___x_2177_, v___x_2175_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2180_ = l_Lean_Expr_isAppOfArity(v_e_2144_, v___x_2179_, v___x_2175_);
if (v___x_2180_ == 0)
{
goto v___jp_2145_;
}
else
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_Expr_appArg_x21(v_e_2144_);
if (lean_obj_tag(v___x_2181_) == 6)
{
lean_object* v_binderName_2182_; lean_object* v_binderType_2183_; lean_object* v_body_2184_; uint8_t v_binderInfo_2185_; lean_object* v___x_2186_; 
lean_dec_ref(v_e_2144_);
v_binderName_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_binderName_2182_);
v_binderType_2183_ = lean_ctor_get(v___x_2181_, 1);
lean_inc_ref(v_binderType_2183_);
v_body_2184_ = lean_ctor_get(v___x_2181_, 2);
lean_inc_ref(v_body_2184_);
v_binderInfo_2185_ = lean_ctor_get_uint8(v___x_2181_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_2181_, 3);
v___x_2186_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2184_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_dec_ref(v_binderType_2183_);
lean_dec(v_binderName_2182_);
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
v___x_2196_ = l_Lean_mkForall(v_binderName_2182_, v_binderInfo_2185_, v_binderType_2183_, v_snd_2192_);
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
else
{
lean_dec_ref(v___x_2181_);
goto v___jp_2145_;
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = l_Lean_Expr_appFn_x21(v_e_2144_);
v___x_2206_ = l_Lean_Expr_appArg_x21(v___x_2205_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2206_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_dec_ref(v_e_2144_);
return v___x_2207_;
}
else
{
lean_object* v_val_2208_; lean_object* v_snd_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_val_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v_snd_2209_ = lean_ctor_get(v_val_2208_, 1);
lean_inc(v_snd_2209_);
lean_dec(v_val_2208_);
v___x_2210_ = l_Lean_Expr_appArg_x21(v_e_2144_);
lean_dec_ref(v_e_2144_);
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
v___x_2221_ = l_Lean_mkOr(v_snd_2209_, v_snd_2217_);
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
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = l_Lean_Expr_appFn_x21(v_e_2144_);
v___x_2231_ = l_Lean_Expr_appArg_x21(v___x_2230_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2231_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_dec_ref(v_e_2144_);
return v___x_2232_;
}
else
{
lean_object* v_val_2233_; lean_object* v_snd_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_val_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v_snd_2234_ = lean_ctor_get(v_val_2233_, 1);
lean_inc(v_snd_2234_);
lean_dec(v_val_2233_);
v___x_2235_ = l_Lean_Expr_appArg_x21(v_e_2144_);
lean_dec_ref(v_e_2144_);
v___x_2236_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2235_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_dec(v_snd_2234_);
return v___x_2236_;
}
else
{
lean_object* v_val_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2254_; 
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2254_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_val_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2254_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_fst_2241_; lean_object* v_snd_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2253_; 
v_fst_2241_ = lean_ctor_get(v_val_2237_, 0);
v_snd_2242_ = lean_ctor_get(v_val_2237_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_val_2237_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2244_ = v_val_2237_;
v_isShared_2245_ = v_isSharedCheck_2253_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snd_2242_);
lean_inc(v_fst_2241_);
lean_dec(v_val_2237_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2253_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = l_Lean_mkAnd(v_snd_2234_, v_snd_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 1, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_fst_2241_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2250_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2248_);
v___x_2250_ = v___x_2239_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
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
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Lean_Expr_getAppFn(v_e_2144_);
v___x_2257_ = l_Lean_Expr_constLevels_x21(v___x_2256_);
lean_dec_ref(v___x_2256_);
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = l_List_get_x21Internal___redArg(v___x_2255_, v___x_2257_, v___x_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = l_Lean_Expr_getAppNumArgs(v_e_2144_);
v___x_2262_ = lean_nat_sub(v___x_2261_, v___x_2260_);
lean_dec(v___x_2261_);
v___x_2263_ = lean_nat_sub(v___x_2262_, v___x_2260_);
lean_dec(v___x_2262_);
v___x_2264_ = l_Lean_Expr_getRevArg_x21(v_e_2144_, v___x_2263_);
lean_dec_ref(v_e_2144_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2259_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
v___jp_2145_:
{
if (lean_obj_tag(v_e_2144_) == 8)
{
lean_object* v_declName_2146_; lean_object* v_type_2147_; lean_object* v_value_2148_; lean_object* v_body_2149_; uint8_t v_nondep_2150_; lean_object* v___x_2151_; 
v_declName_2146_ = lean_ctor_get(v_e_2144_, 0);
lean_inc(v_declName_2146_);
v_type_2147_ = lean_ctor_get(v_e_2144_, 1);
lean_inc_ref(v_type_2147_);
v_value_2148_ = lean_ctor_get(v_e_2144_, 2);
lean_inc_ref(v_value_2148_);
v_body_2149_ = lean_ctor_get(v_e_2144_, 3);
lean_inc_ref(v_body_2149_);
v_nondep_2150_ = lean_ctor_get_uint8(v_e_2144_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2144_, 4);
v___x_2151_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2149_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_dec_ref(v_value_2148_);
lean_dec_ref(v_type_2147_);
lean_dec(v_declName_2146_);
return v___x_2151_;
}
else
{
lean_object* v_val_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2169_; 
v_val_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2169_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_val_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2169_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v_fst_2156_; lean_object* v_snd_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2168_; 
v_fst_2156_ = lean_ctor_get(v_val_2152_, 0);
v_snd_2157_ = lean_ctor_get(v_val_2152_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_val_2152_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2159_ = v_val_2152_;
v_isShared_2160_ = v_isSharedCheck_2168_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_snd_2157_);
lean_inc(v_fst_2156_);
lean_dec(v_val_2152_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2168_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = l_Lean_Expr_letE___override(v_declName_2146_, v_type_2147_, v_value_2148_, v_snd_2157_, v_nondep_2150_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v___x_2161_);
v___x_2163_ = v___x_2159_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_fst_2156_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2163_);
v___x_2165_ = v___x_2154_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
else
{
lean_object* v___x_2170_; 
lean_dec_ref(v_e_2144_);
v___x_2170_ = lean_box(0);
return v___x_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2267_){
_start:
{
lean_object* v___x_2268_; 
lean_inc_ref(v_e_2267_);
v___x_2268_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2267_);
if (lean_obj_tag(v___x_2268_) == 0)
{
return v_e_2267_;
}
else
{
lean_object* v_val_2269_; lean_object* v_fst_2270_; lean_object* v_snd_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v_e_2267_);
v_val_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v_fst_2270_ = lean_ctor_get(v_val_2269_, 0);
lean_inc_n(v_fst_2270_, 2);
v_snd_2271_ = lean_ctor_get(v_val_2269_, 1);
lean_inc(v_snd_2271_);
lean_dec(v_val_2269_);
v___x_2272_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2270_);
v___x_2273_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2270_, v___x_2272_, v_snd_2271_);
return v___x_2273_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Array_mkArray0(lean_box(0));
return v___x_2284_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2323_ = l_String_toRawSubstring_x27(v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2340_ = l_String_toRawSubstring_x27(v___x_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2355_, lean_object* v_default_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v_handlers_2363_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2363_ = l_Lean_Syntax_SepArray_ofElems(v___x_2362_, v_handlers_2355_);
switch(lean_obj_tag(v_default_2356_))
{
case 0:
{
lean_object* v_ref_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_ref_2364_ = lean_ctor_get(v_a_2359_, 2);
v___x_2365_ = 0;
v___x_2366_ = l_Lean_SourceInfo_fromRef(v_ref_2364_, v___x_2365_);
v___x_2367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2366_, 3);
v___x_2369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2366_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2371_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2372_ = l_Array_append___redArg(v___x_2371_, v_handlers_2363_);
lean_dec_ref(v_handlers_2363_);
v___x_2373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2366_);
lean_ctor_set(v___x_2373_, 1, v___x_2370_);
lean_ctor_set(v___x_2373_, 2, v___x_2372_);
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2366_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Lean_Syntax_node3(v___x_2366_, v___x_2367_, v___x_2369_, v___x_2373_, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
case 1:
{
lean_object* v_toCold_2378_; lean_object* v_ref_2379_; lean_object* v_quotContext_2380_; lean_object* v_currMacroScope_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_toCold_2378_ = lean_ctor_get(v_a_2359_, 0);
v_ref_2379_ = lean_ctor_get(v_a_2359_, 2);
v_quotContext_2380_ = lean_ctor_get(v_toCold_2378_, 8);
v_currMacroScope_2381_ = lean_ctor_get(v_toCold_2378_, 9);
v___x_2382_ = 0;
v___x_2383_ = l_Lean_SourceInfo_fromRef(v_ref_2379_, v___x_2382_);
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2383_, 12);
v___x_2386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2383_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2383_);
lean_ctor_set(v___x_2392_, 1, v___x_2390_);
v___x_2393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2383_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2397_ = l_Array_append___redArg(v___x_2396_, v_handlers_2363_);
lean_dec_ref(v_handlers_2363_);
v___x_2398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2383_);
lean_ctor_set(v___x_2398_, 1, v___x_2362_);
v___x_2399_ = lean_array_push(v___x_2397_, v___x_2398_);
v___x_2400_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2381_);
lean_inc(v_quotContext_2380_);
v___x_2402_ = l_Lean_addMacroScope(v_quotContext_2380_, v___x_2401_, v_currMacroScope_2381_);
v___x_2403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2404_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2383_);
lean_ctor_set(v___x_2404_, 1, v___x_2400_);
lean_ctor_set(v___x_2404_, 2, v___x_2402_);
lean_ctor_set(v___x_2404_, 3, v___x_2403_);
v___x_2405_ = lean_array_push(v___x_2399_, v___x_2404_);
v___x_2406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2383_);
lean_ctor_set(v___x_2406_, 1, v___x_2389_);
lean_ctor_set(v___x_2406_, 2, v___x_2405_);
v___x_2407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2383_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = l_Lean_Syntax_node3(v___x_2383_, v___x_2393_, v___x_2395_, v___x_2406_, v___x_2408_);
v___x_2410_ = l_Lean_Syntax_node2(v___x_2383_, v___x_2391_, v___x_2392_, v___x_2409_);
v___x_2411_ = l_Lean_Syntax_node1(v___x_2383_, v___x_2389_, v___x_2410_);
v___x_2412_ = l_Lean_Syntax_node1(v___x_2383_, v___x_2388_, v___x_2411_);
v___x_2413_ = l_Lean_Syntax_node1(v___x_2383_, v___x_2387_, v___x_2412_);
v___x_2414_ = l_Lean_Syntax_node2(v___x_2383_, v___x_2384_, v___x_2386_, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
case 2:
{
lean_object* v_toCold_2416_; lean_object* v_ref_2417_; lean_object* v_quotContext_2418_; lean_object* v_currMacroScope_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_toCold_2416_ = lean_ctor_get(v_a_2359_, 0);
v_ref_2417_ = lean_ctor_get(v_a_2359_, 2);
v_quotContext_2418_ = lean_ctor_get(v_toCold_2416_, 8);
v_currMacroScope_2419_ = lean_ctor_get(v_toCold_2416_, 9);
v___x_2420_ = 0;
v___x_2421_ = l_Lean_SourceInfo_fromRef(v_ref_2417_, v___x_2420_);
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2423_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2421_, 12);
v___x_2424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2421_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2421_);
lean_ctor_set(v___x_2430_, 1, v___x_2428_);
v___x_2431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2421_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2435_ = l_Array_append___redArg(v___x_2434_, v_handlers_2363_);
lean_dec_ref(v_handlers_2363_);
v___x_2436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2421_);
lean_ctor_set(v___x_2436_, 1, v___x_2362_);
v___x_2437_ = lean_array_push(v___x_2435_, v___x_2436_);
v___x_2438_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2439_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
lean_inc(v_currMacroScope_2419_);
lean_inc(v_quotContext_2418_);
v___x_2440_ = l_Lean_addMacroScope(v_quotContext_2418_, v___x_2439_, v_currMacroScope_2419_);
v___x_2441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
v___x_2442_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2421_);
lean_ctor_set(v___x_2442_, 1, v___x_2438_);
lean_ctor_set(v___x_2442_, 2, v___x_2440_);
lean_ctor_set(v___x_2442_, 3, v___x_2441_);
v___x_2443_ = lean_array_push(v___x_2437_, v___x_2442_);
v___x_2444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2421_);
lean_ctor_set(v___x_2444_, 1, v___x_2427_);
lean_ctor_set(v___x_2444_, 2, v___x_2443_);
v___x_2445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2421_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = l_Lean_Syntax_node3(v___x_2421_, v___x_2431_, v___x_2433_, v___x_2444_, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2429_, v___x_2430_, v___x_2447_);
v___x_2449_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2427_, v___x_2448_);
v___x_2450_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2426_, v___x_2449_);
v___x_2451_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2425_, v___x_2450_);
v___x_2452_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2422_, v___x_2424_, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
default: 
{
lean_object* v_e_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_e_2454_ = lean_ctor_get(v_default_2356_, 0);
lean_inc_ref(v_e_2454_);
lean_dec_ref_known(v_default_2356_, 1);
v___x_2455_ = lean_box(1);
v___x_2456_ = l_Lean_PrettyPrinter_delab(v_e_2454_, v___x_2455_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2493_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2493_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2493_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_ref_2461_; uint8_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v_ref_2461_ = lean_ctor_get(v_a_2359_, 2);
v___x_2462_ = 0;
v___x_2463_ = l_Lean_SourceInfo_fromRef(v_ref_2461_, v___x_2462_);
v___x_2464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2463_, 11);
v___x_2466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2463_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2463_);
lean_ctor_set(v___x_2472_, 1, v___x_2470_);
v___x_2473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2463_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2477_ = l_Array_append___redArg(v___x_2476_, v_handlers_2363_);
lean_dec_ref(v_handlers_2363_);
v___x_2478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2463_);
lean_ctor_set(v___x_2478_, 1, v___x_2362_);
v___x_2479_ = lean_array_push(v___x_2477_, v___x_2478_);
v___x_2480_ = lean_array_push(v___x_2479_, v_a_2457_);
v___x_2481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2463_);
lean_ctor_set(v___x_2481_, 1, v___x_2469_);
lean_ctor_set(v___x_2481_, 2, v___x_2480_);
v___x_2482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2463_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_Syntax_node3(v___x_2463_, v___x_2473_, v___x_2475_, v___x_2481_, v___x_2483_);
v___x_2485_ = l_Lean_Syntax_node2(v___x_2463_, v___x_2471_, v___x_2472_, v___x_2484_);
v___x_2486_ = l_Lean_Syntax_node1(v___x_2463_, v___x_2469_, v___x_2485_);
v___x_2487_ = l_Lean_Syntax_node1(v___x_2463_, v___x_2468_, v___x_2486_);
v___x_2488_ = l_Lean_Syntax_node1(v___x_2463_, v___x_2467_, v___x_2487_);
v___x_2489_ = l_Lean_Syntax_node2(v___x_2463_, v___x_2464_, v___x_2466_, v___x_2488_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2489_);
v___x_2491_ = v___x_2459_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
else
{
lean_dec_ref(v_handlers_2363_);
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2494_, lean_object* v_default_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2494_, v_default_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec_ref(v_handlers_2494_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2502_, lean_object* v___y_2503_){
_start:
{
uint8_t v___x_2505_; 
v___x_2505_ = l_Lean_Expr_hasMVar(v_e_2502_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_e_2502_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v_mctx_2508_; lean_object* v___x_2509_; lean_object* v_fst_2510_; lean_object* v_snd_2511_; lean_object* v___x_2512_; lean_object* v_cache_2513_; lean_object* v_zetaDeltaFVarIds_2514_; lean_object* v_postponed_2515_; lean_object* v_diag_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2525_; 
v___x_2507_ = lean_st_ref_get(v___y_2503_);
v_mctx_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc_ref(v_mctx_2508_);
lean_dec(v___x_2507_);
v___x_2509_ = l_Lean_instantiateMVarsCore(v_mctx_2508_, v_e_2502_);
v_fst_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_fst_2510_);
v_snd_2511_ = lean_ctor_get(v___x_2509_, 1);
lean_inc(v_snd_2511_);
lean_dec_ref(v___x_2509_);
v___x_2512_ = lean_st_ref_take(v___y_2503_);
v_cache_2513_ = lean_ctor_get(v___x_2512_, 1);
v_zetaDeltaFVarIds_2514_ = lean_ctor_get(v___x_2512_, 2);
v_postponed_2515_ = lean_ctor_get(v___x_2512_, 3);
v_diag_2516_ = lean_ctor_get(v___x_2512_, 4);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v___x_2512_, 0);
lean_dec(v_unused_2526_);
v___x_2518_ = v___x_2512_;
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_diag_2516_);
lean_inc(v_postponed_2515_);
lean_inc(v_zetaDeltaFVarIds_2514_);
lean_inc(v_cache_2513_);
lean_dec(v___x_2512_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v_snd_2511_);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_snd_2511_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_cache_2513_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_zetaDeltaFVarIds_2514_);
lean_ctor_set(v_reuseFailAlloc_2524_, 3, v_postponed_2515_);
lean_ctor_set(v_reuseFailAlloc_2524_, 4, v_diag_2516_);
v___x_2521_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_st_ref_put(v___y_2503_, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v_fst_2510_);
return v___x_2523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2527_, v___y_2528_);
lean_dec(v___y_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2531_, v___y_2537_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; 
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
v___x_2563_ = lean_apply_9(v_x_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, lean_box(0));
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2575_, lean_object* v_x_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___f_2586_; lean_object* v___x_2587_; 
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
v___f_2586_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2586_, 0, v_x_2576_);
lean_closure_set(v___f_2586_, 1, v___y_2577_);
lean_closure_set(v___f_2586_, 2, v___y_2578_);
lean_closure_set(v___f_2586_, 3, v___y_2579_);
lean_closure_set(v___f_2586_, 4, v___y_2580_);
v___x_2587_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2575_, v___f_2586_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2587_) == 0)
{
return v___x_2587_;
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2596_, lean_object* v_x_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2596_, v_x_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2608_, lean_object* v_mvarId_2609_, lean_object* v_x_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2609_, v_x_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2621_, lean_object* v_mvarId_2622_, lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2621_, v_mvarId_2622_, v_x_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2634_, lean_object* v_inv_2635_, lean_object* v_xs_2636_, uint8_t v___x_2637_, lean_object* v___x_2638_, lean_object* v_letMuts_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; 
lean_inc_ref(v_letMuts_2639_);
lean_inc_ref(v_xs_2636_);
v___x_2649_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2634_, v_inv_2635_, v_xs_2636_, v_letMuts_2639_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2726_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2726_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2726_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
if (lean_obj_tag(v_a_2650_) == 1)
{
lean_object* v_val_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2721_; 
lean_del_object(v___x_2652_);
v_val_2654_ = lean_ctor_get(v_a_2650_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_a_2650_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2656_ = v_a_2650_;
v_isShared_2657_ = v_isSharedCheck_2721_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_val_2654_);
lean_dec(v_a_2650_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2721_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_snd_2658_; lean_object* v_fst_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2720_; 
v_snd_2658_ = lean_ctor_get(v_val_2654_, 1);
v_fst_2659_ = lean_ctor_get(v_val_2654_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_val_2654_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2661_ = v_val_2654_;
v_isShared_2662_ = v_isSharedCheck_2720_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2659_);
lean_dec(v_val_2654_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2720_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_fst_2663_; lean_object* v_snd_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2719_; 
v_fst_2663_ = lean_ctor_get(v_snd_2658_, 0);
v_snd_2664_ = lean_ctor_get(v_snd_2658_, 1);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_snd_2658_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2666_ = v_snd_2658_;
v_isShared_2667_ = v_isSharedCheck_2719_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_snd_2664_);
lean_inc(v_fst_2663_);
lean_dec(v_snd_2658_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2719_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_lvl_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; uint8_t v___x_2678_; lean_object* v___x_2679_; 
v_lvl_2668_ = lean_ctor_get(v_fst_2659_, 0);
lean_inc(v_lvl_2668_);
v___x_2669_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2659_);
lean_inc(v_fst_2663_);
v___x_2670_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2663_);
v___x_2671_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2668_, v___x_2669_, v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(2u);
v___x_2673_ = lean_mk_empty_array_with_capacity(v___x_2672_);
v___x_2674_ = lean_array_push(v___x_2673_, v_xs_2636_);
lean_inc_ref(v_letMuts_2639_);
v___x_2675_ = lean_array_push(v___x_2674_, v_letMuts_2639_);
v___x_2676_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2671_);
v___x_2677_ = 0;
v___x_2678_ = 1;
v___x_2679_ = l_Lean_Meta_mkLambdaFVars(v___x_2675_, v___x_2676_, v___x_2677_, v___x_2637_, v___x_2677_, v___x_2637_, v___x_2678_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec_ref(v___x_2675_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v_letMutsPred_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v_letMutsPred_2681_ = lean_ctor_get(v_fst_2663_, 2);
lean_inc_ref(v_letMutsPred_2681_);
lean_dec(v_fst_2663_);
v___x_2682_ = lean_mk_empty_array_with_capacity(v___x_2638_);
v___x_2683_ = lean_array_push(v___x_2682_, v_letMuts_2639_);
v___x_2684_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2681_);
v___x_2685_ = l_Lean_Meta_mkLambdaFVars(v___x_2683_, v___x_2684_, v___x_2677_, v___x_2637_, v___x_2677_, v___x_2637_, v___x_2678_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec_ref(v___x_2683_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2702_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2702_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2702_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v_a_2686_);
v___x_2691_ = v___x_2666_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2686_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_snd_2664_);
v___x_2691_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2691_);
lean_ctor_set(v___x_2661_, 0, v_a_2680_);
v___x_2693_ = v___x_2661_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2680_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2695_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2693_);
v___x_2695_ = v___x_2656_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2697_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2695_);
v___x_2697_ = v___x_2688_;
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
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_a_2680_);
lean_del_object(v___x_2666_);
lean_dec(v_snd_2664_);
lean_del_object(v___x_2661_);
lean_del_object(v___x_2656_);
v_a_2703_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2685_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2685_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_del_object(v___x_2666_);
lean_dec(v_snd_2664_);
lean_dec(v_fst_2663_);
lean_del_object(v___x_2661_);
lean_del_object(v___x_2656_);
lean_dec_ref(v_letMuts_2639_);
v_a_2711_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2679_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2679_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
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
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
lean_dec(v_a_2650_);
lean_dec_ref(v_letMuts_2639_);
lean_dec_ref(v_xs_2636_);
v___x_2722_ = lean_box(0);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2722_);
v___x_2724_ = v___x_2652_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref(v_letMuts_2639_);
lean_dec_ref(v_xs_2636_);
v_a_2727_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2649_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2649_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2735_, lean_object* v_inv_2736_, lean_object* v_xs_2737_, lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v_letMuts_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v___x_77125__boxed_2750_; lean_object* v_res_2751_; 
v___x_77125__boxed_2750_ = lean_unbox(v___x_2738_);
v_res_2751_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2735_, v_inv_2736_, v_xs_2737_, v___x_77125__boxed_2750_, v___x_2739_, v_letMuts_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___x_2739_);
lean_dec_ref(v_a_2735_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v_b_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2755_);
lean_inc(v___y_2754_);
lean_inc_ref(v___y_2753_);
v___x_2763_ = lean_apply_10(v_k_2752_, v_b_2757_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, lean_box(0));
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v_b_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v_b_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2776_, uint8_t v_bi_2777_, lean_object* v_type_2778_, lean_object* v_k_2779_, uint8_t v_kind_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___f_2790_; lean_object* v___x_2791_; 
lean_inc(v___y_2784_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
v___f_2790_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2790_, 0, v_k_2779_);
lean_closure_set(v___f_2790_, 1, v___y_2781_);
lean_closure_set(v___f_2790_, 2, v___y_2782_);
lean_closure_set(v___f_2790_, 3, v___y_2783_);
lean_closure_set(v___f_2790_, 4, v___y_2784_);
v___x_2791_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2776_, v_bi_2777_, v_type_2778_, v___f_2790_, v_kind_2780_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2791_) == 0)
{
return v___x_2791_;
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2800_, lean_object* v_bi_2801_, lean_object* v_type_2802_, lean_object* v_k_2803_, lean_object* v_kind_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v_bi_boxed_2814_; uint8_t v_kind_boxed_2815_; lean_object* v_res_2816_; 
v_bi_boxed_2814_ = lean_unbox(v_bi_2801_);
v_kind_boxed_2815_ = lean_unbox(v_kind_2804_);
v_res_2816_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2800_, v_bi_boxed_2814_, v_type_2802_, v_k_2803_, v_kind_boxed_2815_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2817_, lean_object* v_type_2818_, lean_object* v_k_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
uint8_t v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = 0;
v___x_2830_ = 0;
v___x_2831_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2817_, v___x_2829_, v_type_2818_, v_k_2819_, v___x_2830_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2832_, lean_object* v_type_2833_, lean_object* v_k_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2832_, v_type_2833_, v_k_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2848_, lean_object* v_inv_2849_, uint8_t v___x_2850_, lean_object* v___x_2851_, lean_object* v_arg_2852_, lean_object* v_xs_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2863_ = lean_box(v___x_2850_);
v___f_2864_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2864_, 0, v_a_2848_);
lean_closure_set(v___f_2864_, 1, v_inv_2849_);
lean_closure_set(v___f_2864_, 2, v_xs_2853_);
lean_closure_set(v___f_2864_, 3, v___x_2863_);
lean_closure_set(v___f_2864_, 4, v___x_2851_);
v___x_2865_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2866_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2865_, v_arg_2852_, v___f_2864_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2867_, lean_object* v_inv_2868_, lean_object* v___x_2869_, lean_object* v___x_2870_, lean_object* v_arg_2871_, lean_object* v_xs_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
uint8_t v___x_77445__boxed_2882_; lean_object* v_res_2883_; 
v___x_77445__boxed_2882_ = lean_unbox(v___x_2869_);
v_res_2883_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2867_, v_inv_2868_, v___x_77445__boxed_2882_, v___x_2870_, v_arg_2871_, v_xs_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
return v_res_2883_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = lean_unsigned_to_nat(32u);
v___x_2891_ = lean_mk_empty_array_with_capacity(v___x_2890_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2893_, lean_object* v_r_2894_, uint8_t v___x_2895_, lean_object* v___x_2896_, lean_object* v___x_2897_, lean_object* v_xs_2898_, lean_object* v_fst_2899_, lean_object* v_fst_2900_, lean_object* v_letMuts_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; 
lean_inc_ref(v_fst_2893_);
v___x_2911_ = l_Lean_Meta_mkNone(v_fst_2893_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_2914_ = lean_unsigned_to_nat(2u);
v___x_2915_ = lean_mk_empty_array_with_capacity(v___x_2914_);
lean_inc_ref(v___x_2915_);
v___x_2916_ = lean_array_push(v___x_2915_, v_a_2912_);
lean_inc_ref(v_letMuts_2901_);
v___x_2917_ = lean_array_push(v___x_2916_, v_letMuts_2901_);
v___x_2918_ = l_Lean_Meta_mkAppM(v___x_2913_, v___x_2917_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2920_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v___x_2920_ = l_Lean_Meta_mkSome(v_fst_2893_, v_r_2894_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
lean_inc_ref(v___x_2915_);
v___x_2922_ = lean_array_push(v___x_2915_, v_a_2921_);
v___x_2923_ = lean_array_push(v___x_2922_, v_letMuts_2901_);
v___x_2924_ = l_Lean_Meta_mkAppM(v___x_2913_, v___x_2923_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2909_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2909_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
v___x_2930_ = lean_unsigned_to_nat(100000u);
v___x_2931_ = 0;
v___x_2932_ = 0;
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2934_, 0, v___x_2930_);
lean_ctor_set(v___x_2934_, 1, v___x_2914_);
lean_ctor_set(v___x_2934_, 2, v___x_2933_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 1, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 2, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 3, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 4, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 5, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 6, v___x_2932_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 7, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 8, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 9, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 10, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 11, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 12, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 13, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 14, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 15, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 16, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 17, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 18, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 19, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 20, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 21, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 22, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 23, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 24, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 25, v___x_2895_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 26, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 27, v___x_2931_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3 + 28, v___x_2931_);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2896_);
lean_inc_ref(v___x_2935_);
v___x_2936_ = lean_array_push(v___x_2935_, v_a_2927_);
v___x_2937_ = l_Lean_Options_empty;
v___x_2938_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2934_, v___x_2936_, v_a_2929_, v___x_2937_, v___y_2906_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_2941_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2942_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2940_, v___x_2941_, v___x_2931_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; size_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc_n(v_a_2943_, 2);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2944_ = lean_array_push(v___x_2915_, v_xs_2898_);
v___x_2945_ = lean_array_push(v___x_2944_, v_a_2919_);
v___x_2946_ = l_Lean_Expr_beta(v_fst_2899_, v___x_2945_);
v___x_2947_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2897_, 2);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___x_2897_);
v___x_2949_ = lean_unsigned_to_nat(32u);
v___x_2950_ = lean_mk_empty_array_with_capacity(v___x_2949_);
v___x_2951_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2952_ = ((size_t)5ULL);
v___x_2953_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2953_, 0, v___x_2951_);
lean_ctor_set(v___x_2953_, 1, v___x_2950_);
lean_ctor_set(v___x_2953_, 2, v___x_2897_);
lean_ctor_set(v___x_2953_, 3, v___x_2897_);
lean_ctor_set_usize(v___x_2953_, 4, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2947_);
lean_ctor_set(v___x_2954_, 1, v___x_2947_);
lean_ctor_set(v___x_2954_, 2, v___x_2947_);
lean_ctor_set(v___x_2954_, 3, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2948_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
lean_inc(v_a_2939_);
v___x_2956_ = l_Lean_Meta_simp(v___x_2946_, v_a_2939_, v_a_2943_, v___x_2933_, v___x_2955_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_fst_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v_fst_2958_ = lean_ctor_get(v_a_2957_, 0);
lean_inc(v_fst_2958_);
lean_dec(v_a_2957_);
v___x_2959_ = lean_array_push(v___x_2935_, v_a_2925_);
v___x_2960_ = l_Lean_Expr_beta(v_fst_2900_, v___x_2959_);
v___x_2961_ = l_Lean_Meta_simp(v___x_2960_, v_a_2939_, v_a_2943_, v___x_2933_, v___x_2955_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec_ref_known(v___x_2955_, 2);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v_fst_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_3000_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v_fst_2963_ = lean_ctor_get(v_a_2962_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_a_2962_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v_a_2962_, 1);
lean_dec(v_unused_3001_);
v___x_2965_ = v_a_2962_;
v_isShared_2966_ = v_isSharedCheck_3000_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_fst_2963_);
lean_dec(v_a_2962_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_3000_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v_expr_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_expr_2967_ = lean_ctor_get(v_fst_2958_, 0);
lean_inc_ref(v_expr_2967_);
lean_dec(v_fst_2958_);
v___x_2968_ = lean_box(1);
v___x_2969_ = l_Lean_PrettyPrinter_delab(v_expr_2967_, v___x_2968_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v_expr_2971_; lean_object* v___x_2972_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v_expr_2971_ = lean_ctor_get(v_fst_2963_, 0);
lean_inc_ref(v_expr_2971_);
lean_dec(v_fst_2963_);
v___x_2972_ = l_Lean_PrettyPrinter_delab(v_expr_2971_, v___x_2968_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2983_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2983_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2983_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v_a_2973_);
lean_ctor_set(v___x_2965_, 0, v_a_2970_);
v___x_2978_ = v___x_2965_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2970_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2980_; 
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2978_);
v___x_2980_ = v___x_2975_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_a_2970_);
lean_del_object(v___x_2965_);
v_a_2984_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2972_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2972_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_del_object(v___x_2965_);
lean_dec(v_fst_2963_);
v_a_2992_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2969_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2969_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v_fst_2958_);
v_a_3002_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2961_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2961_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref_known(v___x_2955_, 2);
lean_dec(v_a_2943_);
lean_dec(v_a_2939_);
lean_dec_ref(v___x_2935_);
lean_dec(v_a_2925_);
lean_dec_ref(v_fst_2900_);
v_a_3010_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2956_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2956_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_a_2939_);
lean_dec_ref(v___x_2935_);
lean_dec(v_a_2925_);
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2915_);
lean_dec_ref(v_fst_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_xs_2898_);
lean_dec(v___x_2897_);
v_a_3018_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2942_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2942_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v___x_2935_);
lean_dec(v_a_2925_);
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2915_);
lean_dec_ref(v_fst_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_xs_2898_);
lean_dec(v___x_2897_);
v_a_3026_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2938_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2938_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_a_2927_);
lean_dec(v_a_2925_);
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2915_);
lean_dec_ref(v_fst_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_xs_2898_);
lean_dec(v___x_2897_);
v_a_3034_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_2928_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_2928_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2915_);
lean_dec_ref(v_fst_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_xs_2898_);
lean_dec(v___x_2897_);
v_a_3042_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_2926_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_2926_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2915_);
lean_dec_ref(v_fst_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_xs_2898_);
lean_dec(v___x_2897_);
v_a_3050_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_2924_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_2924_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2915_);
lean_dec_ref(v_letMuts_2901_);
lean_dec_ref(v_fst_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_xs_2898_);
lean_dec(v___x_2897_);
v_a_3058_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2920_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2920_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v___x_2915_);
lean_dec_ref(v_letMuts_2901_);
lean_dec_ref(v_fst_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_xs_2898_);
lean_dec(v___x_2897_);
lean_dec_ref(v_r_2894_);
lean_dec_ref(v_fst_2893_);
v_a_3066_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2918_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2918_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec_ref(v_letMuts_2901_);
lean_dec_ref(v_fst_2900_);
lean_dec_ref(v_fst_2899_);
lean_dec_ref(v_xs_2898_);
lean_dec(v___x_2897_);
lean_dec_ref(v_r_2894_);
lean_dec_ref(v_fst_2893_);
v_a_3074_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_2911_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_2911_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3082_ = _args[0];
lean_object* v_r_3083_ = _args[1];
lean_object* v___x_3084_ = _args[2];
lean_object* v___x_3085_ = _args[3];
lean_object* v___x_3086_ = _args[4];
lean_object* v_xs_3087_ = _args[5];
lean_object* v_fst_3088_ = _args[6];
lean_object* v_fst_3089_ = _args[7];
lean_object* v_letMuts_3090_ = _args[8];
lean_object* v___y_3091_ = _args[9];
lean_object* v___y_3092_ = _args[10];
lean_object* v___y_3093_ = _args[11];
lean_object* v___y_3094_ = _args[12];
lean_object* v___y_3095_ = _args[13];
lean_object* v___y_3096_ = _args[14];
lean_object* v___y_3097_ = _args[15];
lean_object* v___y_3098_ = _args[16];
lean_object* v___y_3099_ = _args[17];
_start:
{
uint8_t v___x_77518__boxed_3100_; lean_object* v_res_3101_; 
v___x_77518__boxed_3100_ = lean_unbox(v___x_3084_);
v_res_3101_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3082_, v_r_3083_, v___x_77518__boxed_3100_, v___x_3085_, v___x_3086_, v_xs_3087_, v_fst_3088_, v_fst_3089_, v_letMuts_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___x_3085_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3102_, uint8_t v___x_3103_, lean_object* v___x_3104_, lean_object* v___x_3105_, lean_object* v_xs_3106_, lean_object* v_fst_3107_, lean_object* v_fst_3108_, lean_object* v_snd_3109_, lean_object* v_r_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v___x_3120_; lean_object* v___f_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3120_ = lean_box(v___x_3103_);
v___f_3121_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3121_, 0, v_fst_3102_);
lean_closure_set(v___f_3121_, 1, v_r_3110_);
lean_closure_set(v___f_3121_, 2, v___x_3120_);
lean_closure_set(v___f_3121_, 3, v___x_3104_);
lean_closure_set(v___f_3121_, 4, v___x_3105_);
lean_closure_set(v___f_3121_, 5, v_xs_3106_);
lean_closure_set(v___f_3121_, 6, v_fst_3107_);
lean_closure_set(v___f_3121_, 7, v_fst_3108_);
v___x_3122_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3123_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3122_, v_snd_3109_, v___f_3121_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3124_ = _args[0];
lean_object* v___x_3125_ = _args[1];
lean_object* v___x_3126_ = _args[2];
lean_object* v___x_3127_ = _args[3];
lean_object* v_xs_3128_ = _args[4];
lean_object* v_fst_3129_ = _args[5];
lean_object* v_fst_3130_ = _args[6];
lean_object* v_snd_3131_ = _args[7];
lean_object* v_r_3132_ = _args[8];
lean_object* v___y_3133_ = _args[9];
lean_object* v___y_3134_ = _args[10];
lean_object* v___y_3135_ = _args[11];
lean_object* v___y_3136_ = _args[12];
lean_object* v___y_3137_ = _args[13];
lean_object* v___y_3138_ = _args[14];
lean_object* v___y_3139_ = _args[15];
lean_object* v___y_3140_ = _args[16];
lean_object* v___y_3141_ = _args[17];
_start:
{
uint8_t v___x_77914__boxed_3142_; lean_object* v_res_3143_; 
v___x_77914__boxed_3142_ = lean_unbox(v___x_3125_);
v_res_3143_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3124_, v___x_77914__boxed_3142_, v___x_3126_, v___x_3127_, v_xs_3128_, v_fst_3129_, v_fst_3130_, v_snd_3131_, v_r_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3147_, uint8_t v___x_3148_, lean_object* v___x_3149_, lean_object* v___x_3150_, lean_object* v_fst_3151_, lean_object* v_fst_3152_, lean_object* v_snd_3153_, lean_object* v_xs_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; lean_object* v___f_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3164_ = lean_box(v___x_3148_);
lean_inc_ref(v_fst_3147_);
v___f_3165_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3165_, 0, v_fst_3147_);
lean_closure_set(v___f_3165_, 1, v___x_3164_);
lean_closure_set(v___f_3165_, 2, v___x_3149_);
lean_closure_set(v___f_3165_, 3, v___x_3150_);
lean_closure_set(v___f_3165_, 4, v_xs_3154_);
lean_closure_set(v___f_3165_, 5, v_fst_3151_);
lean_closure_set(v___f_3165_, 6, v_fst_3152_);
lean_closure_set(v___f_3165_, 7, v_snd_3153_);
v___x_3166_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3167_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3166_, v_fst_3147_, v___f_3165_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3168_ = _args[0];
lean_object* v___x_3169_ = _args[1];
lean_object* v___x_3170_ = _args[2];
lean_object* v___x_3171_ = _args[3];
lean_object* v_fst_3172_ = _args[4];
lean_object* v_fst_3173_ = _args[5];
lean_object* v_snd_3174_ = _args[6];
lean_object* v_xs_3175_ = _args[7];
lean_object* v___y_3176_ = _args[8];
lean_object* v___y_3177_ = _args[9];
lean_object* v___y_3178_ = _args[10];
lean_object* v___y_3179_ = _args[11];
lean_object* v___y_3180_ = _args[12];
lean_object* v___y_3181_ = _args[13];
lean_object* v___y_3182_ = _args[14];
lean_object* v___y_3183_ = _args[15];
lean_object* v___y_3184_ = _args[16];
_start:
{
uint8_t v___x_77977__boxed_3185_; lean_object* v_res_3186_; 
v___x_77977__boxed_3185_ = lean_unbox(v___x_3169_);
v_res_3186_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3168_, v___x_77977__boxed_3185_, v___x_3170_, v___x_3171_, v_fst_3172_, v_fst_3173_, v_snd_3174_, v_xs_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3187_, size_t v_sz_3188_, size_t v_i_3189_, lean_object* v_b_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
uint8_t v___x_3196_; 
v___x_3196_ = lean_usize_dec_lt(v_i_3189_, v_sz_3188_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v_b_3190_);
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; lean_object* v_a_3199_; lean_object* v___x_3200_; 
v___x_3198_ = lean_box(1);
v_a_3199_ = lean_array_uget_borrowed(v_as_3187_, v_i_3189_);
lean_inc(v_a_3199_);
v___x_3200_ = l_Lean_PrettyPrinter_delab(v_a_3199_, v___x_3198_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3202_; size_t v___x_3203_; size_t v___x_3204_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v___x_3202_ = lean_array_push(v_b_3190_, v_a_3201_);
v___x_3203_ = ((size_t)1ULL);
v___x_3204_ = lean_usize_add(v_i_3189_, v___x_3203_);
v_i_3189_ = v___x_3204_;
v_b_3190_ = v___x_3202_;
goto _start;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v_b_3190_);
v_a_3206_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3200_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3200_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3214_, lean_object* v_sz_3215_, lean_object* v_i_3216_, lean_object* v_b_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
size_t v_sz_boxed_3223_; size_t v_i_boxed_3224_; lean_object* v_res_3225_; 
v_sz_boxed_3223_ = lean_unbox_usize(v_sz_3215_);
lean_dec(v_sz_3215_);
v_i_boxed_3224_ = lean_unbox_usize(v_i_3216_);
lean_dec(v_i_3216_);
v_res_3225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3214_, v_sz_boxed_3223_, v_i_boxed_3224_, v_b_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec_ref(v_as_3214_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3246_, lean_object* v_fst_3247_, lean_object* v_snd_3248_, lean_object* v___x_3249_, lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v___x_3256_, uint8_t v___x_3257_, lean_object* v_letMuts_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3268_ = lean_unsigned_to_nat(2u);
v___x_3269_ = lean_mk_empty_array_with_capacity(v___x_3268_);
v___x_3270_ = lean_array_push(v___x_3269_, v_xs_3246_);
v___x_3271_ = lean_array_push(v___x_3270_, v_letMuts_3258_);
v___x_3272_ = l_Lean_Expr_beta(v_fst_3247_, v___x_3271_);
v___x_3273_ = lean_box(1);
v___x_3274_ = l_Lean_PrettyPrinter_delab(v___x_3272_, v___x_3273_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3414_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3414_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3414_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
uint8_t v___y_3280_; lean_object* v_points_3317_; lean_object* v_default_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3413_; 
v_points_3317_ = lean_ctor_get(v_snd_3248_, 0);
v_default_3318_ = lean_ctor_get(v_snd_3248_, 1);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_snd_3248_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3320_ = v_snd_3248_;
v_isShared_3321_ = v_isSharedCheck_3413_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_default_3318_);
lean_inc(v_points_3317_);
lean_dec(v_snd_3248_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3413_;
goto v_resetjp_3319_;
}
v___jp_3279_:
{
lean_object* v_toCold_3281_; lean_object* v_ref_3282_; lean_object* v_quotContext_3283_; lean_object* v_currMacroScope_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v_toCold_3281_ = lean_ctor_get(v___y_3265_, 0);
v_ref_3282_ = lean_ctor_get(v___y_3265_, 2);
v_quotContext_3283_ = lean_ctor_get(v_toCold_3281_, 8);
v_currMacroScope_3284_ = lean_ctor_get(v_toCold_3281_, 9);
v___x_3285_ = l_Lean_SourceInfo_fromRef(v_ref_3282_, v___y_3280_);
v___x_3286_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3287_ = l_Lean_Name_mkStr3(v___x_3255_, v___x_3256_, v___x_3286_);
v___x_3288_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3289_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3285_, 11);
v___x_3290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3285_);
lean_ctor_set(v___x_3290_, 1, v___x_3288_);
lean_ctor_set(v___x_3290_, 2, v___x_3289_);
v___x_3291_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3285_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3285_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = l_String_toRawSubstring_x27(v___x_3249_);
lean_inc_n(v_currMacroScope_3284_, 2);
lean_inc_n(v_quotContext_3283_, 2);
v___x_3298_ = l_Lean_addMacroScope(v_quotContext_3283_, v___x_3250_, v_currMacroScope_3284_);
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3285_);
lean_ctor_set(v___x_3300_, 1, v___x_3297_);
lean_ctor_set(v___x_3300_, 2, v___x_3298_);
lean_ctor_set(v___x_3300_, 3, v___x_3299_);
v___x_3301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3285_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l_String_toRawSubstring_x27(v___x_3251_);
v___x_3304_ = l_Lean_addMacroScope(v_quotContext_3283_, v___x_3252_, v_currMacroScope_3284_);
v___x_3305_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3285_);
lean_ctor_set(v___x_3305_, 1, v___x_3303_);
lean_ctor_set(v___x_3305_, 2, v___x_3304_);
lean_ctor_set(v___x_3305_, 3, v___x_3299_);
v___x_3306_ = l_Lean_Syntax_node3(v___x_3285_, v___x_3293_, v___x_3300_, v___x_3302_, v___x_3305_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3285_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_Lean_Syntax_node3(v___x_3285_, v___x_3294_, v___x_3296_, v___x_3306_, v___x_3308_);
v___x_3310_ = l_Lean_Syntax_node1(v___x_3285_, v___x_3293_, v___x_3309_);
v___x_3311_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3285_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = l_Lean_Syntax_node5(v___x_3285_, v___x_3287_, v___x_3290_, v___x_3292_, v___x_3310_, v___x_3312_, v_a_3275_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3313_);
v___x_3315_ = v___x_3277_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
v_resetjp_3319_:
{
uint8_t v___y_3323_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3374_ = lean_array_get_size(v_points_3317_);
v___x_3375_ = lean_nat_dec_eq(v___x_3374_, v___x_3254_);
if (v___x_3375_ == 0)
{
lean_del_object(v___x_3277_);
lean_dec_ref(v___x_3256_);
lean_dec_ref(v___x_3255_);
v___y_3323_ = v___x_3375_;
goto v___jp_3322_;
}
else
{
if (lean_obj_tag(v_default_3318_) == 3)
{
uint8_t v___x_3376_; 
lean_del_object(v___x_3277_);
lean_dec_ref(v___x_3256_);
lean_dec_ref(v___x_3255_);
v___x_3376_ = 0;
v___y_3323_ = v___x_3376_;
goto v___jp_3322_;
}
else
{
lean_del_object(v___x_3320_);
lean_dec_ref(v_points_3317_);
if (lean_obj_tag(v_default_3318_) == 2)
{
if (v___x_3257_ == 0)
{
v___y_3280_ = v___x_3257_;
goto v___jp_3279_;
}
else
{
lean_object* v_toCold_3377_; lean_object* v_ref_3378_; lean_object* v_quotContext_3379_; lean_object* v_currMacroScope_3380_; uint8_t v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_del_object(v___x_3277_);
v_toCold_3377_ = lean_ctor_get(v___y_3265_, 0);
v_ref_3378_ = lean_ctor_get(v___y_3265_, 2);
v_quotContext_3379_ = lean_ctor_get(v_toCold_3377_, 8);
v_currMacroScope_3380_ = lean_ctor_get(v_toCold_3377_, 9);
v___x_3381_ = 0;
v___x_3382_ = l_Lean_SourceInfo_fromRef(v_ref_3378_, v___x_3381_);
v___x_3383_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3384_ = l_Lean_Name_mkStr3(v___x_3255_, v___x_3256_, v___x_3383_);
v___x_3385_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3386_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3382_, 11);
v___x_3387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3382_);
lean_ctor_set(v___x_3387_, 1, v___x_3385_);
lean_ctor_set(v___x_3387_, 2, v___x_3386_);
v___x_3388_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3382_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3382_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = l_String_toRawSubstring_x27(v___x_3249_);
lean_inc_n(v_currMacroScope_3380_, 2);
lean_inc_n(v_quotContext_3379_, 2);
v___x_3395_ = l_Lean_addMacroScope(v_quotContext_3379_, v___x_3250_, v_currMacroScope_3380_);
v___x_3396_ = lean_box(0);
v___x_3397_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3382_);
lean_ctor_set(v___x_3397_, 1, v___x_3394_);
lean_ctor_set(v___x_3397_, 2, v___x_3395_);
lean_ctor_set(v___x_3397_, 3, v___x_3396_);
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3382_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = l_String_toRawSubstring_x27(v___x_3251_);
v___x_3401_ = l_Lean_addMacroScope(v_quotContext_3379_, v___x_3252_, v_currMacroScope_3380_);
v___x_3402_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3382_);
lean_ctor_set(v___x_3402_, 1, v___x_3400_);
lean_ctor_set(v___x_3402_, 2, v___x_3401_);
lean_ctor_set(v___x_3402_, 3, v___x_3396_);
v___x_3403_ = l_Lean_Syntax_node3(v___x_3382_, v___x_3390_, v___x_3397_, v___x_3399_, v___x_3402_);
v___x_3404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3382_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = l_Lean_Syntax_node3(v___x_3382_, v___x_3391_, v___x_3393_, v___x_3403_, v___x_3405_);
v___x_3407_ = l_Lean_Syntax_node1(v___x_3382_, v___x_3390_, v___x_3406_);
v___x_3408_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3382_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = l_Lean_Syntax_node5(v___x_3382_, v___x_3384_, v___x_3387_, v___x_3389_, v___x_3407_, v___x_3409_, v_a_3275_);
v___x_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
return v___x_3411_;
}
}
else
{
uint8_t v___x_3412_; 
lean_dec(v_default_3318_);
v___x_3412_ = 0;
v___y_3280_ = v___x_3412_;
goto v___jp_3279_;
}
}
}
v___jp_3322_:
{
lean_object* v_toCold_3324_; lean_object* v_ref_3325_; lean_object* v_quotContext_3326_; lean_object* v_currMacroScope_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
v_toCold_3324_ = lean_ctor_get(v___y_3265_, 0);
v_ref_3325_ = lean_ctor_get(v___y_3265_, 2);
v_quotContext_3326_ = lean_ctor_get(v_toCold_3324_, 8);
v_currMacroScope_3327_ = lean_ctor_get(v_toCold_3324_, 9);
v___x_3328_ = l_Lean_SourceInfo_fromRef(v_ref_3325_, v___y_3323_);
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3330_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3328_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set_tag(v___x_3320_, 2);
lean_ctor_set(v___x_3320_, 1, v___x_3329_);
lean_ctor_set(v___x_3320_, 0, v___x_3328_);
v___x_3332_ = v___x_3320_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v___x_3329_);
v___x_3332_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; size_t v_sz_3360_; size_t v___x_3361_; lean_object* v___x_3362_; 
v___x_3333_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3328_, 11);
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3328_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = l_String_toRawSubstring_x27(v___x_3249_);
lean_inc_n(v_currMacroScope_3327_, 2);
lean_inc_n(v_quotContext_3326_, 2);
v___x_3339_ = l_Lean_addMacroScope(v_quotContext_3326_, v___x_3250_, v_currMacroScope_3327_);
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3328_);
lean_ctor_set(v___x_3341_, 1, v___x_3338_);
lean_ctor_set(v___x_3341_, 2, v___x_3339_);
lean_ctor_set(v___x_3341_, 3, v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3328_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = l_String_toRawSubstring_x27(v___x_3251_);
v___x_3345_ = l_Lean_addMacroScope(v_quotContext_3326_, v___x_3252_, v_currMacroScope_3327_);
v___x_3346_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3328_);
lean_ctor_set(v___x_3346_, 1, v___x_3344_);
lean_ctor_set(v___x_3346_, 2, v___x_3345_);
lean_ctor_set(v___x_3346_, 3, v___x_3340_);
v___x_3347_ = l_Lean_Syntax_node3(v___x_3328_, v___x_3334_, v___x_3341_, v___x_3343_, v___x_3346_);
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3328_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = l_Lean_Syntax_node3(v___x_3328_, v___x_3335_, v___x_3337_, v___x_3347_, v___x_3349_);
v___x_3351_ = l_Lean_Syntax_node1(v___x_3328_, v___x_3334_, v___x_3350_);
v___x_3352_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3328_);
lean_ctor_set(v___x_3353_, 1, v___x_3334_);
lean_ctor_set(v___x_3353_, 2, v___x_3352_);
v___x_3354_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3328_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l_Lean_Syntax_node4(v___x_3328_, v___x_3333_, v___x_3351_, v___x_3353_, v___x_3355_, v_a_3275_);
v___x_3357_ = l_Lean_Syntax_node2(v___x_3328_, v___x_3330_, v___x_3332_, v___x_3356_);
v___x_3358_ = lean_mk_empty_array_with_capacity(v___x_3253_);
v___x_3359_ = lean_array_push(v___x_3358_, v___x_3357_);
v_sz_3360_ = lean_array_size(v_points_3317_);
v___x_3361_ = ((size_t)0ULL);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3317_, v_sz_3360_, v___x_3361_, v___x_3359_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec_ref(v_points_3317_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3363_, v_default_3318_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v_a_3363_);
return v___x_3364_;
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_default_3318_);
v_a_3365_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3362_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3362_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
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
lean_dec_ref(v___x_3256_);
lean_dec_ref(v___x_3255_);
lean_dec(v___x_3252_);
lean_dec_ref(v___x_3251_);
lean_dec(v___x_3250_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v_snd_3248_);
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3415_ = _args[0];
lean_object* v_fst_3416_ = _args[1];
lean_object* v_snd_3417_ = _args[2];
lean_object* v___x_3418_ = _args[3];
lean_object* v___x_3419_ = _args[4];
lean_object* v___x_3420_ = _args[5];
lean_object* v___x_3421_ = _args[6];
lean_object* v___x_3422_ = _args[7];
lean_object* v___x_3423_ = _args[8];
lean_object* v___x_3424_ = _args[9];
lean_object* v___x_3425_ = _args[10];
lean_object* v___x_3426_ = _args[11];
lean_object* v_letMuts_3427_ = _args[12];
lean_object* v___y_3428_ = _args[13];
lean_object* v___y_3429_ = _args[14];
lean_object* v___y_3430_ = _args[15];
lean_object* v___y_3431_ = _args[16];
lean_object* v___y_3432_ = _args[17];
lean_object* v___y_3433_ = _args[18];
lean_object* v___y_3434_ = _args[19];
lean_object* v___y_3435_ = _args[20];
lean_object* v___y_3436_ = _args[21];
_start:
{
uint8_t v___x_78187__boxed_3437_; lean_object* v_res_3438_; 
v___x_78187__boxed_3437_ = lean_unbox(v___x_3426_);
v_res_3438_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3415_, v_fst_3416_, v_snd_3417_, v___x_3418_, v___x_3419_, v___x_3420_, v___x_3421_, v___x_3422_, v___x_3423_, v___x_3424_, v___x_3425_, v___x_78187__boxed_3437_, v_letMuts_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___x_3423_);
lean_dec(v___x_3422_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3439_, lean_object* v_snd_3440_, lean_object* v___x_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v___x_3444_, lean_object* v___x_3445_, lean_object* v___x_3446_, uint8_t v___x_3447_, lean_object* v_arg_3448_, lean_object* v_xs_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; 
v___x_3459_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3460_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3461_ = lean_box(v___x_3447_);
v___f_3462_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3462_, 0, v_xs_3449_);
lean_closure_set(v___f_3462_, 1, v_fst_3439_);
lean_closure_set(v___f_3462_, 2, v_snd_3440_);
lean_closure_set(v___f_3462_, 3, v___x_3441_);
lean_closure_set(v___f_3462_, 4, v___x_3442_);
lean_closure_set(v___f_3462_, 5, v___x_3459_);
lean_closure_set(v___f_3462_, 6, v___x_3460_);
lean_closure_set(v___f_3462_, 7, v___x_3443_);
lean_closure_set(v___f_3462_, 8, v___x_3444_);
lean_closure_set(v___f_3462_, 9, v___x_3445_);
lean_closure_set(v___f_3462_, 10, v___x_3446_);
lean_closure_set(v___f_3462_, 11, v___x_3461_);
v___x_3463_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3460_, v_arg_3448_, v___f_3462_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3464_ = _args[0];
lean_object* v_snd_3465_ = _args[1];
lean_object* v___x_3466_ = _args[2];
lean_object* v___x_3467_ = _args[3];
lean_object* v___x_3468_ = _args[4];
lean_object* v___x_3469_ = _args[5];
lean_object* v___x_3470_ = _args[6];
lean_object* v___x_3471_ = _args[7];
lean_object* v___x_3472_ = _args[8];
lean_object* v_arg_3473_ = _args[9];
lean_object* v_xs_3474_ = _args[10];
lean_object* v___y_3475_ = _args[11];
lean_object* v___y_3476_ = _args[12];
lean_object* v___y_3477_ = _args[13];
lean_object* v___y_3478_ = _args[14];
lean_object* v___y_3479_ = _args[15];
lean_object* v___y_3480_ = _args[16];
lean_object* v___y_3481_ = _args[17];
lean_object* v___y_3482_ = _args[18];
lean_object* v___y_3483_ = _args[19];
_start:
{
uint8_t v___x_78534__boxed_3484_; lean_object* v_res_3485_; 
v___x_78534__boxed_3484_ = lean_unbox(v___x_3472_);
v_res_3485_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3464_, v_snd_3465_, v___x_3466_, v___x_3467_, v___x_3468_, v___x_3469_, v___x_3470_, v___x_3471_, v___x_78534__boxed_3484_, v_arg_3473_, v_xs_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3486_, size_t v_sz_3487_, size_t v_i_3488_, lean_object* v_b_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
uint8_t v___x_3495_; 
v___x_3495_ = lean_usize_dec_lt(v_i_3488_, v_sz_3487_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3496_, 0, v_b_3489_);
return v___x_3496_;
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_a_3497_ = lean_array_uget_borrowed(v_as_3486_, v_i_3488_);
v___x_3498_ = lean_box(1);
lean_inc(v_a_3497_);
v___x_3499_ = l_Lean_PrettyPrinter_delab(v_a_3497_, v___x_3498_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; size_t v___x_3502_; size_t v___x_3503_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___x_3501_ = lean_array_push(v_b_3489_, v_a_3500_);
v___x_3502_ = ((size_t)1ULL);
v___x_3503_ = lean_usize_add(v_i_3488_, v___x_3502_);
v_i_3488_ = v___x_3503_;
v_b_3489_ = v___x_3501_;
goto _start;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v_b_3489_);
v_a_3505_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3499_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3499_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3513_, lean_object* v_sz_3514_, lean_object* v_i_3515_, lean_object* v_b_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
size_t v_sz_boxed_3522_; size_t v_i_boxed_3523_; lean_object* v_res_3524_; 
v_sz_boxed_3522_ = lean_unbox_usize(v_sz_3514_);
lean_dec(v_sz_3514_);
v_i_boxed_3523_ = lean_unbox_usize(v_i_3515_);
lean_dec(v_i_3515_);
v_res_3524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3513_, v_sz_boxed_3522_, v_i_boxed_3523_, v_b_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v_as_3513_);
return v_res_3524_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3533_ = l_String_toRawSubstring_x27(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3544_ = l_String_toRawSubstring_x27(v___x_3543_);
return v___x_3544_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3549_ = l_String_toRawSubstring_x27(v___x_3548_);
return v___x_3549_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3551_ = l_String_toRawSubstring_x27(v___x_3550_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3555_ = l_String_toRawSubstring_x27(v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3560_ = l_String_toRawSubstring_x27(v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3570_, lean_object* v___x_3571_, lean_object* v___f_3572_, lean_object* v_a_3573_, lean_object* v_inv_3574_, lean_object* v_arg_3575_, uint8_t v___x_3576_, lean_object* v___x_3577_, lean_object* v___x_3578_, lean_object* v___x_3579_, lean_object* v___x_3580_, lean_object* v___x_3581_, lean_object* v___x_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v_a_3593_; lean_object* v___y_3597_; lean_object* v___x_3599_; 
lean_inc_ref(v___x_3571_);
lean_inc(v___x_3570_);
v___x_3599_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3570_, v___x_3571_, v___f_3572_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3573_, v_inv_3574_, v_arg_3575_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
if (lean_obj_tag(v_a_3602_) == 1)
{
lean_object* v_val_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_4088_; 
lean_dec_ref(v_arg_3575_);
v_val_3603_ = lean_ctor_get(v_a_3602_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_a_3602_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_3605_ = v_a_3602_;
v_isShared_3606_ = v_isSharedCheck_4088_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_val_3603_);
lean_dec(v_a_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_4088_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
if (lean_obj_tag(v_a_3600_) == 1)
{
lean_object* v_val_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_4010_; 
lean_del_object(v___x_3605_);
v_val_3607_ = lean_ctor_get(v_a_3600_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_a_3600_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3609_ = v_a_3600_;
v_isShared_3610_ = v_isSharedCheck_4010_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_val_3607_);
lean_dec(v_a_3600_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_4010_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v_snd_3611_; lean_object* v_fst_3612_; lean_object* v_snd_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_4009_; 
v_snd_3611_ = lean_ctor_get(v_val_3607_, 1);
lean_inc(v_snd_3611_);
v_fst_3612_ = lean_ctor_get(v_val_3603_, 0);
v_snd_3613_ = lean_ctor_get(v_val_3603_, 1);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_val_3603_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3615_ = v_val_3603_;
v_isShared_3616_ = v_isSharedCheck_4009_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_snd_3613_);
lean_inc(v_fst_3612_);
lean_dec(v_val_3603_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_4009_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v_fst_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_4007_; 
v_fst_3617_ = lean_ctor_get(v_val_3607_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_val_3607_);
if (v_isSharedCheck_4007_ == 0)
{
lean_object* v_unused_4008_; 
v_unused_4008_ = lean_ctor_get(v_val_3607_, 1);
lean_dec(v_unused_4008_);
v___x_3619_ = v_val_3607_;
v_isShared_3620_ = v_isSharedCheck_4007_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_fst_3617_);
lean_dec(v_val_3607_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_4007_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v_fst_3621_; lean_object* v_snd_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_4006_; 
v_fst_3621_ = lean_ctor_get(v_snd_3611_, 0);
v_snd_3622_ = lean_ctor_get(v_snd_3611_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_snd_3611_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3624_ = v_snd_3611_;
v_isShared_3625_ = v_isSharedCheck_4006_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_snd_3622_);
lean_inc(v_fst_3621_);
lean_dec(v_snd_3611_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_4006_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___f_3627_; lean_object* v___x_3628_; 
v___x_3626_ = lean_box(v___x_3576_);
lean_inc(v___x_3578_);
v___f_3627_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3627_, 0, v_fst_3612_);
lean_closure_set(v___f_3627_, 1, v___x_3626_);
lean_closure_set(v___f_3627_, 2, v___x_3577_);
lean_closure_set(v___f_3627_, 3, v___x_3578_);
lean_closure_set(v___f_3627_, 4, v_fst_3617_);
lean_closure_set(v___f_3627_, 5, v_fst_3621_);
lean_closure_set(v___f_3627_, 6, v_snd_3613_);
lean_inc(v___x_3570_);
v___x_3628_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3570_, v___x_3571_, v___f_3627_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v_fst_3630_; lean_object* v_snd_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3997_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
v_fst_3630_ = lean_ctor_get(v_a_3629_, 0);
v_snd_3631_ = lean_ctor_get(v_a_3629_, 1);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_a_3629_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3633_ = v_a_3629_;
v_isShared_3634_ = v_isSharedCheck_3997_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_snd_3631_);
lean_inc(v_fst_3630_);
lean_dec(v_a_3629_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3997_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_points_3635_; lean_object* v_default_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3996_; 
v_points_3635_ = lean_ctor_get(v_snd_3622_, 0);
v_default_3636_ = lean_ctor_get(v_snd_3622_, 1);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_snd_3622_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3638_ = v_snd_3622_;
v_isShared_3639_ = v_isSharedCheck_3996_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_default_3636_);
lean_inc(v_points_3635_);
lean_dec(v_snd_3622_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3996_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3640_ = lean_array_get_size(v_points_3635_);
v___x_3641_ = lean_nat_dec_eq(v___x_3640_, v___x_3578_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; size_t v_sz_3643_; size_t v___x_3644_; lean_object* v___x_3645_; 
lean_del_object(v___x_3609_);
v___x_3642_ = lean_mk_empty_array_with_capacity(v___x_3578_);
lean_dec(v___x_3578_);
v_sz_3643_ = lean_array_size(v_points_3635_);
v___x_3644_ = ((size_t)0ULL);
v___x_3645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3635_, v_sz_3643_, v___x_3644_, v___x_3642_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec_ref(v_points_3635_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3647_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3645_, 1);
v___x_3647_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3646_, v_default_3636_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v_a_3646_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_toCold_3648_; lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3731_; 
v_toCold_3648_ = lean_ctor_get(v___y_3589_, 0);
lean_inc_ref(v_toCold_3648_);
v_a_3649_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3651_ = v___x_3647_;
v_isShared_3652_ = v_isSharedCheck_3731_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3647_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3731_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_ref_3653_; lean_object* v_quotContext_3654_; lean_object* v_currMacroScope_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
v_ref_3653_ = lean_ctor_get(v___y_3589_, 2);
lean_inc(v_ref_3653_);
lean_dec_ref(v___y_3589_);
v_quotContext_3654_ = lean_ctor_get(v_toCold_3648_, 8);
lean_inc_n(v_quotContext_3654_, 2);
v_currMacroScope_3655_ = lean_ctor_get(v_toCold_3648_, 9);
lean_inc_n(v_currMacroScope_3655_, 2);
lean_dec_ref(v_toCold_3648_);
v___x_3656_ = l_Lean_SourceInfo_fromRef(v_ref_3653_, v___x_3641_);
lean_dec(v_ref_3653_);
v___x_3657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3658_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3659_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3579_);
v___x_3660_ = l_Lean_Name_mkStr2(v___x_3579_, v___x_3659_);
v___x_3661_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3660_, v_currMacroScope_3655_);
v___x_3662_ = l_Lean_Name_mkStr4(v___x_3580_, v___x_3581_, v___x_3579_, v___x_3659_);
v___x_3663_ = lean_box(0);
lean_inc(v___x_3662_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 1);
lean_ctor_set(v___x_3638_, 1, v___x_3663_);
lean_ctor_set(v___x_3638_, 0, v___x_3662_);
v___x_3665_ = v___x_3638_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3667_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3662_);
v___x_3667_ = v___x_3651_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3662_);
v___x_3667_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3669_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 1);
lean_ctor_set(v___x_3633_, 1, v___x_3663_);
lean_ctor_set(v___x_3633_, 0, v___x_3667_);
v___x_3669_ = v___x_3633_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v___x_3663_);
v___x_3669_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set_tag(v___x_3624_, 1);
lean_ctor_set(v___x_3624_, 1, v___x_3669_);
lean_ctor_set(v___x_3624_, 0, v___x_3665_);
v___x_3671_ = v___x_3624_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
lean_inc_n(v___x_3656_, 2);
v___x_3672_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3656_);
lean_ctor_set(v___x_3672_, 1, v___x_3658_);
lean_ctor_set(v___x_3672_, 2, v___x_3661_);
lean_ctor_set(v___x_3672_, 3, v___x_3671_);
v___x_3673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3675_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 2);
lean_ctor_set(v___x_3619_, 1, v___x_3675_);
lean_ctor_set(v___x_3619_, 0, v___x_3656_);
v___x_3677_ = v___x_3619_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3678_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3679_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3655_);
lean_inc(v_quotContext_3654_);
v___x_3680_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3679_, v_currMacroScope_3655_);
lean_inc_n(v___x_3656_, 2);
v___x_3681_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3656_);
lean_ctor_set(v___x_3681_, 1, v___x_3678_);
lean_ctor_set(v___x_3681_, 2, v___x_3680_);
lean_ctor_set(v___x_3681_, 3, v___x_3663_);
v___x_3682_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 2);
lean_ctor_set(v___x_3615_, 1, v___x_3682_);
lean_ctor_set(v___x_3615_, 0, v___x_3656_);
v___x_3684_ = v___x_3615_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3685_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3686_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3656_, 19);
v___x_3687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3656_);
lean_ctor_set(v___x_3687_, 1, v___x_3685_);
v___x_3688_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3689_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3690_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3655_, 4);
lean_inc_n(v_quotContext_3654_, 4);
v___x_3691_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3690_, v_currMacroScope_3655_);
v___x_3692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3656_);
lean_ctor_set(v___x_3692_, 1, v___x_3689_);
lean_ctor_set(v___x_3692_, 2, v___x_3691_);
lean_ctor_set(v___x_3692_, 3, v___x_3663_);
v___x_3693_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3694_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3695_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3694_, v_currMacroScope_3655_);
v___x_3696_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3656_);
lean_ctor_set(v___x_3696_, 1, v___x_3693_);
lean_ctor_set(v___x_3696_, 2, v___x_3695_);
lean_ctor_set(v___x_3696_, 3, v___x_3663_);
lean_inc_ref(v___x_3696_);
v___x_3697_ = l_Lean_Syntax_node2(v___x_3656_, v___x_3673_, v___x_3692_, v___x_3696_);
v___x_3698_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3656_);
lean_ctor_set(v___x_3699_, 1, v___x_3673_);
lean_ctor_set(v___x_3699_, 2, v___x_3698_);
v___x_3700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3656_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
lean_inc_ref(v___x_3701_);
lean_inc_ref(v___x_3699_);
v___x_3702_ = l_Lean_Syntax_node4(v___x_3656_, v___x_3688_, v___x_3697_, v___x_3699_, v___x_3701_, v_snd_3631_);
lean_inc_ref(v___x_3687_);
v___x_3703_ = l_Lean_Syntax_node2(v___x_3656_, v___x_3686_, v___x_3687_, v___x_3702_);
v___x_3704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3656_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
lean_inc_ref_n(v___x_3705_, 2);
lean_inc_ref_n(v___x_3684_, 2);
lean_inc_ref_n(v___x_3677_, 2);
v___x_3706_ = l_Lean_Syntax_node5(v___x_3656_, v___x_3674_, v___x_3677_, v___x_3681_, v___x_3684_, v___x_3703_, v___x_3705_);
v___x_3707_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3708_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3709_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3708_, v_currMacroScope_3655_);
v___x_3710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3656_);
lean_ctor_set(v___x_3710_, 1, v___x_3707_);
lean_ctor_set(v___x_3710_, 2, v___x_3709_);
lean_ctor_set(v___x_3710_, 3, v___x_3663_);
v___x_3711_ = l_String_toRawSubstring_x27(v___x_3582_);
v___x_3712_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3570_, v_currMacroScope_3655_);
v___x_3713_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3656_);
lean_ctor_set(v___x_3713_, 1, v___x_3711_);
lean_ctor_set(v___x_3713_, 2, v___x_3712_);
lean_ctor_set(v___x_3713_, 3, v___x_3663_);
v___x_3714_ = l_Lean_Syntax_node2(v___x_3656_, v___x_3673_, v___x_3713_, v___x_3696_);
v___x_3715_ = l_Lean_Syntax_node4(v___x_3656_, v___x_3688_, v___x_3714_, v___x_3699_, v___x_3701_, v_fst_3630_);
v___x_3716_ = l_Lean_Syntax_node2(v___x_3656_, v___x_3686_, v___x_3687_, v___x_3715_);
v___x_3717_ = l_Lean_Syntax_node5(v___x_3656_, v___x_3674_, v___x_3677_, v___x_3710_, v___x_3684_, v___x_3716_, v___x_3705_);
v___x_3718_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3720_ = l_Lean_addMacroScope(v_quotContext_3654_, v___x_3719_, v_currMacroScope_3655_);
v___x_3721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3656_);
lean_ctor_set(v___x_3721_, 1, v___x_3718_);
lean_ctor_set(v___x_3721_, 2, v___x_3720_);
lean_ctor_set(v___x_3721_, 3, v___x_3663_);
v___x_3722_ = l_Lean_Syntax_node5(v___x_3656_, v___x_3674_, v___x_3677_, v___x_3721_, v___x_3684_, v_a_3649_, v___x_3705_);
v___x_3723_ = l_Lean_Syntax_node3(v___x_3656_, v___x_3673_, v___x_3706_, v___x_3717_, v___x_3722_);
v___x_3724_ = l_Lean_Syntax_node2(v___x_3656_, v___x_3657_, v___x_3672_, v___x_3723_);
v_a_3593_ = v___x_3724_;
goto v___jp_3592_;
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
lean_del_object(v___x_3638_);
lean_del_object(v___x_3633_);
lean_dec(v_snd_3631_);
lean_dec(v_fst_3630_);
lean_del_object(v___x_3624_);
lean_del_object(v___x_3619_);
lean_del_object(v___x_3615_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec(v___x_3570_);
v___y_3597_ = v___x_3647_;
goto v___jp_3596_;
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_del_object(v___x_3638_);
lean_dec(v_default_3636_);
lean_del_object(v___x_3633_);
lean_dec(v_snd_3631_);
lean_dec(v_fst_3630_);
lean_del_object(v___x_3624_);
lean_del_object(v___x_3619_);
lean_del_object(v___x_3615_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec(v___x_3570_);
v_a_3732_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3645_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3645_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_dec_ref(v_points_3635_);
lean_dec(v___x_3578_);
switch(lean_obj_tag(v_default_3636_))
{
case 2:
{
lean_object* v_toCold_3740_; lean_object* v_ref_3741_; lean_object* v_quotContext_3742_; lean_object* v_currMacroScope_3743_; uint8_t v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v_toCold_3740_ = lean_ctor_get(v___y_3589_, 0);
lean_inc_ref(v_toCold_3740_);
v_ref_3741_ = lean_ctor_get(v___y_3589_, 2);
lean_inc(v_ref_3741_);
lean_dec_ref(v___y_3589_);
v_quotContext_3742_ = lean_ctor_get(v_toCold_3740_, 8);
lean_inc_n(v_quotContext_3742_, 2);
v_currMacroScope_3743_ = lean_ctor_get(v_toCold_3740_, 9);
lean_inc_n(v_currMacroScope_3743_, 2);
lean_dec_ref(v_toCold_3740_);
v___x_3744_ = 0;
v___x_3745_ = l_Lean_SourceInfo_fromRef(v_ref_3741_, v___x_3744_);
lean_dec(v_ref_3741_);
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3747_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3748_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3579_);
v___x_3749_ = l_Lean_Name_mkStr2(v___x_3579_, v___x_3748_);
v___x_3750_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3749_, v_currMacroScope_3743_);
lean_inc_ref(v___x_3581_);
lean_inc_ref(v___x_3580_);
v___x_3751_ = l_Lean_Name_mkStr4(v___x_3580_, v___x_3581_, v___x_3579_, v___x_3748_);
v___x_3752_ = lean_box(0);
lean_inc(v___x_3751_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 1);
lean_ctor_set(v___x_3638_, 1, v___x_3752_);
lean_ctor_set(v___x_3638_, 0, v___x_3751_);
v___x_3754_ = v___x_3638_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3756_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3751_);
v___x_3756_ = v___x_3609_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3751_);
v___x_3756_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 1);
lean_ctor_set(v___x_3633_, 1, v___x_3752_);
lean_ctor_set(v___x_3633_, 0, v___x_3756_);
v___x_3758_ = v___x_3633_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3752_);
v___x_3758_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set_tag(v___x_3624_, 1);
lean_ctor_set(v___x_3624_, 1, v___x_3758_);
lean_ctor_set(v___x_3624_, 0, v___x_3754_);
v___x_3760_ = v___x_3624_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
lean_inc_n(v___x_3745_, 2);
v___x_3761_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3745_);
lean_ctor_set(v___x_3761_, 1, v___x_3747_);
lean_ctor_set(v___x_3761_, 2, v___x_3750_);
lean_ctor_set(v___x_3761_, 3, v___x_3760_);
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3764_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 2);
lean_ctor_set(v___x_3619_, 1, v___x_3764_);
lean_ctor_set(v___x_3619_, 0, v___x_3745_);
v___x_3766_ = v___x_3619_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3767_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3768_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3743_);
lean_inc(v_quotContext_3742_);
v___x_3769_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3768_, v_currMacroScope_3743_);
lean_inc_n(v___x_3745_, 2);
v___x_3770_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3745_);
lean_ctor_set(v___x_3770_, 1, v___x_3767_);
lean_ctor_set(v___x_3770_, 2, v___x_3769_);
lean_ctor_set(v___x_3770_, 3, v___x_3752_);
v___x_3771_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 2);
lean_ctor_set(v___x_3615_, 1, v___x_3771_);
lean_ctor_set(v___x_3615_, 0, v___x_3745_);
v___x_3773_ = v___x_3615_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3745_, 22);
v___x_3776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3745_);
lean_ctor_set(v___x_3776_, 1, v___x_3774_);
v___x_3777_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3778_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3779_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3743_, 5);
lean_inc_n(v_quotContext_3742_, 5);
v___x_3780_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3779_, v_currMacroScope_3743_);
v___x_3781_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3745_);
lean_ctor_set(v___x_3781_, 1, v___x_3778_);
lean_ctor_set(v___x_3781_, 2, v___x_3780_);
lean_ctor_set(v___x_3781_, 3, v___x_3752_);
v___x_3782_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3783_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3784_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3783_, v_currMacroScope_3743_);
v___x_3785_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3745_);
lean_ctor_set(v___x_3785_, 1, v___x_3782_);
lean_ctor_set(v___x_3785_, 2, v___x_3784_);
lean_ctor_set(v___x_3785_, 3, v___x_3752_);
lean_inc_ref(v___x_3785_);
v___x_3786_ = l_Lean_Syntax_node2(v___x_3745_, v___x_3762_, v___x_3781_, v___x_3785_);
v___x_3787_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3745_);
lean_ctor_set(v___x_3788_, 1, v___x_3762_);
lean_ctor_set(v___x_3788_, 2, v___x_3787_);
v___x_3789_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3745_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
lean_inc_ref(v___x_3790_);
lean_inc_ref(v___x_3788_);
v___x_3791_ = l_Lean_Syntax_node4(v___x_3745_, v___x_3777_, v___x_3786_, v___x_3788_, v___x_3790_, v_snd_3631_);
lean_inc_ref(v___x_3776_);
v___x_3792_ = l_Lean_Syntax_node2(v___x_3745_, v___x_3775_, v___x_3776_, v___x_3791_);
v___x_3793_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3745_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
lean_inc_ref_n(v___x_3794_, 2);
lean_inc_ref_n(v___x_3773_, 2);
lean_inc_ref_n(v___x_3766_, 2);
v___x_3795_ = l_Lean_Syntax_node5(v___x_3745_, v___x_3763_, v___x_3766_, v___x_3770_, v___x_3773_, v___x_3792_, v___x_3794_);
v___x_3796_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3797_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3798_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3797_, v_currMacroScope_3743_);
v___x_3799_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3745_);
lean_ctor_set(v___x_3799_, 1, v___x_3796_);
lean_ctor_set(v___x_3799_, 2, v___x_3798_);
lean_ctor_set(v___x_3799_, 3, v___x_3752_);
v___x_3800_ = l_String_toRawSubstring_x27(v___x_3582_);
v___x_3801_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3570_, v_currMacroScope_3743_);
v___x_3802_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3745_);
lean_ctor_set(v___x_3802_, 1, v___x_3800_);
lean_ctor_set(v___x_3802_, 2, v___x_3801_);
lean_ctor_set(v___x_3802_, 3, v___x_3752_);
v___x_3803_ = l_Lean_Syntax_node2(v___x_3745_, v___x_3762_, v___x_3802_, v___x_3785_);
v___x_3804_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3805_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3806_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3805_, v_currMacroScope_3743_);
v___x_3807_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3745_);
lean_ctor_set(v___x_3807_, 1, v___x_3804_);
lean_ctor_set(v___x_3807_, 2, v___x_3806_);
lean_ctor_set(v___x_3807_, 3, v___x_3752_);
v___x_3808_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3812_ = l_Lean_addMacroScope(v_quotContext_3742_, v___x_3811_, v_currMacroScope_3743_);
v___x_3813_ = l_Lean_Name_mkStr4(v___x_3580_, v___x_3581_, v___x_3809_, v___x_3810_);
v___x_3814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v___x_3752_);
v___x_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
lean_ctor_set(v___x_3815_, 1, v___x_3752_);
v___x_3816_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3745_);
lean_ctor_set(v___x_3816_, 1, v___x_3808_);
lean_ctor_set(v___x_3816_, 2, v___x_3812_);
lean_ctor_set(v___x_3816_, 3, v___x_3815_);
v___x_3817_ = l_Lean_Syntax_node5(v___x_3745_, v___x_3763_, v___x_3766_, v___x_3807_, v___x_3773_, v___x_3816_, v___x_3794_);
v___x_3818_ = l_Lean_Syntax_node1(v___x_3745_, v___x_3762_, v___x_3817_);
v___x_3819_ = l_Lean_Syntax_node2(v___x_3745_, v___x_3746_, v_fst_3630_, v___x_3818_);
v___x_3820_ = l_Lean_Syntax_node4(v___x_3745_, v___x_3777_, v___x_3803_, v___x_3788_, v___x_3790_, v___x_3819_);
v___x_3821_ = l_Lean_Syntax_node2(v___x_3745_, v___x_3775_, v___x_3776_, v___x_3820_);
v___x_3822_ = l_Lean_Syntax_node5(v___x_3745_, v___x_3763_, v___x_3766_, v___x_3799_, v___x_3773_, v___x_3821_, v___x_3794_);
v___x_3823_ = l_Lean_Syntax_node2(v___x_3745_, v___x_3762_, v___x_3795_, v___x_3822_);
v___x_3824_ = l_Lean_Syntax_node2(v___x_3745_, v___x_3746_, v___x_3761_, v___x_3823_);
v_a_3593_ = v___x_3824_;
goto v___jp_3592_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_del_object(v___x_3609_);
v_e_3831_ = lean_ctor_get(v_default_3636_, 0);
lean_inc_ref(v_e_3831_);
lean_dec_ref_known(v_default_3636_, 1);
v___x_3832_ = lean_box(1);
v___x_3833_ = l_Lean_PrettyPrinter_delab(v_e_3831_, v___x_3832_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_toCold_3834_; lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3920_; 
v_toCold_3834_ = lean_ctor_get(v___y_3589_, 0);
lean_inc_ref(v_toCold_3834_);
v_a_3835_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3837_ = v___x_3833_;
v_isShared_3838_ = v_isSharedCheck_3920_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3833_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3920_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v_ref_3839_; lean_object* v_quotContext_3840_; lean_object* v_currMacroScope_3841_; uint8_t v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3852_; 
v_ref_3839_ = lean_ctor_get(v___y_3589_, 2);
lean_inc(v_ref_3839_);
lean_dec_ref(v___y_3589_);
v_quotContext_3840_ = lean_ctor_get(v_toCold_3834_, 8);
lean_inc_n(v_quotContext_3840_, 2);
v_currMacroScope_3841_ = lean_ctor_get(v_toCold_3834_, 9);
lean_inc_n(v_currMacroScope_3841_, 2);
lean_dec_ref(v_toCold_3834_);
v___x_3842_ = 0;
v___x_3843_ = l_Lean_SourceInfo_fromRef(v_ref_3839_, v___x_3842_);
lean_dec(v_ref_3839_);
v___x_3844_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3845_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3846_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3579_);
v___x_3847_ = l_Lean_Name_mkStr2(v___x_3579_, v___x_3846_);
v___x_3848_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3847_, v_currMacroScope_3841_);
v___x_3849_ = l_Lean_Name_mkStr4(v___x_3580_, v___x_3581_, v___x_3579_, v___x_3846_);
v___x_3850_ = lean_box(0);
lean_inc(v___x_3849_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 1);
lean_ctor_set(v___x_3638_, 1, v___x_3850_);
lean_ctor_set(v___x_3638_, 0, v___x_3849_);
v___x_3852_ = v___x_3638_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3854_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3849_);
v___x_3854_ = v___x_3837_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3849_);
v___x_3854_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3856_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 1);
lean_ctor_set(v___x_3633_, 1, v___x_3850_);
lean_ctor_set(v___x_3633_, 0, v___x_3854_);
v___x_3856_ = v___x_3633_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3854_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3850_);
v___x_3856_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3858_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set_tag(v___x_3624_, 1);
lean_ctor_set(v___x_3624_, 1, v___x_3856_);
lean_ctor_set(v___x_3624_, 0, v___x_3852_);
v___x_3858_ = v___x_3624_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3864_; 
lean_inc_n(v___x_3843_, 2);
v___x_3859_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3843_);
lean_ctor_set(v___x_3859_, 1, v___x_3845_);
lean_ctor_set(v___x_3859_, 2, v___x_3848_);
lean_ctor_set(v___x_3859_, 3, v___x_3858_);
v___x_3860_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3861_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3862_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 2);
lean_ctor_set(v___x_3619_, 1, v___x_3862_);
lean_ctor_set(v___x_3619_, 0, v___x_3843_);
v___x_3864_ = v___x_3619_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3865_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3866_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3841_);
lean_inc(v_quotContext_3840_);
v___x_3867_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3866_, v_currMacroScope_3841_);
lean_inc_n(v___x_3843_, 2);
v___x_3868_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3843_);
lean_ctor_set(v___x_3868_, 1, v___x_3865_);
lean_ctor_set(v___x_3868_, 2, v___x_3867_);
lean_ctor_set(v___x_3868_, 3, v___x_3850_);
v___x_3869_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 2);
lean_ctor_set(v___x_3615_, 1, v___x_3869_);
lean_ctor_set(v___x_3615_, 0, v___x_3843_);
v___x_3871_ = v___x_3615_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3872_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3873_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3843_, 21);
v___x_3874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3843_);
lean_ctor_set(v___x_3874_, 1, v___x_3872_);
v___x_3875_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3876_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3841_, 4);
lean_inc_n(v_quotContext_3840_, 4);
v___x_3878_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3877_, v_currMacroScope_3841_);
v___x_3879_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3843_);
lean_ctor_set(v___x_3879_, 1, v___x_3876_);
lean_ctor_set(v___x_3879_, 2, v___x_3878_);
lean_ctor_set(v___x_3879_, 3, v___x_3850_);
v___x_3880_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3881_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3882_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3881_, v_currMacroScope_3841_);
v___x_3883_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3843_);
lean_ctor_set(v___x_3883_, 1, v___x_3880_);
lean_ctor_set(v___x_3883_, 2, v___x_3882_);
lean_ctor_set(v___x_3883_, 3, v___x_3850_);
lean_inc_ref(v___x_3883_);
v___x_3884_ = l_Lean_Syntax_node2(v___x_3843_, v___x_3860_, v___x_3879_, v___x_3883_);
v___x_3885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3843_);
lean_ctor_set(v___x_3886_, 1, v___x_3860_);
lean_ctor_set(v___x_3886_, 2, v___x_3885_);
v___x_3887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3843_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
lean_inc_ref(v___x_3888_);
lean_inc_ref(v___x_3886_);
v___x_3889_ = l_Lean_Syntax_node4(v___x_3843_, v___x_3875_, v___x_3884_, v___x_3886_, v___x_3888_, v_snd_3631_);
lean_inc_ref(v___x_3874_);
v___x_3890_ = l_Lean_Syntax_node2(v___x_3843_, v___x_3873_, v___x_3874_, v___x_3889_);
v___x_3891_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3843_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
lean_inc_ref_n(v___x_3892_, 2);
lean_inc_ref_n(v___x_3871_, 2);
lean_inc_ref_n(v___x_3864_, 2);
v___x_3893_ = l_Lean_Syntax_node5(v___x_3843_, v___x_3861_, v___x_3864_, v___x_3868_, v___x_3871_, v___x_3890_, v___x_3892_);
v___x_3894_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3895_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3896_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3895_, v_currMacroScope_3841_);
v___x_3897_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3843_);
lean_ctor_set(v___x_3897_, 1, v___x_3894_);
lean_ctor_set(v___x_3897_, 2, v___x_3896_);
lean_ctor_set(v___x_3897_, 3, v___x_3850_);
v___x_3898_ = l_String_toRawSubstring_x27(v___x_3582_);
v___x_3899_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3570_, v_currMacroScope_3841_);
v___x_3900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3843_);
lean_ctor_set(v___x_3900_, 1, v___x_3898_);
lean_ctor_set(v___x_3900_, 2, v___x_3899_);
lean_ctor_set(v___x_3900_, 3, v___x_3850_);
v___x_3901_ = l_Lean_Syntax_node2(v___x_3843_, v___x_3860_, v___x_3900_, v___x_3883_);
v___x_3902_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3904_ = l_Lean_addMacroScope(v_quotContext_3840_, v___x_3903_, v_currMacroScope_3841_);
v___x_3905_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3843_);
lean_ctor_set(v___x_3905_, 1, v___x_3902_);
lean_ctor_set(v___x_3905_, 2, v___x_3904_);
lean_ctor_set(v___x_3905_, 3, v___x_3850_);
v___x_3906_ = l_Lean_Syntax_node5(v___x_3843_, v___x_3861_, v___x_3864_, v___x_3905_, v___x_3871_, v_a_3835_, v___x_3892_);
v___x_3907_ = l_Lean_Syntax_node1(v___x_3843_, v___x_3860_, v___x_3906_);
v___x_3908_ = l_Lean_Syntax_node2(v___x_3843_, v___x_3844_, v_fst_3630_, v___x_3907_);
v___x_3909_ = l_Lean_Syntax_node4(v___x_3843_, v___x_3875_, v___x_3901_, v___x_3886_, v___x_3888_, v___x_3908_);
v___x_3910_ = l_Lean_Syntax_node2(v___x_3843_, v___x_3873_, v___x_3874_, v___x_3909_);
v___x_3911_ = l_Lean_Syntax_node5(v___x_3843_, v___x_3861_, v___x_3864_, v___x_3897_, v___x_3871_, v___x_3910_, v___x_3892_);
v___x_3912_ = l_Lean_Syntax_node2(v___x_3843_, v___x_3860_, v___x_3893_, v___x_3911_);
v___x_3913_ = l_Lean_Syntax_node2(v___x_3843_, v___x_3844_, v___x_3859_, v___x_3912_);
v_a_3593_ = v___x_3913_;
goto v___jp_3592_;
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
lean_del_object(v___x_3638_);
lean_del_object(v___x_3633_);
lean_dec(v_snd_3631_);
lean_dec(v_fst_3630_);
lean_del_object(v___x_3624_);
lean_del_object(v___x_3619_);
lean_del_object(v___x_3615_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec(v___x_3570_);
v___y_3597_ = v___x_3833_;
goto v___jp_3596_;
}
}
default: 
{
lean_object* v_toCold_3921_; lean_object* v_ref_3922_; lean_object* v_quotContext_3923_; lean_object* v_currMacroScope_3924_; uint8_t v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
lean_dec(v_default_3636_);
v_toCold_3921_ = lean_ctor_get(v___y_3589_, 0);
lean_inc_ref(v_toCold_3921_);
v_ref_3922_ = lean_ctor_get(v___y_3589_, 2);
lean_inc(v_ref_3922_);
lean_dec_ref(v___y_3589_);
v_quotContext_3923_ = lean_ctor_get(v_toCold_3921_, 8);
lean_inc_n(v_quotContext_3923_, 2);
v_currMacroScope_3924_ = lean_ctor_get(v_toCold_3921_, 9);
lean_inc_n(v_currMacroScope_3924_, 2);
lean_dec_ref(v_toCold_3921_);
v___x_3925_ = 0;
v___x_3926_ = l_Lean_SourceInfo_fromRef(v_ref_3922_, v___x_3925_);
lean_dec(v_ref_3922_);
v___x_3927_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3928_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3579_);
v___x_3930_ = l_Lean_Name_mkStr2(v___x_3579_, v___x_3929_);
v___x_3931_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3930_, v_currMacroScope_3924_);
v___x_3932_ = l_Lean_Name_mkStr4(v___x_3580_, v___x_3581_, v___x_3579_, v___x_3929_);
v___x_3933_ = lean_box(0);
lean_inc(v___x_3932_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 1);
lean_ctor_set(v___x_3638_, 1, v___x_3933_);
lean_ctor_set(v___x_3638_, 0, v___x_3932_);
v___x_3935_ = v___x_3638_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3937_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3932_);
v___x_3937_ = v___x_3609_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3932_);
v___x_3937_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3939_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 1);
lean_ctor_set(v___x_3633_, 1, v___x_3933_);
lean_ctor_set(v___x_3633_, 0, v___x_3937_);
v___x_3939_ = v___x_3633_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v___x_3933_);
v___x_3939_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3941_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set_tag(v___x_3624_, 1);
lean_ctor_set(v___x_3624_, 1, v___x_3939_);
lean_ctor_set(v___x_3624_, 0, v___x_3935_);
v___x_3941_ = v___x_3624_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
lean_inc_n(v___x_3926_, 2);
v___x_3942_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3926_);
lean_ctor_set(v___x_3942_, 1, v___x_3928_);
lean_ctor_set(v___x_3942_, 2, v___x_3931_);
lean_ctor_set(v___x_3942_, 3, v___x_3941_);
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3945_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 2);
lean_ctor_set(v___x_3619_, 1, v___x_3945_);
lean_ctor_set(v___x_3619_, 0, v___x_3926_);
v___x_3947_ = v___x_3619_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3948_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3949_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3924_);
lean_inc(v_quotContext_3923_);
v___x_3950_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3949_, v_currMacroScope_3924_);
lean_inc_n(v___x_3926_, 2);
v___x_3951_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3926_);
lean_ctor_set(v___x_3951_, 1, v___x_3948_);
lean_ctor_set(v___x_3951_, 2, v___x_3950_);
lean_ctor_set(v___x_3951_, 3, v___x_3933_);
v___x_3952_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 2);
lean_ctor_set(v___x_3615_, 1, v___x_3952_);
lean_ctor_set(v___x_3615_, 0, v___x_3926_);
v___x_3954_ = v___x_3615_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3955_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3956_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3926_, 17);
v___x_3957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3926_);
lean_ctor_set(v___x_3957_, 1, v___x_3955_);
v___x_3958_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3959_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3960_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3924_, 3);
lean_inc_n(v_quotContext_3923_, 3);
v___x_3961_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3960_, v_currMacroScope_3924_);
v___x_3962_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3926_);
lean_ctor_set(v___x_3962_, 1, v___x_3959_);
lean_ctor_set(v___x_3962_, 2, v___x_3961_);
lean_ctor_set(v___x_3962_, 3, v___x_3933_);
v___x_3963_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3964_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3965_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3964_, v_currMacroScope_3924_);
v___x_3966_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3926_);
lean_ctor_set(v___x_3966_, 1, v___x_3963_);
lean_ctor_set(v___x_3966_, 2, v___x_3965_);
lean_ctor_set(v___x_3966_, 3, v___x_3933_);
lean_inc_ref(v___x_3966_);
v___x_3967_ = l_Lean_Syntax_node2(v___x_3926_, v___x_3943_, v___x_3962_, v___x_3966_);
v___x_3968_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3926_);
lean_ctor_set(v___x_3969_, 1, v___x_3943_);
lean_ctor_set(v___x_3969_, 2, v___x_3968_);
v___x_3970_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3926_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
lean_inc_ref(v___x_3971_);
lean_inc_ref(v___x_3969_);
v___x_3972_ = l_Lean_Syntax_node4(v___x_3926_, v___x_3958_, v___x_3967_, v___x_3969_, v___x_3971_, v_snd_3631_);
lean_inc_ref(v___x_3957_);
v___x_3973_ = l_Lean_Syntax_node2(v___x_3926_, v___x_3956_, v___x_3957_, v___x_3972_);
v___x_3974_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3926_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
lean_inc_ref(v___x_3975_);
lean_inc_ref(v___x_3954_);
lean_inc_ref(v___x_3947_);
v___x_3976_ = l_Lean_Syntax_node5(v___x_3926_, v___x_3944_, v___x_3947_, v___x_3951_, v___x_3954_, v___x_3973_, v___x_3975_);
v___x_3977_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3978_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3979_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3978_, v_currMacroScope_3924_);
v___x_3980_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3926_);
lean_ctor_set(v___x_3980_, 1, v___x_3977_);
lean_ctor_set(v___x_3980_, 2, v___x_3979_);
lean_ctor_set(v___x_3980_, 3, v___x_3933_);
v___x_3981_ = l_String_toRawSubstring_x27(v___x_3582_);
v___x_3982_ = l_Lean_addMacroScope(v_quotContext_3923_, v___x_3570_, v_currMacroScope_3924_);
v___x_3983_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3926_);
lean_ctor_set(v___x_3983_, 1, v___x_3981_);
lean_ctor_set(v___x_3983_, 2, v___x_3982_);
lean_ctor_set(v___x_3983_, 3, v___x_3933_);
v___x_3984_ = l_Lean_Syntax_node2(v___x_3926_, v___x_3943_, v___x_3983_, v___x_3966_);
v___x_3985_ = l_Lean_Syntax_node4(v___x_3926_, v___x_3958_, v___x_3984_, v___x_3969_, v___x_3971_, v_fst_3630_);
v___x_3986_ = l_Lean_Syntax_node2(v___x_3926_, v___x_3956_, v___x_3957_, v___x_3985_);
v___x_3987_ = l_Lean_Syntax_node5(v___x_3926_, v___x_3944_, v___x_3947_, v___x_3980_, v___x_3954_, v___x_3986_, v___x_3975_);
v___x_3988_ = l_Lean_Syntax_node2(v___x_3926_, v___x_3943_, v___x_3976_, v___x_3987_);
v___x_3989_ = l_Lean_Syntax_node2(v___x_3926_, v___x_3927_, v___x_3942_, v___x_3988_);
v_a_3593_ = v___x_3989_;
goto v___jp_3592_;
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
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_del_object(v___x_3624_);
lean_dec(v_snd_3622_);
lean_del_object(v___x_3619_);
lean_del_object(v___x_3615_);
lean_del_object(v___x_3609_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec(v___x_3578_);
lean_dec(v___x_3570_);
v_a_3998_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3628_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3628_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
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
lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4085_; 
lean_dec(v_a_3600_);
lean_dec(v___x_3578_);
lean_dec(v___x_3577_);
lean_dec_ref(v___x_3571_);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_val_3603_);
if (v_isSharedCheck_4085_ == 0)
{
lean_object* v_unused_4086_; lean_object* v_unused_4087_; 
v_unused_4086_ = lean_ctor_get(v_val_3603_, 1);
lean_dec(v_unused_4086_);
v_unused_4087_ = lean_ctor_get(v_val_3603_, 0);
lean_dec(v_unused_4087_);
v___x_4012_ = v_val_3603_;
v_isShared_4013_ = v_isSharedCheck_4085_;
goto v_resetjp_4011_;
}
else
{
lean_dec(v_val_3603_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4085_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v_toCold_4014_; lean_object* v_ref_4015_; lean_object* v_quotContext_4016_; lean_object* v_currMacroScope_4017_; uint8_t v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
v_toCold_4014_ = lean_ctor_get(v___y_3589_, 0);
lean_inc_ref(v_toCold_4014_);
v_ref_4015_ = lean_ctor_get(v___y_3589_, 2);
lean_inc(v_ref_4015_);
lean_dec_ref(v___y_3589_);
v_quotContext_4016_ = lean_ctor_get(v_toCold_4014_, 8);
lean_inc_n(v_quotContext_4016_, 2);
v_currMacroScope_4017_ = lean_ctor_get(v_toCold_4014_, 9);
lean_inc_n(v_currMacroScope_4017_, 2);
lean_dec_ref(v_toCold_4014_);
v___x_4018_ = 0;
v___x_4019_ = l_Lean_SourceInfo_fromRef(v_ref_4015_, v___x_4018_);
lean_dec(v_ref_4015_);
v___x_4020_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4021_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4022_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3579_);
v___x_4023_ = l_Lean_Name_mkStr2(v___x_3579_, v___x_4022_);
v___x_4024_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4023_, v_currMacroScope_4017_);
v___x_4025_ = l_Lean_Name_mkStr4(v___x_3580_, v___x_3581_, v___x_3579_, v___x_4022_);
v___x_4026_ = lean_box(0);
lean_inc(v___x_4025_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set_tag(v___x_4012_, 1);
lean_ctor_set(v___x_4012_, 1, v___x_4026_);
lean_ctor_set(v___x_4012_, 0, v___x_4025_);
v___x_4028_ = v___x_4012_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set_tag(v___x_3605_, 0);
lean_ctor_set(v___x_3605_, 0, v___x_4025_);
v___x_4030_ = v___x_3605_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4025_);
v___x_4030_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
lean_ctor_set(v___x_4031_, 1, v___x_4026_);
v___x_4032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4028_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
lean_inc_n(v___x_4019_, 23);
v___x_4033_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4019_);
lean_ctor_set(v___x_4033_, 1, v___x_4021_);
lean_ctor_set(v___x_4033_, 2, v___x_4024_);
lean_ctor_set(v___x_4033_, 3, v___x_4032_);
v___x_4034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4035_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4036_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_4037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4019_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4039_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_4017_, 4);
lean_inc_n(v_quotContext_4016_, 4);
v___x_4040_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4039_, v_currMacroScope_4017_);
v___x_4041_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4019_);
lean_ctor_set(v___x_4041_, 1, v___x_4038_);
lean_ctor_set(v___x_4041_, 2, v___x_4040_);
lean_ctor_set(v___x_4041_, 3, v___x_4026_);
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_4043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4019_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4045_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
v___x_4046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4019_);
lean_ctor_set(v___x_4046_, 1, v___x_4044_);
v___x_4047_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4048_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4049_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_4050_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4049_, v_currMacroScope_4017_);
v___x_4051_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4019_);
lean_ctor_set(v___x_4051_, 1, v___x_4048_);
lean_ctor_set(v___x_4051_, 2, v___x_4050_);
lean_ctor_set(v___x_4051_, 3, v___x_4026_);
v___x_4052_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4053_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4054_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4053_, v_currMacroScope_4017_);
v___x_4055_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4019_);
lean_ctor_set(v___x_4055_, 1, v___x_4052_);
lean_ctor_set(v___x_4055_, 2, v___x_4054_);
lean_ctor_set(v___x_4055_, 3, v___x_4026_);
lean_inc_ref(v___x_4055_);
v___x_4056_ = l_Lean_Syntax_node2(v___x_4019_, v___x_4034_, v___x_4051_, v___x_4055_);
v___x_4057_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4019_);
lean_ctor_set(v___x_4058_, 1, v___x_4034_);
lean_ctor_set(v___x_4058_, 2, v___x_4057_);
v___x_4059_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4019_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4062_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4019_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
v___x_4064_ = l_Lean_Syntax_node1(v___x_4019_, v___x_4061_, v___x_4063_);
lean_inc(v___x_4064_);
lean_inc_ref(v___x_4060_);
lean_inc_ref(v___x_4058_);
v___x_4065_ = l_Lean_Syntax_node4(v___x_4019_, v___x_4047_, v___x_4056_, v___x_4058_, v___x_4060_, v___x_4064_);
lean_inc_ref(v___x_4046_);
v___x_4066_ = l_Lean_Syntax_node2(v___x_4019_, v___x_4045_, v___x_4046_, v___x_4065_);
v___x_4067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4019_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
lean_inc_ref(v___x_4068_);
lean_inc_ref(v___x_4043_);
lean_inc_ref(v___x_4037_);
v___x_4069_ = l_Lean_Syntax_node5(v___x_4019_, v___x_4035_, v___x_4037_, v___x_4041_, v___x_4043_, v___x_4066_, v___x_4068_);
v___x_4070_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4071_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4072_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4071_, v_currMacroScope_4017_);
v___x_4073_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4019_);
lean_ctor_set(v___x_4073_, 1, v___x_4070_);
lean_ctor_set(v___x_4073_, 2, v___x_4072_);
lean_ctor_set(v___x_4073_, 3, v___x_4026_);
v___x_4074_ = l_String_toRawSubstring_x27(v___x_3582_);
v___x_4075_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_3570_, v_currMacroScope_4017_);
v___x_4076_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4019_);
lean_ctor_set(v___x_4076_, 1, v___x_4074_);
lean_ctor_set(v___x_4076_, 2, v___x_4075_);
lean_ctor_set(v___x_4076_, 3, v___x_4026_);
v___x_4077_ = l_Lean_Syntax_node2(v___x_4019_, v___x_4034_, v___x_4076_, v___x_4055_);
v___x_4078_ = l_Lean_Syntax_node4(v___x_4019_, v___x_4047_, v___x_4077_, v___x_4058_, v___x_4060_, v___x_4064_);
v___x_4079_ = l_Lean_Syntax_node2(v___x_4019_, v___x_4045_, v___x_4046_, v___x_4078_);
v___x_4080_ = l_Lean_Syntax_node5(v___x_4019_, v___x_4035_, v___x_4037_, v___x_4073_, v___x_4043_, v___x_4079_, v___x_4068_);
v___x_4081_ = l_Lean_Syntax_node2(v___x_4019_, v___x_4034_, v___x_4069_, v___x_4080_);
v___x_4082_ = l_Lean_Syntax_node2(v___x_4019_, v___x_4020_, v___x_4033_, v___x_4081_);
v_a_3593_ = v___x_4082_;
goto v___jp_3592_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3602_);
lean_dec_ref(v___x_3579_);
if (lean_obj_tag(v_a_3600_) == 1)
{
lean_object* v_val_4089_; lean_object* v_snd_4090_; lean_object* v_fst_4091_; lean_object* v_snd_4092_; lean_object* v___x_4093_; lean_object* v___f_4094_; lean_object* v___x_4095_; 
v_val_4089_ = lean_ctor_get(v_a_3600_, 0);
lean_inc(v_val_4089_);
lean_dec_ref_known(v_a_3600_, 1);
v_snd_4090_ = lean_ctor_get(v_val_4089_, 1);
lean_inc(v_snd_4090_);
v_fst_4091_ = lean_ctor_get(v_val_4089_, 0);
lean_inc(v_fst_4091_);
lean_dec(v_val_4089_);
v_snd_4092_ = lean_ctor_get(v_snd_4090_, 1);
lean_inc(v_snd_4092_);
lean_dec(v_snd_4090_);
v___x_4093_ = lean_box(v___x_3576_);
lean_inc(v___x_3570_);
v___f_4094_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4094_, 0, v_fst_4091_);
lean_closure_set(v___f_4094_, 1, v_snd_4092_);
lean_closure_set(v___f_4094_, 2, v___x_3582_);
lean_closure_set(v___f_4094_, 3, v___x_3570_);
lean_closure_set(v___f_4094_, 4, v___x_3577_);
lean_closure_set(v___f_4094_, 5, v___x_3578_);
lean_closure_set(v___f_4094_, 6, v___x_3580_);
lean_closure_set(v___f_4094_, 7, v___x_3581_);
lean_closure_set(v___f_4094_, 8, v___x_4093_);
lean_closure_set(v___f_4094_, 9, v_arg_3575_);
v___x_4095_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3570_, v___x_3571_, v___f_4094_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec_ref(v___y_3589_);
v___y_3597_ = v___x_4095_;
goto v___jp_3596_;
}
else
{
lean_object* v_toCold_4096_; lean_object* v_ref_4097_; lean_object* v_quotContext_4098_; lean_object* v_currMacroScope_4099_; uint8_t v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_dec(v_a_3600_);
lean_dec(v___x_3578_);
lean_dec(v___x_3577_);
lean_dec_ref(v_arg_3575_);
lean_dec_ref(v___x_3571_);
v_toCold_4096_ = lean_ctor_get(v___y_3589_, 0);
lean_inc_ref(v_toCold_4096_);
v_ref_4097_ = lean_ctor_get(v___y_3589_, 2);
lean_inc(v_ref_4097_);
lean_dec_ref(v___y_3589_);
v_quotContext_4098_ = lean_ctor_get(v_toCold_4096_, 8);
lean_inc_n(v_quotContext_4098_, 2);
v_currMacroScope_4099_ = lean_ctor_get(v_toCold_4096_, 9);
lean_inc_n(v_currMacroScope_4099_, 2);
lean_dec_ref(v_toCold_4096_);
v___x_4100_ = 0;
v___x_4101_ = l_Lean_SourceInfo_fromRef(v_ref_4097_, v___x_4100_);
lean_dec(v_ref_4097_);
v___x_4102_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4103_ = l_Lean_Name_mkStr3(v___x_3580_, v___x_3581_, v___x_4102_);
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4105_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4101_, 13);
v___x_4106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4101_);
lean_ctor_set(v___x_4106_, 1, v___x_4104_);
lean_ctor_set(v___x_4106_, 2, v___x_4105_);
v___x_4107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_4108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4101_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4101_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = l_String_toRawSubstring_x27(v___x_3582_);
v___x_4114_ = l_Lean_addMacroScope(v_quotContext_4098_, v___x_3570_, v_currMacroScope_4099_);
v___x_4115_ = lean_box(0);
v___x_4116_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4101_);
lean_ctor_set(v___x_4116_, 1, v___x_4113_);
lean_ctor_set(v___x_4116_, 2, v___x_4114_);
lean_ctor_set(v___x_4116_, 3, v___x_4115_);
v___x_4117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4101_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4120_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4121_ = l_Lean_addMacroScope(v_quotContext_4098_, v___x_4120_, v_currMacroScope_4099_);
v___x_4122_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4101_);
lean_ctor_set(v___x_4122_, 1, v___x_4119_);
lean_ctor_set(v___x_4122_, 2, v___x_4121_);
lean_ctor_set(v___x_4122_, 3, v___x_4115_);
v___x_4123_ = l_Lean_Syntax_node3(v___x_4101_, v___x_4109_, v___x_4116_, v___x_4118_, v___x_4122_);
v___x_4124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4101_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_Syntax_node3(v___x_4101_, v___x_4110_, v___x_4112_, v___x_4123_, v___x_4125_);
v___x_4127_ = l_Lean_Syntax_node1(v___x_4101_, v___x_4109_, v___x_4126_);
v___x_4128_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4101_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4131_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4101_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l_Lean_Syntax_node1(v___x_4101_, v___x_4130_, v___x_4132_);
v___x_4134_ = l_Lean_Syntax_node5(v___x_4101_, v___x_4103_, v___x_4106_, v___x_4108_, v___x_4127_, v___x_4129_, v___x_4133_);
v_a_3593_ = v___x_4134_;
goto v___jp_3592_;
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v_a_3600_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec(v___x_3578_);
lean_dec(v___x_3577_);
lean_dec_ref(v_arg_3575_);
lean_dec_ref(v___x_3571_);
lean_dec(v___x_3570_);
v_a_4135_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_3601_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_3601_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v___x_3581_);
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___x_3579_);
lean_dec(v___x_3578_);
lean_dec(v___x_3577_);
lean_dec_ref(v_arg_3575_);
lean_dec(v_inv_3574_);
lean_dec_ref(v___x_3571_);
lean_dec(v___x_3570_);
v_a_4143_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_3599_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_3599_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
v___jp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3593_);
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
return v___x_3595_;
}
v___jp_3596_:
{
if (lean_obj_tag(v___y_3597_) == 0)
{
lean_object* v_a_3598_; 
v_a_3598_ = lean_ctor_get(v___y_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___y_3597_, 1);
v_a_3593_ = v_a_3598_;
goto v___jp_3592_;
}
else
{
return v___y_3597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4151_ = _args[0];
lean_object* v___x_4152_ = _args[1];
lean_object* v___f_4153_ = _args[2];
lean_object* v_a_4154_ = _args[3];
lean_object* v_inv_4155_ = _args[4];
lean_object* v_arg_4156_ = _args[5];
lean_object* v___x_4157_ = _args[6];
lean_object* v___x_4158_ = _args[7];
lean_object* v___x_4159_ = _args[8];
lean_object* v___x_4160_ = _args[9];
lean_object* v___x_4161_ = _args[10];
lean_object* v___x_4162_ = _args[11];
lean_object* v___x_4163_ = _args[12];
lean_object* v___y_4164_ = _args[13];
lean_object* v___y_4165_ = _args[14];
lean_object* v___y_4166_ = _args[15];
lean_object* v___y_4167_ = _args[16];
lean_object* v___y_4168_ = _args[17];
lean_object* v___y_4169_ = _args[18];
lean_object* v___y_4170_ = _args[19];
lean_object* v___y_4171_ = _args[20];
lean_object* v___y_4172_ = _args[21];
_start:
{
uint8_t v___x_79051__boxed_4173_; lean_object* v_res_4174_; 
v___x_79051__boxed_4173_ = lean_unbox(v___x_4157_);
v_res_4174_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4151_, v___x_4152_, v___f_4153_, v_a_4154_, v_inv_4155_, v_arg_4156_, v___x_79051__boxed_4173_, v___x_4158_, v___x_4159_, v___x_4160_, v___x_4161_, v___x_4162_, v___x_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
lean_dec(v___y_4171_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec_ref(v_a_4154_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___x_4181_; lean_object* v_env_4182_; lean_object* v___x_4183_; lean_object* v_toCold_4184_; lean_object* v_mctx_4185_; lean_object* v_lctx_4186_; lean_object* v_options_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4181_ = lean_st_ref_get(v___y_4179_);
v_env_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc_ref(v_env_4182_);
lean_dec(v___x_4181_);
v___x_4183_ = lean_st_ref_get(v___y_4177_);
v_toCold_4184_ = lean_ctor_get(v___y_4178_, 0);
v_mctx_4185_ = lean_ctor_get(v___x_4183_, 0);
lean_inc_ref(v_mctx_4185_);
lean_dec(v___x_4183_);
v_lctx_4186_ = lean_ctor_get(v___y_4176_, 2);
v_options_4187_ = lean_ctor_get(v_toCold_4184_, 2);
lean_inc_ref(v_options_4187_);
lean_inc_ref(v_lctx_4186_);
v___x_4188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4188_, 0, v_env_4182_);
lean_ctor_set(v___x_4188_, 1, v_mctx_4185_);
lean_ctor_set(v___x_4188_, 2, v_lctx_4186_);
lean_ctor_set(v___x_4188_, 3, v_options_4187_);
v___x_4189_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
lean_ctor_set(v___x_4189_, 1, v_msgData_4175_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v_ref_4204_; lean_object* v___x_4205_; lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4214_; 
v_ref_4204_ = lean_ctor_get(v___y_4201_, 2);
v___x_4205_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4208_ = v___x_4205_;
v_isShared_4209_ = v_isSharedCheck_4214_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4205_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4214_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
lean_inc(v_ref_4204_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v_ref_4204_);
lean_ctor_set(v___x_4210_, 1, v_a_4206_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set_tag(v___x_4208_, 1);
lean_ctor_set(v___x_4208_, 0, v___x_4210_);
v___x_4212_ = v___x_4208_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4228_, size_t v_i_4229_, size_t v_stop_4230_, lean_object* v_b_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_a_4242_; lean_object* v_a_4247_; uint8_t v___x_4249_; 
v___x_4249_ = lean_usize_dec_eq(v_i_4229_, v_stop_4230_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4233_, v___y_4235_, v___y_4237_, v___y_4239_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v___x_4252_; lean_object* v___y_4254_; uint8_t v___y_4255_; lean_object* v___y_4270_; lean_object* v_a_4271_; lean_object* v___x_4274_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v___x_4250_, 1);
v___x_4252_ = lean_array_uget_borrowed(v_as_4228_, v_i_4229_);
lean_inc(v___x_4252_);
v___x_4274_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4252_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v_ref_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref_known(v___x_4274_, 1);
v_ref_4276_ = lean_ctor_get(v___y_4238_, 2);
v___x_4277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
v___x_4279_ = l_Lean_SourceInfo_fromRef(v_ref_4276_, v___x_4249_);
lean_inc(v___x_4279_);
v___x_4280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
lean_ctor_set(v___x_4280_, 1, v___x_4277_);
v___x_4281_ = l_Lean_Syntax_node1(v___x_4279_, v___x_4278_, v___x_4280_);
v___x_4282_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4281_, v_a_4275_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4284_; 
lean_dec(v_a_4251_);
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = lean_array_mk(v_a_4283_);
v_a_4247_ = v___x_4284_;
goto v___jp_4246_;
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
v_a_4285_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4282_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4282_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
lean_inc(v_a_4285_);
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
v___y_4270_ = v___x_4290_;
v_a_4271_ = v_a_4285_;
goto v___jp_4269_;
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
v_a_4293_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4274_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4274_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
lean_inc(v_a_4293_);
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
v___y_4270_ = v___x_4298_;
v_a_4271_ = v_a_4293_;
goto v___jp_4269_;
}
}
}
v___jp_4253_:
{
if (v___y_4255_ == 0)
{
lean_object* v___x_4256_; 
lean_dec_ref(v___y_4254_);
v___x_4256_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4251_, v___y_4255_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
lean_dec_ref_known(v___x_4256_, 1);
v___x_4257_ = lean_unsigned_to_nat(1u);
v___x_4258_ = lean_mk_empty_array_with_capacity(v___x_4257_);
lean_inc(v___x_4252_);
v___x_4259_ = lean_array_push(v___x_4258_, v___x_4252_);
v_a_4247_ = v___x_4259_;
goto v___jp_4246_;
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref(v_b_4231_);
v_a_4260_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4256_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4256_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
lean_dec(v_a_4251_);
lean_dec_ref(v_b_4231_);
if (lean_obj_tag(v___y_4254_) == 0)
{
lean_object* v_a_4268_; 
v_a_4268_ = lean_ctor_get(v___y_4254_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v___y_4254_, 1);
v_a_4242_ = v_a_4268_;
goto v___jp_4241_;
}
else
{
return v___y_4254_;
}
}
}
v___jp_4269_:
{
uint8_t v___x_4272_; 
v___x_4272_ = l_Lean_Exception_isInterrupt(v_a_4271_);
if (v___x_4272_ == 0)
{
uint8_t v___x_4273_; 
v___x_4273_ = l_Lean_Exception_isRuntime(v_a_4271_);
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___x_4273_;
goto v___jp_4253_;
}
else
{
lean_dec_ref(v_a_4271_);
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___x_4272_;
goto v___jp_4253_;
}
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec_ref(v_b_4231_);
v_a_4301_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4250_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4250_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v_b_4231_);
return v___x_4309_;
}
v___jp_4241_:
{
size_t v___x_4243_; size_t v___x_4244_; 
v___x_4243_ = ((size_t)1ULL);
v___x_4244_ = lean_usize_add(v_i_4229_, v___x_4243_);
v_i_4229_ = v___x_4244_;
v_b_4231_ = v_a_4242_;
goto _start;
}
v___jp_4246_:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Array_append___redArg(v_b_4231_, v_a_4247_);
lean_dec_ref(v_a_4247_);
v_a_4242_ = v___x_4248_;
goto v___jp_4241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4310_, lean_object* v_i_4311_, lean_object* v_stop_4312_, lean_object* v_b_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
size_t v_i_boxed_4323_; size_t v_stop_boxed_4324_; lean_object* v_res_4325_; 
v_i_boxed_4323_ = lean_unbox_usize(v_i_4311_);
lean_dec(v_i_4311_);
v_stop_boxed_4324_ = lean_unbox_usize(v_stop_4312_);
lean_dec(v_stop_4312_);
v_res_4325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4310_, v_i_boxed_4323_, v_stop_boxed_4324_, v_b_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec_ref(v_as_4310_);
return v_res_4325_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4328_ = l_Lean_stringToMessageData(v___x_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4344_, lean_object* v_inv_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v___x_4355_; 
lean_inc(v_inv_4345_);
v___x_4355_ = l_Lean_MVarId_getType(v_inv_4345_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; lean_object* v_a_4358_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___x_4372_; uint8_t v___x_4373_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4356_, v_a_4351_);
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc_n(v_a_4358_, 2);
lean_dec_ref(v___x_4357_);
v___x_4372_ = l_Lean_Expr_cleanupAnnotations(v_a_4358_);
v___x_4373_ = l_Lean_Expr_isApp(v___x_4372_);
if (v___x_4373_ == 0)
{
lean_dec_ref(v___x_4372_);
lean_dec(v_inv_4345_);
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
goto v___jp_4359_;
}
else
{
lean_object* v___x_4374_; uint8_t v___x_4375_; 
v___x_4374_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4372_);
v___x_4375_ = l_Lean_Expr_isApp(v___x_4374_);
if (v___x_4375_ == 0)
{
lean_dec_ref(v___x_4374_);
lean_dec(v_inv_4345_);
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
goto v___jp_4359_;
}
else
{
lean_object* v_arg_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; 
v_arg_4376_ = lean_ctor_get(v___x_4374_, 1);
lean_inc_ref(v_arg_4376_);
v___x_4377_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4374_);
v___x_4378_ = l_Lean_Expr_isApp(v___x_4377_);
if (v___x_4378_ == 0)
{
lean_dec_ref(v___x_4377_);
lean_dec_ref(v_arg_4376_);
lean_dec(v_inv_4345_);
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
goto v___jp_4359_;
}
else
{
lean_object* v_arg_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v_arg_4379_ = lean_ctor_get(v___x_4377_, 1);
lean_inc_ref(v_arg_4379_);
v___x_4380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4377_);
v___x_4381_ = l_Lean_Expr_isApp(v___x_4380_);
if (v___x_4381_ == 0)
{
lean_dec_ref(v___x_4380_);
lean_dec_ref(v_arg_4379_);
lean_dec_ref(v_arg_4376_);
lean_dec(v_inv_4345_);
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
goto v___jp_4359_;
}
else
{
lean_object* v_arg_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; uint8_t v___x_4388_; 
v_arg_4382_ = lean_ctor_get(v___x_4380_, 1);
lean_inc_ref(v_arg_4382_);
v___x_4383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4380_);
v___x_4384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4386_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4387_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4388_ = l_Lean_Expr_isConstOf(v___x_4383_, v___x_4387_);
if (v___x_4388_ == 0)
{
lean_dec_ref(v___x_4383_);
lean_dec_ref(v_arg_4382_);
lean_dec_ref(v_arg_4379_);
lean_dec_ref(v_arg_4376_);
lean_dec(v_inv_4345_);
v___y_4360_ = v_a_4346_;
v___y_4361_ = v_a_4347_;
v___y_4362_ = v_a_4348_;
v___y_4363_ = v_a_4349_;
v___y_4364_ = v_a_4350_;
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
goto v___jp_4359_;
}
else
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v_a_4395_; lean_object* v___x_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
lean_dec(v_a_4358_);
v___x_4389_ = lean_unsigned_to_nat(1u);
v___x_4390_ = l_Lean_Expr_constLevels_x21(v___x_4383_);
lean_dec_ref(v___x_4383_);
v___x_4391_ = lean_unsigned_to_nat(0u);
v___x_4392_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4390_);
v___x_4393_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4390_, v___x_4390_, v___x_4389_, v___x_4392_);
lean_dec(v___x_4390_);
v___x_4406_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4407_ = lean_array_get_size(v_vcs_4344_);
v___x_4408_ = lean_nat_dec_lt(v___x_4391_, v___x_4407_);
if (v___x_4408_ == 0)
{
v_a_4395_ = v___x_4406_;
goto v___jp_4394_;
}
else
{
size_t v___x_4409_; size_t v___x_4410_; lean_object* v___x_4411_; 
v___x_4409_ = ((size_t)0ULL);
v___x_4410_ = lean_usize_of_nat(v___x_4407_);
v___x_4411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4344_, v___x_4409_, v___x_4410_, v___x_4406_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v_a_4395_ = v_a_4412_;
goto v___jp_4394_;
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v___x_4393_);
lean_dec_ref(v_arg_4382_);
lean_dec_ref(v_arg_4379_);
lean_dec_ref(v_arg_4376_);
lean_dec(v_inv_4345_);
v_a_4413_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4411_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4411_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
v___jp_4394_:
{
lean_object* v___x_4396_; lean_object* v___f_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___f_4404_; lean_object* v___x_4405_; 
v___x_4396_ = lean_box(v___x_4388_);
lean_inc_ref(v_arg_4376_);
lean_inc_n(v_inv_4345_, 2);
lean_inc_ref(v_a_4395_);
v___f_4397_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4397_, 0, v_a_4395_);
lean_closure_set(v___f_4397_, 1, v_inv_4345_);
lean_closure_set(v___f_4397_, 2, v___x_4396_);
lean_closure_set(v___f_4397_, 3, v___x_4389_);
lean_closure_set(v___f_4397_, 4, v_arg_4376_);
v___x_4398_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4399_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4400_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4401_ = l_Lean_mkConst(v___x_4400_, v___x_4393_);
v___x_4402_ = l_Lean_mkAppB(v___x_4401_, v_arg_4382_, v_arg_4379_);
v___x_4403_ = lean_box(v___x_4388_);
v___f_4404_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4404_, 0, v___x_4399_);
lean_closure_set(v___f_4404_, 1, v___x_4402_);
lean_closure_set(v___f_4404_, 2, v___f_4397_);
lean_closure_set(v___f_4404_, 3, v_a_4395_);
lean_closure_set(v___f_4404_, 4, v_inv_4345_);
lean_closure_set(v___f_4404_, 5, v_arg_4376_);
lean_closure_set(v___f_4404_, 6, v___x_4403_);
lean_closure_set(v___f_4404_, 7, v___x_4389_);
lean_closure_set(v___f_4404_, 8, v___x_4391_);
lean_closure_set(v___f_4404_, 9, v___x_4386_);
lean_closure_set(v___f_4404_, 10, v___x_4384_);
lean_closure_set(v___f_4404_, 11, v___x_4385_);
lean_closure_set(v___f_4404_, 12, v___x_4398_);
v___x_4405_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4345_, v___f_4404_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
return v___x_4405_;
}
}
}
}
}
}
v___jp_4359_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4368_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4369_ = l_Lean_MessageData_ofExpr(v_a_4358_);
v___x_4370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
v___x_4371_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4370_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
return v___x_4371_;
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_inv_4345_);
v_a_4421_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4355_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4355_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4429_, lean_object* v_inv_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4429_, v_inv_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_);
lean_dec(v_a_4438_);
lean_dec_ref(v_a_4437_);
lean_dec(v_a_4436_);
lean_dec_ref(v_a_4435_);
lean_dec(v_a_4434_);
lean_dec_ref(v_a_4433_);
lean_dec(v_a_4432_);
lean_dec_ref(v_a_4431_);
lean_dec_ref(v_vcs_4429_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4441_, lean_object* v_msg_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4442_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4453_, lean_object* v_msg_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4453_, v_msg_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4465_, lean_object* v_name_4466_, uint8_t v_bi_4467_, lean_object* v_type_4468_, lean_object* v_k_4469_, uint8_t v_kind_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4466_, v_bi_4467_, v_type_4468_, v_k_4469_, v_kind_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4481_, lean_object* v_name_4482_, lean_object* v_bi_4483_, lean_object* v_type_4484_, lean_object* v_k_4485_, lean_object* v_kind_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
uint8_t v_bi_boxed_4496_; uint8_t v_kind_boxed_4497_; lean_object* v_res_4498_; 
v_bi_boxed_4496_ = lean_unbox(v_bi_4483_);
v_kind_boxed_4497_ = lean_unbox(v_kind_4486_);
v_res_4498_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4481_, v_name_4482_, v_bi_boxed_4496_, v_type_4484_, v_k_4485_, v_kind_boxed_4497_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4499_, lean_object* v_name_4500_, lean_object* v_type_4501_, lean_object* v_k_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v___x_4512_; 
v___x_4512_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4500_, v_type_4501_, v_k_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4513_, lean_object* v_name_4514_, lean_object* v_type_4515_, lean_object* v_k_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4513_, v_name_4514_, v_type_4515_, v_k_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4527_, size_t v_sz_4528_, size_t v_i_4529_, lean_object* v_b_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4527_, v_sz_4528_, v_i_4529_, v_b_4530_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4541_, lean_object* v_sz_4542_, lean_object* v_i_4543_, lean_object* v_b_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
size_t v_sz_boxed_4554_; size_t v_i_boxed_4555_; lean_object* v_res_4556_; 
v_sz_boxed_4554_ = lean_unbox_usize(v_sz_4542_);
lean_dec(v_sz_4542_);
v_i_boxed_4555_ = lean_unbox_usize(v_i_4543_);
lean_dec(v_i_4543_);
v_res_4556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4541_, v_sz_boxed_4554_, v_i_boxed_4555_, v_b_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec_ref(v_as_4541_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4557_, size_t v_sz_4558_, size_t v_i_4559_, lean_object* v_b_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v___x_4570_; 
v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4557_, v_sz_4558_, v_i_4559_, v_b_4560_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4571_, lean_object* v_sz_4572_, lean_object* v_i_4573_, lean_object* v_b_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
size_t v_sz_boxed_4584_; size_t v_i_boxed_4585_; lean_object* v_res_4586_; 
v_sz_boxed_4584_ = lean_unbox_usize(v_sz_4572_);
lean_dec(v_sz_4572_);
v_i_boxed_4585_ = lean_unbox_usize(v_i_4573_);
lean_dec(v_i_4573_);
v_res_4586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4571_, v_sz_boxed_4584_, v_i_boxed_4585_, v_b_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec_ref(v_as_4571_);
return v_res_4586_;
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
