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
v___x_436_ = lean_st_ref_set(v___y_417_, v___x_435_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(lean_object* v_dontRevert_739_, lean_object* v_as_740_, size_t v_i_741_, size_t v_stop_742_, lean_object* v_b_743_){
_start:
{
lean_object* v___y_745_; uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_eq(v_i_741_, v_stop_742_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_750_ = lean_array_uget_borrowed(v_as_740_, v_i_741_);
v___x_751_ = l_Lean_Expr_fvarId_x21(v___x_750_);
lean_inc_ref(v_dontRevert_739_);
v___x_752_ = lean_apply_1(v_dontRevert_739_, v___x_751_);
v___x_753_ = lean_unbox(v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_inc(v___x_750_);
v___x_754_ = lean_array_push(v_b_743_, v___x_750_);
v___y_745_ = v___x_754_;
goto v___jp_744_;
}
else
{
v___y_745_ = v_b_743_;
goto v___jp_744_;
}
}
else
{
lean_dec_ref(v_dontRevert_739_);
return v_b_743_;
}
v___jp_744_:
{
size_t v___x_746_; size_t v___x_747_; 
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_add(v_i_741_, v___x_746_);
v_i_741_ = v___x_747_;
v_b_743_ = v___y_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5___boxed(lean_object* v_dontRevert_755_, lean_object* v_as_756_, lean_object* v_i_757_, lean_object* v_stop_758_, lean_object* v_b_759_){
_start:
{
size_t v_i_boxed_760_; size_t v_stop_boxed_761_; lean_object* v_res_762_; 
v_i_boxed_760_ = lean_unbox_usize(v_i_757_);
lean_dec(v_i_757_);
v_stop_boxed_761_ = lean_unbox_usize(v_stop_758_);
lean_dec(v_stop_758_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_755_, v_as_756_, v_i_boxed_760_, v_stop_boxed_761_, v_b_759_);
lean_dec_ref(v_as_756_);
return v_res_762_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(lean_object* v_a_763_, lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
uint8_t v___x_765_; 
v___x_765_ = 0;
return v___x_765_;
}
else
{
lean_object* v_key_766_; lean_object* v_tail_767_; uint8_t v___x_768_; 
v_key_766_ = lean_ctor_get(v_x_764_, 0);
v_tail_767_ = lean_ctor_get(v_x_764_, 2);
v___x_768_ = lean_expr_eqv(v_key_766_, v_a_763_);
if (v___x_768_ == 0)
{
v_x_764_ = v_tail_767_;
goto _start;
}
else
{
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_a_770_, lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_770_, v_x_771_);
lean_dec(v_x_771_);
lean_dec_ref(v_a_770_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 0)
{
return v_x_774_;
}
else
{
lean_object* v_key_776_; lean_object* v_value_777_; lean_object* v_tail_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_801_; 
v_key_776_ = lean_ctor_get(v_x_775_, 0);
v_value_777_ = lean_ctor_get(v_x_775_, 1);
v_tail_778_ = lean_ctor_get(v_x_775_, 2);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_775_);
if (v_isSharedCheck_801_ == 0)
{
v___x_780_ = v_x_775_;
v_isShared_781_ = v_isSharedCheck_801_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_tail_778_);
lean_inc(v_value_777_);
lean_inc(v_key_776_);
lean_dec(v_x_775_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_801_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v_fold_786_; uint64_t v___x_787_; uint64_t v___x_788_; uint64_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_782_ = lean_array_get_size(v_x_774_);
v___x_783_ = l_Lean_Expr_hash(v_key_776_);
v___x_784_ = 32ULL;
v___x_785_ = lean_uint64_shift_right(v___x_783_, v___x_784_);
v_fold_786_ = lean_uint64_xor(v___x_783_, v___x_785_);
v___x_787_ = 16ULL;
v___x_788_ = lean_uint64_shift_right(v_fold_786_, v___x_787_);
v___x_789_ = lean_uint64_xor(v_fold_786_, v___x_788_);
v___x_790_ = lean_uint64_to_usize(v___x_789_);
v___x_791_ = lean_usize_of_nat(v___x_782_);
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_sub(v___x_791_, v___x_792_);
v___x_794_ = lean_usize_land(v___x_790_, v___x_793_);
v___x_795_ = lean_array_uget_borrowed(v_x_774_, v___x_794_);
lean_inc(v___x_795_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 2, v___x_795_);
v___x_797_ = v___x_780_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_key_776_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_value_777_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v___x_795_);
v___x_797_ = v_reuseFailAlloc_800_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_array_uset(v_x_774_, v___x_794_, v___x_797_);
v_x_774_ = v___x_798_;
v_x_775_ = v_tail_778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_i_802_, lean_object* v_source_803_, lean_object* v_target_804_){
_start:
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_array_get_size(v_source_803_);
v___x_806_ = lean_nat_dec_lt(v_i_802_, v___x_805_);
if (v___x_806_ == 0)
{
lean_dec_ref(v_source_803_);
lean_dec(v_i_802_);
return v_target_804_;
}
else
{
lean_object* v_es_807_; lean_object* v___x_808_; lean_object* v_source_809_; lean_object* v_target_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_es_807_ = lean_array_fget(v_source_803_, v_i_802_);
v___x_808_ = lean_box(0);
v_source_809_ = lean_array_fset(v_source_803_, v_i_802_, v___x_808_);
v_target_810_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_target_804_, v_es_807_);
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_add(v_i_802_, v___x_811_);
lean_dec(v_i_802_);
v_i_802_ = v___x_812_;
v_source_803_ = v_source_809_;
v_target_804_ = v_target_810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(lean_object* v_data_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_nbuckets_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_815_ = lean_array_get_size(v_data_814_);
v___x_816_ = lean_unsigned_to_nat(2u);
v_nbuckets_817_ = lean_nat_mul(v___x_815_, v___x_816_);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_box(0);
v___x_820_ = lean_mk_array(v_nbuckets_817_, v___x_819_);
v___x_821_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v___x_818_, v_data_814_, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(lean_object* v_m_822_, lean_object* v_a_823_, lean_object* v_b_824_){
_start:
{
lean_object* v_size_825_; lean_object* v_buckets_826_; lean_object* v___x_827_; uint64_t v___x_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v_fold_831_; uint64_t v___x_832_; uint64_t v___x_833_; uint64_t v___x_834_; size_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v_bkt_840_; uint8_t v___x_841_; 
v_size_825_ = lean_ctor_get(v_m_822_, 0);
v_buckets_826_ = lean_ctor_get(v_m_822_, 1);
v___x_827_ = lean_array_get_size(v_buckets_826_);
v___x_828_ = l_Lean_Expr_hash(v_a_823_);
v___x_829_ = 32ULL;
v___x_830_ = lean_uint64_shift_right(v___x_828_, v___x_829_);
v_fold_831_ = lean_uint64_xor(v___x_828_, v___x_830_);
v___x_832_ = 16ULL;
v___x_833_ = lean_uint64_shift_right(v_fold_831_, v___x_832_);
v___x_834_ = lean_uint64_xor(v_fold_831_, v___x_833_);
v___x_835_ = lean_uint64_to_usize(v___x_834_);
v___x_836_ = lean_usize_of_nat(v___x_827_);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_sub(v___x_836_, v___x_837_);
v___x_839_ = lean_usize_land(v___x_835_, v___x_838_);
v_bkt_840_ = lean_array_uget_borrowed(v_buckets_826_, v___x_839_);
v___x_841_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_823_, v_bkt_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_862_; 
lean_inc_ref(v_buckets_826_);
lean_inc(v_size_825_);
v_isSharedCheck_862_ = !lean_is_exclusive(v_m_822_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; lean_object* v_unused_864_; 
v_unused_863_ = lean_ctor_get(v_m_822_, 1);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_m_822_, 0);
lean_dec(v_unused_864_);
v___x_843_ = v_m_822_;
v_isShared_844_ = v_isSharedCheck_862_;
goto v_resetjp_842_;
}
else
{
lean_dec(v_m_822_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_862_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v_size_x27_846_; lean_object* v___x_847_; lean_object* v_buckets_x27_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_845_ = lean_unsigned_to_nat(1u);
v_size_x27_846_ = lean_nat_add(v_size_825_, v___x_845_);
lean_dec(v_size_825_);
lean_inc(v_bkt_840_);
v___x_847_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_847_, 0, v_a_823_);
lean_ctor_set(v___x_847_, 1, v_b_824_);
lean_ctor_set(v___x_847_, 2, v_bkt_840_);
v_buckets_x27_848_ = lean_array_uset(v_buckets_826_, v___x_839_, v___x_847_);
v___x_849_ = lean_unsigned_to_nat(4u);
v___x_850_ = lean_nat_mul(v_size_x27_846_, v___x_849_);
v___x_851_ = lean_unsigned_to_nat(3u);
v___x_852_ = lean_nat_div(v___x_850_, v___x_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_array_get_size(v_buckets_x27_848_);
v___x_854_ = lean_nat_dec_le(v___x_852_, v___x_853_);
lean_dec(v___x_852_);
if (v___x_854_ == 0)
{
lean_object* v_val_855_; lean_object* v___x_857_; 
v_val_855_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_buckets_x27_848_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v_val_855_);
lean_ctor_set(v___x_843_, 0, v_size_x27_846_);
v___x_857_ = v___x_843_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_size_x27_846_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_val_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v___x_860_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v_buckets_x27_848_);
lean_ctor_set(v___x_843_, 0, v_size_x27_846_);
v___x_860_ = v___x_843_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_size_x27_846_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_buckets_x27_848_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_dec(v_b_824_);
lean_dec_ref(v_a_823_);
return v_m_822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(lean_object* v_as_865_, size_t v_sz_866_, size_t v_i_867_, lean_object* v_b_868_){
_start:
{
uint8_t v___x_869_; 
v___x_869_ = lean_usize_dec_lt(v_i_867_, v_sz_866_);
if (v___x_869_ == 0)
{
return v_b_868_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_871_; lean_object* v_r_872_; size_t v___x_873_; size_t v___x_874_; 
v_a_870_ = lean_array_uget_borrowed(v_as_865_, v_i_867_);
v___x_871_ = lean_box(0);
lean_inc(v_a_870_);
v_r_872_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_b_868_, v_a_870_, v___x_871_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_867_, v___x_873_);
v_i_867_ = v___x_874_;
v_b_868_ = v_r_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4___boxed(lean_object* v_as_876_, lean_object* v_sz_877_, lean_object* v_i_878_, lean_object* v_b_879_){
_start:
{
size_t v_sz_boxed_880_; size_t v_i_boxed_881_; lean_object* v_res_882_; 
v_sz_boxed_880_ = lean_unbox_usize(v_sz_877_);
lean_dec(v_sz_877_);
v_i_boxed_881_ = lean_unbox_usize(v_i_878_);
lean_dec(v_i_878_);
v_res_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_as_876_, v_sz_boxed_880_, v_i_boxed_881_, v_b_879_);
lean_dec_ref(v_as_876_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(lean_object* v_m_883_, lean_object* v_l_884_){
_start:
{
size_t v_sz_885_; size_t v___x_886_; lean_object* v___x_887_; 
v_sz_885_ = lean_array_size(v_l_884_);
v___x_886_ = ((size_t)0ULL);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__4(v_l_884_, v_sz_885_, v___x_886_, v_m_883_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3___boxed(lean_object* v_m_888_, lean_object* v_l_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v_m_888_, v_l_889_);
lean_dec_ref(v_l_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(lean_object* v_as_891_, size_t v_i_892_, size_t v_stop_893_, lean_object* v_b_894_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = lean_usize_dec_eq(v_i_892_, v_stop_893_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; size_t v___x_898_; size_t v___x_899_; 
v___x_896_ = lean_array_uget_borrowed(v_as_891_, v_i_892_);
lean_inc(v___x_896_);
v___x_897_ = l_Lean_collectFVars(v_b_894_, v___x_896_);
v___x_898_ = ((size_t)1ULL);
v___x_899_ = lean_usize_add(v_i_892_, v___x_898_);
v_i_892_ = v___x_899_;
v_b_894_ = v___x_897_;
goto _start;
}
else
{
return v_b_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4___boxed(lean_object* v_as_901_, lean_object* v_i_902_, lean_object* v_stop_903_, lean_object* v_b_904_){
_start:
{
size_t v_i_boxed_905_; size_t v_stop_boxed_906_; lean_object* v_res_907_; 
v_i_boxed_905_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_stop_boxed_906_ = lean_unbox_usize(v_stop_903_);
lean_dec(v_stop_903_);
v_res_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_as_901_, v_i_boxed_905_, v_stop_boxed_906_, v_b_904_);
lean_dec_ref(v_as_901_);
return v_res_907_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_unsigned_to_nat(16u);
v___x_912_ = lean_mk_array(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__1);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(lean_object* v_dontRevert_916_, lean_object* v_a_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
uint8_t v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_923_ = 0;
v___x_924_ = 1;
lean_inc_ref(v_a_917_);
v___x_925_ = l_Lean_Meta_collectForwardDeps(v_a_917_, v___x_923_, v___x_924_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_999_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_999_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_999_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_999_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___y_932_; size_t v___y_933_; lean_object* v___y_934_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___y_947_; size_t v___y_948_; lean_object* v_fvarIds_949_; lean_object* v___y_958_; size_t v___y_959_; lean_object* v___y_960_; lean_object* v___y_963_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_box(1);
v___x_945_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_990_ = lean_array_get_size(v_a_926_);
v___x_991_ = lean_nat_dec_lt(v___x_930_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec(v_a_926_);
v___y_963_ = v___x_945_;
goto v___jp_962_;
}
else
{
uint8_t v___x_992_; 
v___x_992_ = lean_nat_dec_le(v___x_990_, v___x_990_);
if (v___x_992_ == 0)
{
if (v___x_991_ == 0)
{
lean_dec(v_a_926_);
v___y_963_ = v___x_945_;
goto v___jp_962_;
}
else
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_990_);
lean_inc_ref(v_dontRevert_916_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_916_, v_a_926_, v___x_993_, v___x_994_, v___x_945_);
lean_dec(v_a_926_);
v___y_963_ = v___x_995_;
goto v___jp_962_;
}
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_990_);
lean_inc_ref(v_dontRevert_916_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__5(v_dontRevert_916_, v_a_926_, v___x_996_, v___x_997_, v___x_945_);
lean_dec(v_a_926_);
v___y_963_ = v___x_998_;
goto v___jp_962_;
}
}
v___jp_931_:
{
size_t v_sz_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_sz_935_ = lean_array_size(v___y_934_);
lean_inc_ref(v___y_934_);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_935_, v___y_933_, v___y_934_);
v___x_937_ = l_Array_append___redArg(v___y_932_, v___x_936_);
lean_dec_ref(v___x_936_);
v___x_938_ = lean_array_get_size(v___y_934_);
lean_dec_ref(v___y_934_);
v___x_939_ = lean_nat_dec_eq(v___x_938_, v___x_930_);
if (v___x_939_ == 0)
{
lean_del_object(v___x_928_);
v_a_917_ = v___x_937_;
goto _start;
}
else
{
lean_object* v___x_942_; 
lean_dec_ref(v_dontRevert_916_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_937_);
v___x_942_ = v___x_928_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
v___jp_946_:
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_array_get_size(v_fvarIds_949_);
v___x_951_ = lean_nat_dec_lt(v___x_930_, v___x_950_);
if (v___x_951_ == 0)
{
lean_dec_ref(v_fvarIds_949_);
v___y_932_ = v___y_947_;
v___y_933_ = v___y_948_;
v___y_934_ = v___x_945_;
goto v___jp_931_;
}
else
{
uint8_t v___x_952_; 
v___x_952_ = lean_nat_dec_le(v___x_950_, v___x_950_);
if (v___x_952_ == 0)
{
if (v___x_951_ == 0)
{
lean_dec_ref(v_fvarIds_949_);
v___y_932_ = v___y_947_;
v___y_933_ = v___y_948_;
v___y_934_ = v___x_945_;
goto v___jp_931_;
}
else
{
size_t v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_usize_of_nat(v___x_950_);
lean_inc_ref(v_dontRevert_916_);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_916_, v_fvarIds_949_, v___y_948_, v___x_953_, v___x_945_);
lean_dec_ref(v_fvarIds_949_);
v___y_932_ = v___y_947_;
v___y_933_ = v___y_948_;
v___y_934_ = v___x_954_;
goto v___jp_931_;
}
}
else
{
size_t v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_usize_of_nat(v___x_950_);
lean_inc_ref(v_dontRevert_916_);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_916_, v_fvarIds_949_, v___y_948_, v___x_955_, v___x_945_);
lean_dec_ref(v_fvarIds_949_);
v___y_932_ = v___y_947_;
v___y_933_ = v___y_948_;
v___y_934_ = v___x_956_;
goto v___jp_931_;
}
}
}
v___jp_957_:
{
lean_object* v_fvarIds_961_; 
v_fvarIds_961_ = lean_ctor_get(v___y_960_, 2);
lean_inc_ref(v_fvarIds_961_);
lean_dec_ref(v___y_960_);
v___y_947_ = v___y_958_;
v___y_948_ = v___y_959_;
v_fvarIds_949_ = v_fvarIds_961_;
goto v___jp_946_;
}
v___jp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_964_ = lean_array_get_size(v___y_963_);
v___x_965_ = lean_array_get_size(v_a_917_);
lean_dec_ref(v_a_917_);
v___x_966_ = lean_nat_dec_eq(v___x_964_, v___x_965_);
if (v___x_966_ == 0)
{
size_t v_sz_967_; size_t v___x_968_; lean_object* v___x_969_; 
v_sz_967_ = lean_array_size(v___y_963_);
v___x_968_ = ((size_t)0ULL);
lean_inc_ref(v___y_963_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__0(v_sz_967_, v___x_968_, v___y_963_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = lean_array_get_size(v_a_970_);
v___x_972_ = lean_nat_dec_lt(v___x_930_, v___x_971_);
if (v___x_972_ == 0)
{
lean_dec(v_a_970_);
v___y_947_ = v___y_963_;
v___y_948_ = v___x_968_;
v_fvarIds_949_ = v___x_945_;
goto v___jp_946_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_973_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3(v___x_973_, v___y_963_);
v___x_975_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_944_);
lean_ctor_set(v___x_975_, 2, v___x_945_);
v___x_976_ = lean_nat_dec_le(v___x_971_, v___x_971_);
if (v___x_976_ == 0)
{
if (v___x_972_ == 0)
{
lean_dec_ref_known(v___x_975_, 3);
lean_dec(v_a_970_);
v___y_947_ = v___y_963_;
v___y_948_ = v___x_968_;
v_fvarIds_949_ = v___x_945_;
goto v___jp_946_;
}
else
{
size_t v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_usize_of_nat(v___x_971_);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_970_, v___x_968_, v___x_977_, v___x_975_);
lean_dec(v_a_970_);
v___y_958_ = v___y_963_;
v___y_959_ = v___x_968_;
v___y_960_ = v___x_978_;
goto v___jp_957_;
}
}
else
{
size_t v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_usize_of_nat(v___x_971_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__4(v_a_970_, v___x_968_, v___x_979_, v___x_975_);
lean_dec(v_a_970_);
v___y_958_ = v___y_963_;
v___y_959_ = v___x_968_;
v___y_960_ = v___x_980_;
goto v___jp_957_;
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v___y_963_);
lean_del_object(v___x_928_);
lean_dec_ref(v_dontRevert_916_);
v_a_981_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_969_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_969_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_object* v___x_989_; 
lean_del_object(v___x_928_);
lean_dec_ref(v_dontRevert_916_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___y_963_);
return v___x_989_;
}
}
}
}
else
{
lean_dec_ref(v_a_917_);
lean_dec_ref(v_dontRevert_916_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___boxed(lean_object* v_dontRevert_1000_, lean_object* v_a_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1000_, v_a_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1007_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1009_ = lean_box(1);
v___x_1010_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__2);
v___x_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
lean_ctor_set(v___x_1011_, 2, v___x_1008_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(lean_object* v_e_1012_, lean_object* v_dontRevert_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___y_1020_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_fvarIds_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg___closed__0));
v___x_1027_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___closed__0);
v___x_1028_ = l_Lean_collectFVars(v___x_1027_, v_e_1012_);
v_fvarIds_1029_ = lean_ctor_get(v___x_1028_, 2);
lean_inc_ref(v_fvarIds_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = lean_array_get_size(v_fvarIds_1029_);
v___x_1031_ = lean_nat_dec_lt(v___x_1025_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_dec_ref(v_fvarIds_1029_);
v___y_1020_ = v___x_1026_;
goto v___jp_1019_;
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_nat_dec_le(v___x_1030_, v___x_1030_);
if (v___x_1032_ == 0)
{
if (v___x_1031_ == 0)
{
lean_dec_ref(v_fvarIds_1029_);
v___y_1020_ = v___x_1026_;
goto v___jp_1019_;
}
else
{
size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = ((size_t)0ULL);
v___x_1034_ = lean_usize_of_nat(v___x_1030_);
lean_inc_ref(v_dontRevert_1013_);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1013_, v_fvarIds_1029_, v___x_1033_, v___x_1034_, v___x_1026_);
lean_dec_ref(v_fvarIds_1029_);
v___y_1020_ = v___x_1035_;
goto v___jp_1019_;
}
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1030_);
lean_inc_ref(v_dontRevert_1013_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__2(v_dontRevert_1013_, v_fvarIds_1029_, v___x_1036_, v___x_1037_, v___x_1026_);
lean_dec_ref(v_fvarIds_1029_);
v___y_1020_ = v___x_1038_;
goto v___jp_1019_;
}
}
v___jp_1019_:
{
size_t v_sz_1021_; size_t v___x_1022_; lean_object* v_xs_1023_; lean_object* v___x_1024_; 
v_sz_1021_ = lean_array_size(v___y_1020_);
v___x_1022_ = ((size_t)0ULL);
v_xs_1023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__1(v_sz_1021_, v___x_1022_, v___y_1020_);
v___x_1024_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1013_, v_xs_1023_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert___boxed(lean_object* v_e_1039_, lean_object* v_dontRevert_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1039_, v_dontRevert_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(lean_object* v_dontRevert_1047_, lean_object* v_inst_1048_, lean_object* v_a_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___redArg(v_dontRevert_1047_, v_a_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6___boxed(lean_object* v_dontRevert_1056_, lean_object* v_inst_1057_, lean_object* v_a_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__6(v_dontRevert_1056_, v_inst_1057_, v_a_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3(lean_object* v_00_u03b2_1065_, lean_object* v_m_1066_, lean_object* v_a_1067_, lean_object* v_b_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3___redArg(v_m_1066_, v_a_1067_, v_b_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1070_, lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___redArg(v_a_1071_, v_x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1074_, lean_object* v_a_1075_, lean_object* v_x_1076_){
_start:
{
uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_res_1077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__4(v_00_u03b2_1074_, v_a_1075_, v_x_1076_);
lean_dec(v_x_1076_);
lean_dec_ref(v_a_1075_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1079_, lean_object* v_data_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5___redArg(v_data_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1082_, lean_object* v_i_1083_, lean_object* v_source_1084_, lean_object* v_target_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9___redArg(v_i_1083_, v_source_1084_, v_target_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert_spec__3_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1088_, v_x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(lean_object* v_a_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v_i_1100_, lean_object* v_a_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_zero_1107_; uint8_t v_isZero_1108_; 
v_zero_1107_ = lean_unsigned_to_nat(0u);
v_isZero_1108_ = lean_nat_dec_eq(v_i_1100_, v_zero_1107_);
if (v_isZero_1108_ == 1)
{
lean_object* v___x_1109_; 
lean_dec(v_i_1100_);
lean_dec(v___x_1099_);
lean_dec_ref(v___x_1098_);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_a_1101_);
return v___x_1109_;
}
else
{
lean_object* v_one_1110_; lean_object* v_n_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_one_1110_ = lean_unsigned_to_nat(1u);
v_n_1111_ = lean_nat_sub(v_i_1100_, v_one_1110_);
lean_dec(v_i_1100_);
v___x_1112_ = lean_array_fget_borrowed(v_a_1097_, v_n_1111_);
lean_inc_ref(v___x_1098_);
v___x_1113_ = l_Lean_LocalContext_getFVar_x21(v___x_1098_, v___x_1112_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_userName_1114_; lean_object* v_type_1115_; uint8_t v_bi_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_userName_1114_ = lean_ctor_get(v___x_1113_, 2);
lean_inc(v_userName_1114_);
v_type_1115_ = lean_ctor_get(v___x_1113_, 3);
lean_inc_ref(v_type_1115_);
v_bi_1116_ = lean_ctor_get_uint8(v___x_1113_, sizeof(void*)*4);
lean_dec_ref_known(v___x_1113_, 4);
v___x_1117_ = l_Lean_Expr_headBeta(v_type_1115_);
v___x_1118_ = lean_expr_abstract_range(v___x_1117_, v_n_1111_, v_a_1097_);
lean_dec_ref(v___x_1117_);
lean_inc_ref(v___x_1118_);
v___x_1119_ = l_Lean_Meta_getLevel(v___x_1118_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1122_ = lean_box(0);
lean_inc_n(v___x_1099_, 2);
v___x_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1099_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1120_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_mkConst(v___x_1121_, v___x_1124_);
v___x_1126_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1099_);
lean_inc_ref(v___x_1118_);
v___x_1127_ = l_Lean_mkLambda(v_userName_1114_, v_bi_1116_, v___x_1118_, v_a_1101_);
v___x_1128_ = l_Lean_mkApp3(v___x_1125_, v___x_1118_, v___x_1126_, v___x_1127_);
v_i_1100_ = v_n_1111_;
v_a_1101_ = v___x_1128_;
goto _start;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___x_1118_);
lean_dec(v_userName_1114_);
lean_dec(v_n_1111_);
lean_dec_ref(v_a_1101_);
lean_dec(v___x_1099_);
lean_dec_ref(v___x_1098_);
v_a_1130_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1119_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1119_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
uint8_t v_nondep_1138_; 
v_nondep_1138_ = lean_ctor_get_uint8(v___x_1113_, sizeof(void*)*5);
if (v_nondep_1138_ == 0)
{
lean_object* v_userName_1139_; lean_object* v_type_1140_; lean_object* v_value_1141_; uint8_t v___x_1142_; 
v_userName_1139_ = lean_ctor_get(v___x_1113_, 2);
lean_inc(v_userName_1139_);
v_type_1140_ = lean_ctor_get(v___x_1113_, 3);
lean_inc_ref(v_type_1140_);
v_value_1141_ = lean_ctor_get(v___x_1113_, 4);
lean_inc_ref(v_value_1141_);
lean_dec_ref_known(v___x_1113_, 5);
v___x_1142_ = lean_expr_has_loose_bvar(v_a_1101_, v_zero_1107_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref(v_value_1141_);
lean_dec_ref(v_type_1140_);
lean_dec(v_userName_1139_);
v___x_1143_ = lean_expr_lower_loose_bvars(v_a_1101_, v_one_1110_, v_one_1110_);
lean_dec_ref(v_a_1101_);
v_i_1100_ = v_n_1111_;
v_a_1101_ = v___x_1143_;
goto _start;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = l_Lean_Expr_headBeta(v_type_1140_);
v___x_1146_ = lean_expr_abstract_range(v___x_1145_, v_n_1111_, v_a_1097_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = lean_expr_abstract_range(v_value_1141_, v_n_1111_, v_a_1097_);
lean_dec_ref(v_value_1141_);
v___x_1148_ = l_Lean_Expr_letE___override(v_userName_1139_, v___x_1146_, v___x_1147_, v_a_1101_, v_nondep_1138_);
v_i_1100_ = v_n_1111_;
v_a_1101_ = v___x_1148_;
goto _start;
}
}
else
{
lean_object* v_userName_1150_; lean_object* v_type_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_userName_1150_ = lean_ctor_get(v___x_1113_, 2);
lean_inc(v_userName_1150_);
v_type_1151_ = lean_ctor_get(v___x_1113_, 3);
lean_inc_ref(v_type_1151_);
lean_dec_ref_known(v___x_1113_, 5);
v___x_1152_ = l_Lean_Expr_headBeta(v_type_1151_);
v___x_1153_ = lean_expr_abstract_range(v___x_1152_, v_n_1111_, v_a_1097_);
lean_dec_ref(v___x_1152_);
lean_inc_ref(v___x_1153_);
v___x_1154_ = l_Lean_Meta_getLevel(v___x_1153_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v___x_1156_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_1157_ = lean_box(0);
lean_inc_n(v___x_1099_, 2);
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1099_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_a_1155_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_mkConst(v___x_1156_, v___x_1159_);
v___x_1161_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v___x_1099_);
v___x_1162_ = 0;
lean_inc_ref(v___x_1153_);
v___x_1163_ = l_Lean_mkLambda(v_userName_1150_, v___x_1162_, v___x_1153_, v_a_1101_);
v___x_1164_ = l_Lean_mkApp3(v___x_1160_, v___x_1153_, v___x_1161_, v___x_1163_);
v_i_1100_ = v_n_1111_;
v_a_1101_ = v___x_1164_;
goto _start;
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v___x_1153_);
lean_dec(v_userName_1150_);
lean_dec(v_n_1111_);
lean_dec_ref(v_a_1101_);
lean_dec(v___x_1099_);
lean_dec_ref(v___x_1098_);
v_a_1166_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1154_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1154_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___boxed(lean_object* v_a_1174_, lean_object* v___x_1175_, lean_object* v___x_1176_, lean_object* v_i_1177_, lean_object* v_a_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1174_, v___x_1175_, v___x_1176_, v_i_1177_, v_a_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec_ref(v_a_1174_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(lean_object* v_e_1189_, lean_object* v_dontRevert_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; 
lean_inc_ref(v_e_1189_);
v___x_1196_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectFVarsToRevert(v_e_1189_, v_dontRevert_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v_lctx_1198_; lean_object* v___x_1199_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v_lctx_1198_ = lean_ctor_get(v_a_1191_, 2);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc_ref(v_a_1191_);
lean_inc_ref(v_e_1189_);
v___x_1199_ = lean_infer_type(v_e_1189_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1222_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1222_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1222_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = l_Lean_Expr_cleanupAnnotations(v_a_1200_);
v___x_1205_ = l_Lean_Expr_isApp(v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1207_; 
lean_dec_ref(v___x_1204_);
lean_dec(v_a_1197_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v_e_1189_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_e_1189_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1209_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1204_);
v___x_1210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___closed__0));
v___x_1211_ = l_Lean_Expr_isConstOf(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v___x_1209_);
lean_dec(v_a_1197_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v_e_1189_);
v___x_1213_ = v___x_1202_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_e_1189_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1202_);
v___x_1215_ = lean_box(0);
v___x_1216_ = l_Lean_Expr_constLevels_x21(v___x_1209_);
lean_dec_ref(v___x_1209_);
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = l_List_get_x21Internal___redArg(v___x_1215_, v___x_1216_, v___x_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_array_get_size(v_a_1197_);
v___x_1220_ = lean_expr_abstract(v_e_1189_, v_a_1197_);
lean_dec_ref(v_e_1189_);
lean_inc_ref(v_lctx_1198_);
v___x_1221_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1197_, v_lctx_1198_, v___x_1218_, v___x_1219_, v___x_1220_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1197_);
return v___x_1221_;
}
}
}
}
else
{
lean_dec(v_a_1197_);
lean_dec_ref(v_e_1189_);
return v___x_1199_;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_e_1189_);
v_a_1223_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1196_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1196_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed(lean_object* v_e_1231_, lean_object* v_dontRevert_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept(v_e_1231_, v_dontRevert_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(lean_object* v_a_1239_, lean_object* v___x_1240_, lean_object* v___x_1241_, lean_object* v_n_1242_, lean_object* v_i_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg(v_a_1239_, v___x_1240_, v___x_1241_, v_i_1243_, v_a_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___boxed(lean_object* v_a_1252_, lean_object* v___x_1253_, lean_object* v___x_1254_, lean_object* v_n_1255_, lean_object* v_i_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0(v_a_1252_, v___x_1253_, v___x_1254_, v_n_1255_, v_i_1256_, v_a_1257_, v_a_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_n_1255_);
lean_dec_ref(v_a_1252_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(lean_object* v_lvl_1271_, lean_object* v_lhs_1272_, lean_object* v_rhs_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_1275_ = lean_box(0);
lean_inc(v_lvl_1271_);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_lvl_1271_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l_Lean_mkConst(v___x_1274_, v___x_1276_);
v___x_1278_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1271_);
v___x_1279_ = l_Lean_mkApp3(v___x_1277_, v___x_1278_, v_lhs_1272_, v_rhs_1273_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(lean_object* v_lvl_1286_, lean_object* v_lhs_1287_, lean_object* v_rhs_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_1290_ = lean_box(0);
lean_inc(v_lvl_1286_);
v___x_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_lvl_1286_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = l_Lean_mkConst(v___x_1289_, v___x_1291_);
v___x_1293_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_lvl_1286_);
v___x_1294_ = l_Lean_mkApp3(v___x_1292_, v___x_1293_, v_lhs_1287_, v_rhs_1288_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(lean_object* v_p_1295_){
_start:
{
lean_object* v_lvl_1296_; lean_object* v_cursorPred_1297_; lean_object* v_letMutsPred_1298_; lean_object* v___x_1299_; 
v_lvl_1296_ = lean_ctor_get(v_p_1295_, 0);
lean_inc(v_lvl_1296_);
v_cursorPred_1297_ = lean_ctor_get(v_p_1295_, 1);
lean_inc_ref(v_cursorPred_1297_);
v_letMutsPred_1298_ = lean_ctor_get(v_p_1295_, 2);
lean_inc_ref(v_letMutsPred_1298_);
lean_dec_ref(v_p_1295_);
v___x_1299_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v_lvl_1296_, v_cursorPred_1297_, v_letMutsPred_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(lean_object* v_x_1300_){
_start:
{
switch(lean_obj_tag(v_x_1300_))
{
case 0:
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_unsigned_to_nat(0u);
return v___x_1301_;
}
case 1:
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_unsigned_to_nat(1u);
return v___x_1302_;
}
case 2:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_unsigned_to_nat(2u);
return v___x_1303_;
}
default: 
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_unsigned_to_nat(3u);
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx___boxed(lean_object* v_x_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorIdx(v_x_1305_);
lean_dec(v_x_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(lean_object* v_t_1307_, lean_object* v_k_1308_){
_start:
{
if (lean_obj_tag(v_t_1307_) == 3)
{
lean_object* v_e_1309_; lean_object* v___x_1310_; 
v_e_1309_ = lean_ctor_get(v_t_1307_, 0);
lean_inc_ref(v_e_1309_);
lean_dec_ref_known(v_t_1307_, 1);
v___x_1310_ = lean_apply_1(v_k_1308_, v_e_1309_);
return v___x_1310_;
}
else
{
lean_dec(v_t_1307_);
return v_k_1308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(lean_object* v_motive_1311_, lean_object* v_ctorIdx_1312_, lean_object* v_t_1313_, lean_object* v_h_1314_, lean_object* v_k_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1313_, v_k_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___boxed(lean_object* v_motive_1317_, lean_object* v_ctorIdx_1318_, lean_object* v_t_1319_, lean_object* v_h_1320_, lean_object* v_k_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim(v_motive_1317_, v_ctorIdx_1318_, v_t_1319_, v_h_1320_, v_k_1321_);
lean_dec(v_ctorIdx_1318_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim___redArg(lean_object* v_t_1323_, lean_object* v_punit_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1323_, v_punit_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_punit_elim(lean_object* v_motive_1326_, lean_object* v_t_1327_, lean_object* v_h_1328_, lean_object* v_punit_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1327_, v_punit_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim___redArg(lean_object* v_t_1331_, lean_object* v_false_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1331_, v_false_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_false_elim(lean_object* v_motive_1334_, lean_object* v_t_1335_, lean_object* v_h_1336_, lean_object* v_false_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1335_, v_false_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim___redArg(lean_object* v_t_1339_, lean_object* v_true_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1339_, v_true_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_true_elim(lean_object* v_motive_1342_, lean_object* v_t_1343_, lean_object* v_h_1344_, lean_object* v_true_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1343_, v_true_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim___redArg(lean_object* v_t_1347_, lean_object* v_other_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1347_, v_other_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_other_elim(lean_object* v_motive_1350_, lean_object* v_t_1351_, lean_object* v_h_1352_, lean_object* v_other_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_ExceptCondsDefault_ctorElim___redArg(v_t_1351_, v_other_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(lean_object* v_a_1355_){
_start:
{
lean_object* v_snd_1357_; lean_object* v_fst_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1397_; 
v_snd_1357_ = lean_ctor_get(v_a_1355_, 1);
v_fst_1358_ = lean_ctor_get(v_a_1355_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_a_1355_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1360_ = v_a_1355_;
v_isShared_1361_ = v_isSharedCheck_1397_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_snd_1357_);
lean_inc(v_fst_1358_);
lean_dec(v_a_1355_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1397_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_fst_1362_; lean_object* v_snd_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1396_; 
v_fst_1362_ = lean_ctor_get(v_snd_1357_, 0);
v_snd_1363_ = lean_ctor_get(v_snd_1357_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_snd_1357_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1365_ = v_snd_1357_;
v_isShared_1366_ = v_isSharedCheck_1396_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snd_1363_);
lean_inc(v_fst_1362_);
lean_dec(v_snd_1357_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1396_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_1368_ = lean_unsigned_to_nat(4u);
v___x_1369_ = l_Lean_Expr_isAppOfArity(v_fst_1362_, v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1371_; 
if (v_isShared_1366_ == 0)
{
v___x_1371_ = v___x_1365_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_fst_1362_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_snd_1363_);
v___x_1371_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1371_);
v___x_1373_ = v___x_1360_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_fst_1358_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1377_ = lean_unsigned_to_nat(3u);
v___x_1378_ = lean_unsigned_to_nat(2u);
v___x_1379_ = l_Lean_Expr_getAppNumArgs(v_fst_1362_);
v___x_1380_ = lean_nat_sub(v___x_1379_, v___x_1378_);
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_sub(v___x_1380_, v___x_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = l_Lean_Expr_getRevArg_x21(v_fst_1362_, v___x_1382_);
v___x_1384_ = lean_array_push(v_snd_1363_, v___x_1383_);
v___x_1385_ = lean_nat_add(v_fst_1358_, v___x_1381_);
lean_dec(v_fst_1358_);
v___x_1386_ = lean_nat_sub(v___x_1379_, v___x_1377_);
lean_dec(v___x_1379_);
v___x_1387_ = lean_nat_sub(v___x_1386_, v___x_1381_);
lean_dec(v___x_1386_);
v___x_1388_ = l_Lean_Expr_getRevArg_x21(v_fst_1362_, v___x_1387_);
lean_dec(v_fst_1362_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1384_);
lean_ctor_set(v___x_1365_, 0, v___x_1388_);
v___x_1390_ = v___x_1365_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1384_);
v___x_1390_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1392_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1390_);
lean_ctor_set(v___x_1360_, 0, v___x_1385_);
v___x_1392_ = v___x_1360_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v_a_1355_ = v___x_1392_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg___boxed(lean_object* v_a_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(lean_object* v_fst_1401_, lean_object* v_p_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_inc(v_fst_1401_);
v___x_1403_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_1401_);
v___x_1404_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_1401_, v___x_1403_, v_p_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(lean_object* v_letMutsTuple_1405_, lean_object* v___x_1406_, uint8_t v___x_1407_, lean_object* v_fvarId_1408_){
_start:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = l_Lean_Expr_fvarId_x21(v_letMutsTuple_1405_);
v___x_1410_ = l_Lean_instBEqFVarId_beq(v_fvarId_1408_, v___x_1409_);
lean_dec(v___x_1409_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = l_Lean_LocalContext_contains(v___x_1406_, v_fvarId_1408_);
return v___x_1411_;
}
else
{
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed(lean_object* v_letMutsTuple_1412_, lean_object* v___x_1413_, lean_object* v___x_1414_, lean_object* v_fvarId_1415_){
_start:
{
uint8_t v___x_11385__boxed_1416_; uint8_t v_res_1417_; lean_object* v_r_1418_; 
v___x_11385__boxed_1416_ = lean_unbox(v___x_1414_);
v_res_1417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0(v_letMutsTuple_1412_, v___x_1413_, v___x_11385__boxed_1416_, v_fvarId_1415_);
lean_dec(v_fvarId_1415_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v_letMutsTuple_1412_);
v_r_1418_ = lean_box(v_res_1417_);
return v_r_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(lean_object* v_inv_1438_, lean_object* v___x_1439_, lean_object* v_xs_1440_, lean_object* v_letMuts_1441_, lean_object* v_as_1442_, size_t v_sz_1443_, size_t v_i_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_a_1452_; uint8_t v___x_1456_; 
v___x_1456_ = lean_usize_dec_lt(v_i_1444_, v_sz_1443_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_b_1445_);
return v___x_1457_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_array_uget_borrowed(v_as_1442_, v_i_1444_);
lean_inc(v_a_1458_);
v___x_1459_ = l_Lean_MVarId_getType(v_a_1458_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_snd_1460_; lean_object* v_a_1461_; lean_object* v_fst_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1804_; 
v_snd_1460_ = lean_ctor_get(v_b_1445_, 1);
lean_inc(v_snd_1460_);
v_a_1461_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1459_, 1);
v_fst_1462_ = lean_ctor_get(v_b_1445_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_b_1445_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v_b_1445_, 1);
lean_dec(v_unused_1805_);
v___x_1464_ = v_b_1445_;
v_isShared_1465_ = v_isSharedCheck_1804_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_fst_1462_);
lean_dec(v_b_1445_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1804_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_fst_1466_; lean_object* v_snd_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1803_; 
v_fst_1466_ = lean_ctor_get(v_snd_1460_, 0);
v_snd_1467_ = lean_ctor_get(v_snd_1460_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_snd_1460_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1469_ = v_snd_1460_;
v_isShared_1470_ = v_isSharedCheck_1803_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_snd_1467_);
lean_inc(v_fst_1466_);
lean_dec(v_snd_1460_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1803_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; uint8_t v___y_1485_; lean_object* v___y_1585_; lean_object* v_prefixPoint_x3f_1586_; lean_object* v_suffixPoint_x3f_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; uint8_t v___y_1626_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v_prefixPoint_x3f_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v_a_1713_; lean_object* v_a_1718_; lean_object* v___x_1791_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse___closed__5));
v___x_1473_ = lean_box(0);
v___x_1791_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__1___redArg(v_a_1461_, v___y_1447_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1793_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1793_ = l_Lean_Expr_consumeMData(v_a_1792_);
lean_dec(v_a_1792_);
v_a_1718_ = v___x_1793_;
goto v___jp_1717_;
}
else
{
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1794_; 
v_a_1794_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1791_, 1);
v_a_1718_ = v_a_1794_;
goto v___jp_1717_;
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_del_object(v___x_1469_);
lean_dec(v_snd_1467_);
lean_dec(v_fst_1466_);
lean_del_object(v___x_1464_);
lean_dec(v_fst_1462_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1795_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1791_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1791_);
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
v___jp_1474_:
{
if (v___y_1485_ == 0)
{
lean_object* v___x_1487_; 
lean_dec_ref(v___y_1478_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___y_1480_);
v___x_1487_ = v___x_1469_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___y_1480_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_snd_1467_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v___x_1487_);
lean_ctor_set(v___x_1464_, 0, v___y_1475_);
v___x_1489_ = v___x_1464_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___y_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
v_a_1452_ = v___x_1489_;
goto v___jp_1451_;
}
}
}
else
{
lean_object* v___x_1493_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1472_);
lean_ctor_set(v___x_1469_, 0, v___y_1478_);
v___x_1493_ = v___x_1469_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___y_1478_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1472_);
v___x_1493_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v___x_1493_);
lean_ctor_set(v___x_1464_, 0, v___x_1471_);
v___x_1495_ = v___x_1464_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v___x_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1572_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v_snd_1498_ = lean_ctor_get(v_a_1497_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_a_1497_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v_a_1497_, 0);
lean_dec(v_unused_1573_);
v___x_1500_ = v_a_1497_;
v_isShared_1501_ = v_isSharedCheck_1572_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_dec(v_a_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1572_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_fst_1502_; lean_object* v_snd_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1571_; 
v_fst_1502_ = lean_ctor_get(v_snd_1498_, 0);
v_snd_1503_ = lean_ctor_get(v_snd_1498_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_snd_1498_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1505_ = v_snd_1498_;
v_isShared_1506_ = v_isSharedCheck_1571_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_snd_1503_);
lean_inc(v_fst_1502_);
lean_dec(v_snd_1498_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1571_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_points_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_points_1507_ = lean_ctor_get(v_snd_1467_, 0);
v___x_1508_ = lean_array_get_size(v_points_1507_);
v___x_1509_ = lean_array_get_size(v_snd_1503_);
v___x_1510_ = lean_nat_dec_lt(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1512_; 
lean_dec(v_snd_1503_);
lean_dec(v_fst_1502_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v_snd_1467_);
lean_ctor_set(v___x_1505_, 0, v___y_1480_);
v___x_1512_ = v___x_1505_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___y_1480_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_snd_1467_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1512_);
lean_ctor_set(v___x_1500_, 0, v___y_1475_);
v___x_1514_ = v___x_1500_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___y_1475_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
v_a_1452_ = v___x_1514_;
goto v___jp_1451_;
}
}
}
else
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1568_; 
v_isSharedCheck_1568_ = !lean_is_exclusive(v_snd_1467_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1569_ = lean_ctor_get(v_snd_1467_, 1);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_snd_1467_, 0);
lean_dec(v_unused_1570_);
v___x_1518_ = v_snd_1467_;
v_isShared_1519_ = v_isSharedCheck_1568_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v_snd_1467_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1568_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__2));
v___x_1521_ = l_Lean_Expr_isConstOf(v_fst_1502_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__3));
lean_inc_ref(v___y_1484_);
lean_inc_ref(v___y_1476_);
lean_inc_ref(v___y_1479_);
v___x_1523_ = l_Lean_Name_mkStr4(v___y_1479_, v___y_1476_, v___y_1484_, v___x_1522_);
v___x_1524_ = lean_unsigned_to_nat(1u);
v___x_1525_ = l_Lean_Expr_isAppOfArity(v_fst_1502_, v___x_1523_, v___x_1524_);
lean_dec(v___x_1523_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
lean_inc_ref(v___y_1484_);
lean_inc_ref(v___y_1476_);
lean_inc_ref(v___y_1479_);
v___x_1527_ = l_Lean_Name_mkStr4(v___y_1479_, v___y_1476_, v___y_1484_, v___x_1526_);
v___x_1528_ = l_Lean_Expr_isAppOfArity(v_fst_1502_, v___x_1527_, v___x_1524_);
lean_dec(v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_fst_1502_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v___x_1529_);
lean_ctor_set(v___x_1518_, 0, v_snd_1503_);
v___x_1531_ = v___x_1518_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_snd_1503_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v___x_1531_);
lean_ctor_set(v___x_1505_, 0, v___y_1480_);
v___x_1533_ = v___x_1505_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___y_1480_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1533_);
lean_ctor_set(v___x_1500_, 0, v___y_1475_);
v___x_1535_ = v___x_1500_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___y_1475_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
v_a_1452_ = v___x_1535_;
goto v___jp_1451_;
}
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_dec(v_fst_1502_);
v___x_1539_ = lean_box(2);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v___x_1539_);
lean_ctor_set(v___x_1518_, 0, v_snd_1503_);
v___x_1541_ = v___x_1518_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_snd_1503_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v___x_1541_);
lean_ctor_set(v___x_1505_, 0, v___y_1480_);
v___x_1543_ = v___x_1505_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___y_1480_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1543_);
lean_ctor_set(v___x_1500_, 0, v___y_1475_);
v___x_1545_ = v___x_1500_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___y_1475_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v_a_1452_ = v___x_1545_;
goto v___jp_1451_;
}
}
}
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec(v_fst_1502_);
v___x_1549_ = lean_box(1);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v___x_1549_);
lean_ctor_set(v___x_1518_, 0, v_snd_1503_);
v___x_1551_ = v___x_1518_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_snd_1503_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v___x_1551_);
lean_ctor_set(v___x_1505_, 0, v___y_1480_);
v___x_1553_ = v___x_1505_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___y_1480_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1553_);
lean_ctor_set(v___x_1500_, 0, v___y_1475_);
v___x_1555_ = v___x_1500_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___y_1475_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
v_a_1452_ = v___x_1555_;
goto v___jp_1451_;
}
}
}
}
}
else
{
lean_object* v___x_1560_; 
lean_dec(v_fst_1502_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v___x_1473_);
lean_ctor_set(v___x_1518_, 0, v_snd_1503_);
v___x_1560_ = v___x_1518_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_snd_1503_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1473_);
v___x_1560_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v___x_1560_);
lean_ctor_set(v___x_1505_, 0, v___y_1480_);
v___x_1562_ = v___x_1505_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___y_1480_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1564_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1562_);
lean_ctor_set(v___x_1500_, 0, v___y_1475_);
v___x_1564_ = v___x_1500_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___y_1475_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
v_a_1452_ = v___x_1564_;
goto v___jp_1451_;
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
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v___y_1480_);
lean_dec(v___y_1475_);
lean_dec(v_snd_1467_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1574_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1496_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1496_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
}
v___jp_1584_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_1593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_1594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_1595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__6));
v___x_1596_ = lean_unsigned_to_nat(3u);
v___x_1597_ = l_Lean_Expr_isAppOfArity(v___y_1585_, v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v___y_1585_);
lean_del_object(v___x_1469_);
lean_del_object(v___x_1464_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_suffixPoint_x3f_1587_);
lean_ctor_set(v___x_1598_, 1, v_snd_1467_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_prefixPoint_x3f_1586_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v_a_1452_ = v___x_1599_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1600_ = l_Lean_Expr_appFn_x21(v___y_1585_);
v___x_1601_ = l_Lean_Expr_appArg_x21(v___x_1600_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = l_Lean_Expr_appArg_x21(v___y_1585_);
lean_dec_ref(v___y_1585_);
v___x_1603_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__0___redArg___closed__1));
v___x_1604_ = l_Lean_Expr_isAppOfArity(v___x_1601_, v___x_1603_, v___x_1596_);
if (v___x_1604_ == 0)
{
lean_dec_ref(v___x_1601_);
v___y_1475_ = v_prefixPoint_x3f_1586_;
v___y_1476_ = v___x_1593_;
v___y_1477_ = v___y_1589_;
v___y_1478_ = v___x_1602_;
v___y_1479_ = v___x_1592_;
v___y_1480_ = v_suffixPoint_x3f_1587_;
v___y_1481_ = v___y_1591_;
v___y_1482_ = v___y_1590_;
v___y_1483_ = v___y_1588_;
v___y_1484_ = v___x_1594_;
v___y_1485_ = v___x_1604_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1605_ = lean_unsigned_to_nat(2u);
v___x_1606_ = l_Lean_Expr_getAppNumArgs(v___x_1601_);
v___x_1607_ = lean_nat_sub(v___x_1606_, v___x_1605_);
lean_dec(v___x_1606_);
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_sub(v___x_1607_, v___x_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = l_Lean_Expr_getRevArg_x21(v___x_1601_, v___x_1609_);
lean_dec_ref(v___x_1601_);
lean_inc(v_inv_1438_);
v___x_1611_ = l_Lean_mkMVar(v_inv_1438_);
v___x_1612_ = lean_expr_eqv(v___x_1610_, v___x_1611_);
lean_dec_ref(v___x_1611_);
lean_dec_ref(v___x_1610_);
v___y_1475_ = v_prefixPoint_x3f_1586_;
v___y_1476_ = v___x_1593_;
v___y_1477_ = v___y_1589_;
v___y_1478_ = v___x_1602_;
v___y_1479_ = v___x_1592_;
v___y_1480_ = v_suffixPoint_x3f_1587_;
v___y_1481_ = v___y_1591_;
v___y_1482_ = v___y_1590_;
v___y_1483_ = v___y_1588_;
v___y_1484_ = v___x_1594_;
v___y_1485_ = v___x_1612_;
goto v___jp_1474_;
}
}
}
v___jp_1613_:
{
if (v___y_1626_ == 0)
{
lean_dec_ref(v___y_1625_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
v___y_1585_ = v___y_1624_;
v_prefixPoint_x3f_1586_ = v___y_1618_;
v_suffixPoint_x3f_1587_ = v_fst_1466_;
v___y_1588_ = v___y_1617_;
v___y_1589_ = v___y_1616_;
v___y_1590_ = v___y_1623_;
v___y_1591_ = v___y_1622_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__8));
lean_inc_ref(v_xs_1440_);
v___x_1628_ = l_Lean_Meta_mkProjection(v_xs_1440_, v___x_1627_, v___y_1617_, v___y_1616_, v___y_1623_, v___y_1622_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = l_Lean_Meta_mkEq(v_a_1629_, v___y_1619_, v___y_1617_, v___y_1616_, v___y_1623_, v___y_1622_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept___boxed), 7, 2);
lean_closure_set(v___x_1632_, 0, v___y_1614_);
lean_closure_set(v___x_1632_, 1, v___y_1621_);
lean_inc(v_a_1458_);
v___x_1633_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1458_, v___x_1632_, v___y_1617_, v___y_1616_, v___y_1623_, v___y_1622_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = l_Lean_Expr_replaceFVar(v_a_1634_, v___y_1625_, v_letMuts_1441_);
lean_dec(v_a_1634_);
if (lean_obj_tag(v_fst_1466_) == 1)
{
lean_object* v_val_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_a_1631_);
lean_dec_ref(v___y_1620_);
v_val_1636_ = lean_ctor_get(v_fst_1466_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_fst_1466_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1638_ = v_fst_1466_;
v_isShared_1639_ = v_isSharedCheck_1654_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_val_1636_);
lean_dec(v_fst_1466_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1654_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_lvl_1640_; lean_object* v_cursorPred_1641_; lean_object* v_letMutsPred_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1653_; 
v_lvl_1640_ = lean_ctor_get(v_val_1636_, 0);
v_cursorPred_1641_ = lean_ctor_get(v_val_1636_, 1);
v_letMutsPred_1642_ = lean_ctor_get(v_val_1636_, 2);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_val_1636_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1644_ = v_val_1636_;
v_isShared_1645_ = v_isSharedCheck_1653_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_letMutsPred_1642_);
lean_inc(v_cursorPred_1641_);
lean_inc(v_lvl_1640_);
lean_dec(v_val_1636_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1653_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd(v___y_1615_, v_letMutsPred_1642_, v___x_1635_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 2, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_lvl_1640_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_cursorPred_1641_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1648_);
v___x_1650_ = v___x_1638_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
v___y_1585_ = v___y_1624_;
v_prefixPoint_x3f_1586_ = v___y_1618_;
v_suffixPoint_x3f_1587_ = v___x_1650_;
v___y_1588_ = v___y_1617_;
v___y_1589_ = v___y_1616_;
v___y_1590_ = v___y_1623_;
v___y_1591_ = v___y_1622_;
goto v___jp_1584_;
}
}
}
}
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v_fst_1466_);
v___x_1655_ = lean_apply_1(v___y_1620_, v_a_1631_);
v___x_1656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1656_, 0, v___y_1615_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
lean_ctor_set(v___x_1656_, 2, v___x_1635_);
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
v___y_1585_ = v___y_1624_;
v_prefixPoint_x3f_1586_ = v___y_1618_;
v_suffixPoint_x3f_1587_ = v___x_1657_;
v___y_1588_ = v___y_1617_;
v___y_1589_ = v___y_1616_;
v___y_1590_ = v___y_1623_;
v___y_1591_ = v___y_1622_;
goto v___jp_1584_;
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_a_1631_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1618_);
lean_dec(v___y_1615_);
lean_del_object(v___x_1469_);
lean_dec(v_snd_1467_);
lean_dec(v_fst_1466_);
lean_del_object(v___x_1464_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1658_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1633_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1633_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1618_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_del_object(v___x_1469_);
lean_dec(v_snd_1467_);
lean_dec(v_fst_1466_);
lean_del_object(v___x_1464_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1666_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1630_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1630_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_del_object(v___x_1469_);
lean_dec(v_snd_1467_);
lean_dec(v_fst_1466_);
lean_del_object(v___x_1464_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1674_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1628_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1628_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
v___jp_1682_:
{
lean_object* v___x_1693_; 
lean_inc(v_inv_1438_);
v___x_1693_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v___y_1683_, v_inv_1438_);
lean_dec_ref(v___y_1683_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_invariantUse_1694_; lean_object* v_conditionIdx_1695_; lean_object* v_cursorSuffix_1696_; lean_object* v_letMutsTuple_1697_; uint8_t v___x_1698_; 
v_invariantUse_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc_ref(v_invariantUse_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v_conditionIdx_1695_ = lean_ctor_get(v_invariantUse_1694_, 0);
lean_inc(v_conditionIdx_1695_);
v_cursorSuffix_1696_ = lean_ctor_get(v_invariantUse_1694_, 2);
lean_inc_ref(v_cursorSuffix_1696_);
v_letMutsTuple_1697_ = lean_ctor_get(v_invariantUse_1694_, 4);
lean_inc_ref(v_letMutsTuple_1697_);
lean_dec_ref(v_invariantUse_1694_);
v___x_1698_ = lean_nat_dec_eq(v_conditionIdx_1695_, v___x_1471_);
lean_dec(v_conditionIdx_1695_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec_ref(v_letMutsTuple_1697_);
lean_dec_ref(v_cursorSuffix_1696_);
lean_dec_ref(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_del_object(v___x_1469_);
lean_del_object(v___x_1464_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_fst_1466_);
lean_ctor_set(v___x_1699_, 1, v_snd_1467_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_prefixPoint_x3f_1688_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v_a_1452_ = v___x_1700_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1701_ = lean_box(v___x_1698_);
lean_inc_ref(v___x_1439_);
lean_inc_ref(v_letMutsTuple_1697_);
v___f_1702_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1702_, 0, v_letMutsTuple_1697_);
lean_closure_set(v___f_1702_, 1, v___x_1439_);
lean_closure_set(v___f_1702_, 2, v___x_1701_);
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_1704_ = l_Lean_Expr_isAppOf(v_cursorSuffix_1696_, v___x_1703_);
if (v___x_1704_ == 0)
{
v___y_1614_ = v___y_1684_;
v___y_1615_ = v___y_1685_;
v___y_1616_ = v___y_1690_;
v___y_1617_ = v___y_1689_;
v___y_1618_ = v_prefixPoint_x3f_1688_;
v___y_1619_ = v_cursorSuffix_1696_;
v___y_1620_ = v___y_1687_;
v___y_1621_ = v___f_1702_;
v___y_1622_ = v___y_1692_;
v___y_1623_ = v___y_1691_;
v___y_1624_ = v___y_1686_;
v___y_1625_ = v_letMutsTuple_1697_;
v___y_1626_ = v___x_1704_;
goto v___jp_1613_;
}
else
{
uint8_t v___x_1705_; 
v___x_1705_ = l_Lean_Expr_isFVar(v_letMutsTuple_1697_);
v___y_1614_ = v___y_1684_;
v___y_1615_ = v___y_1685_;
v___y_1616_ = v___y_1690_;
v___y_1617_ = v___y_1689_;
v___y_1618_ = v_prefixPoint_x3f_1688_;
v___y_1619_ = v_cursorSuffix_1696_;
v___y_1620_ = v___y_1687_;
v___y_1621_ = v___f_1702_;
v___y_1622_ = v___y_1692_;
v___y_1623_ = v___y_1691_;
v___y_1624_ = v___y_1686_;
v___y_1625_ = v_letMutsTuple_1697_;
v___y_1626_ = v___x_1705_;
goto v___jp_1613_;
}
}
}
else
{
lean_dec(v___x_1693_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
v___y_1585_ = v___y_1686_;
v_prefixPoint_x3f_1586_ = v_prefixPoint_x3f_1688_;
v_suffixPoint_x3f_1587_ = v_fst_1466_;
v___y_1588_ = v___y_1689_;
v___y_1589_ = v___y_1690_;
v___y_1590_ = v___y_1691_;
v___y_1591_ = v___y_1692_;
goto v___jp_1584_;
}
}
v___jp_1706_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_inc_ref(v___y_1712_);
v___x_1714_ = lean_apply_1(v___y_1712_, v___y_1711_);
lean_inc(v___y_1709_);
v___x_1715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1715_, 0, v___y_1709_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
lean_ctor_set(v___x_1715_, 2, v_a_1713_);
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
v___y_1683_ = v___y_1707_;
v___y_1684_ = v___y_1708_;
v___y_1685_ = v___y_1709_;
v___y_1686_ = v___y_1710_;
v___y_1687_ = v___y_1712_;
v_prefixPoint_x3f_1688_ = v___x_1716_;
v___y_1689_ = v___y_1446_;
v___y_1690_ = v___y_1447_;
v___y_1691_ = v___y_1448_;
v___y_1692_ = v___y_1449_;
goto v___jp_1682_;
}
v___jp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_inc_ref(v_a_1718_);
v___x_1719_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___boxed), 6, 1);
lean_closure_set(v___x_1719_, 0, v_a_1718_);
lean_inc(v_a_1458_);
v___x_1720_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__0___redArg(v_a_1458_, v___x_1719_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
if (lean_obj_tag(v_a_1721_) == 1)
{
lean_object* v_val_1722_; lean_object* v_snd_1723_; lean_object* v_fst_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1782_; 
v_val_1722_ = lean_ctor_get(v_a_1721_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v_a_1721_, 1);
v_snd_1723_ = lean_ctor_get(v_val_1722_, 1);
v_fst_1724_ = lean_ctor_get(v_val_1722_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_val_1722_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1726_ = v_val_1722_;
v_isShared_1727_ = v_isSharedCheck_1782_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1723_);
lean_inc(v_fst_1724_);
lean_dec(v_val_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1782_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_fst_1728_; lean_object* v_snd_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1781_; 
v_fst_1728_ = lean_ctor_get(v_snd_1723_, 0);
v_snd_1729_ = lean_ctor_get(v_snd_1723_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_snd_1723_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1731_ = v_snd_1723_;
v_isShared_1732_ = v_isSharedCheck_1781_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_snd_1729_);
lean_inc(v_fst_1728_);
lean_dec(v_snd_1723_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1781_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___f_1733_; lean_object* v___x_1734_; 
lean_inc(v_fst_1724_);
v___f_1733_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_1733_, 0, v_fst_1724_);
lean_inc(v_inv_1438_);
v___x_1734_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse(v_snd_1729_, v_inv_1438_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_invariantUse_1735_; lean_object* v_conditionIdx_1736_; lean_object* v_cursorPrefix_1737_; lean_object* v_letMutsTuple_1738_; uint8_t v___x_1739_; 
v_invariantUse_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_invariantUse_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v_conditionIdx_1736_ = lean_ctor_get(v_invariantUse_1735_, 0);
lean_inc(v_conditionIdx_1736_);
v_cursorPrefix_1737_ = lean_ctor_get(v_invariantUse_1735_, 1);
lean_inc_ref(v_cursorPrefix_1737_);
v_letMutsTuple_1738_ = lean_ctor_get(v_invariantUse_1735_, 4);
lean_inc_ref(v_letMutsTuple_1738_);
lean_dec_ref(v_invariantUse_1735_);
v___x_1739_ = lean_nat_dec_eq(v_conditionIdx_1736_, v___x_1471_);
lean_dec(v_conditionIdx_1736_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref(v_letMutsTuple_1738_);
lean_dec_ref(v_cursorPrefix_1737_);
lean_dec_ref(v___f_1733_);
lean_dec(v_snd_1729_);
lean_dec(v_fst_1728_);
lean_dec(v_fst_1724_);
lean_dec_ref(v_a_1718_);
lean_del_object(v___x_1469_);
lean_del_object(v___x_1464_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v_snd_1467_);
lean_ctor_set(v___x_1731_, 0, v_fst_1466_);
v___x_1741_ = v___x_1731_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_fst_1466_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_snd_1467_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v___x_1741_);
lean_ctor_set(v___x_1726_, 0, v_fst_1462_);
v___x_1743_ = v___x_1726_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_fst_1462_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
v_a_1452_ = v___x_1743_;
goto v___jp_1451_;
}
}
}
else
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
lean_del_object(v___x_1731_);
lean_del_object(v___x_1726_);
v___x_1746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn_spec__2___closed__7));
v___x_1747_ = l_Lean_Expr_isAppOf(v_cursorPrefix_1737_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_dec_ref(v_letMutsTuple_1738_);
lean_dec_ref(v_cursorPrefix_1737_);
v___y_1683_ = v_fst_1728_;
v___y_1684_ = v_snd_1729_;
v___y_1685_ = v_fst_1724_;
v___y_1686_ = v_a_1718_;
v___y_1687_ = v___f_1733_;
v_prefixPoint_x3f_1688_ = v_fst_1462_;
v___y_1689_ = v___y_1446_;
v___y_1690_ = v___y_1447_;
v___y_1691_ = v___y_1448_;
v___y_1692_ = v___y_1449_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v_fst_1462_);
v___x_1748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__10));
lean_inc_ref(v_xs_1440_);
v___x_1749_ = l_Lean_Meta_mkProjection(v_xs_1440_, v___x_1748_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = l_Lean_Meta_mkEq(v_a_1750_, v_cursorPrefix_1737_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
lean_inc_ref(v_letMuts_1441_);
v___x_1753_ = l_Lean_Meta_mkEq(v_letMuts_1441_, v_letMutsTuple_1738_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
lean_inc(v_fst_1724_);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___lam__1(v_fst_1724_, v_a_1754_);
v___y_1707_ = v_fst_1728_;
v___y_1708_ = v_snd_1729_;
v___y_1709_ = v_fst_1724_;
v___y_1710_ = v_a_1718_;
v___y_1711_ = v_a_1752_;
v___y_1712_ = v___f_1733_;
v_a_1713_ = v___x_1755_;
goto v___jp_1706_;
}
else
{
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1756_; 
v_a_1756_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1753_, 1);
v___y_1707_ = v_fst_1728_;
v___y_1708_ = v_snd_1729_;
v___y_1709_ = v_fst_1724_;
v___y_1710_ = v_a_1718_;
v___y_1711_ = v_a_1752_;
v___y_1712_ = v___f_1733_;
v_a_1713_ = v_a_1756_;
goto v___jp_1706_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_a_1752_);
lean_dec_ref(v___f_1733_);
lean_dec(v_snd_1729_);
lean_dec(v_fst_1728_);
lean_dec(v_fst_1724_);
lean_dec_ref(v_a_1718_);
lean_del_object(v___x_1469_);
lean_dec(v_snd_1467_);
lean_dec(v_fst_1466_);
lean_del_object(v___x_1464_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1757_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1753_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1753_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v_letMutsTuple_1738_);
lean_dec_ref(v___f_1733_);
lean_dec(v_snd_1729_);
lean_dec(v_fst_1728_);
lean_dec(v_fst_1724_);
lean_dec_ref(v_a_1718_);
lean_del_object(v___x_1469_);
lean_dec(v_snd_1467_);
lean_dec(v_fst_1466_);
lean_del_object(v___x_1464_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1765_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1751_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1751_);
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
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_letMutsTuple_1738_);
lean_dec_ref(v_cursorPrefix_1737_);
lean_dec_ref(v___f_1733_);
lean_dec(v_snd_1729_);
lean_dec(v_fst_1728_);
lean_dec(v_fst_1724_);
lean_dec_ref(v_a_1718_);
lean_del_object(v___x_1469_);
lean_dec(v_snd_1467_);
lean_dec(v_fst_1466_);
lean_del_object(v___x_1464_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1773_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1749_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1749_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1734_);
lean_del_object(v___x_1731_);
lean_del_object(v___x_1726_);
v___y_1683_ = v_fst_1728_;
v___y_1684_ = v_snd_1729_;
v___y_1685_ = v_fst_1724_;
v___y_1686_ = v_a_1718_;
v___y_1687_ = v___f_1733_;
v_prefixPoint_x3f_1688_ = v_fst_1462_;
v___y_1689_ = v___y_1446_;
v___y_1690_ = v___y_1447_;
v___y_1691_ = v___y_1448_;
v___y_1692_ = v___y_1449_;
goto v___jp_1682_;
}
}
}
}
else
{
lean_dec(v_a_1721_);
v___y_1585_ = v_a_1718_;
v_prefixPoint_x3f_1586_ = v_fst_1462_;
v_suffixPoint_x3f_1587_ = v_fst_1466_;
v___y_1588_ = v___y_1446_;
v___y_1589_ = v___y_1447_;
v___y_1590_ = v___y_1448_;
v___y_1591_ = v___y_1449_;
goto v___jp_1584_;
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref(v_a_1718_);
lean_del_object(v___x_1469_);
lean_dec(v_snd_1467_);
lean_dec(v_fst_1466_);
lean_del_object(v___x_1464_);
lean_dec(v_fst_1462_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1783_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1720_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1720_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec_ref(v_b_1445_);
lean_dec_ref(v_letMuts_1441_);
lean_dec_ref(v_xs_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v_inv_1438_);
v_a_1806_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1459_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1459_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
v___jp_1451_:
{
size_t v___x_1453_; size_t v___x_1454_; 
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1444_, v___x_1453_);
v_i_1444_ = v___x_1454_;
v_b_1445_ = v_a_1452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___boxed(lean_object* v_inv_1814_, lean_object* v___x_1815_, lean_object* v_xs_1816_, lean_object* v_letMuts_1817_, lean_object* v_as_1818_, lean_object* v_sz_1819_, lean_object* v_i_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
size_t v_sz_boxed_1827_; size_t v_i_boxed_1828_; lean_object* v_res_1829_; 
v_sz_boxed_1827_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v_i_boxed_1828_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_res_1829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1814_, v___x_1815_, v_xs_1816_, v_letMuts_1817_, v_as_1818_, v_sz_boxed_1827_, v_i_boxed_1828_, v_b_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_as_1818_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(lean_object* v_vcs_1839_, lean_object* v_inv_1840_, lean_object* v_xs_1841_, lean_object* v_letMuts_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_lctx_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; size_t v_sz_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v_lctx_1848_ = lean_ctor_get(v_a_1843_, 2);
v___x_1849_ = lean_box(0);
v___x_1850_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___closed__2));
v_sz_1851_ = lean_array_size(v_vcs_1839_);
v___x_1852_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1848_);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1(v_inv_1840_, v_lctx_1848_, v_xs_1841_, v_letMuts_1842_, v_vcs_1839_, v_sz_1851_, v___x_1852_, v___x_1850_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1897_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1897_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1897_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_snd_1862_; lean_object* v_fst_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1896_; 
v_snd_1862_ = lean_ctor_get(v_a_1854_, 1);
v_fst_1863_ = lean_ctor_get(v_a_1854_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_a_1854_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1865_ = v_a_1854_;
v_isShared_1866_ = v_isSharedCheck_1896_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snd_1862_);
lean_inc(v_fst_1863_);
lean_dec(v_a_1854_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1896_;
goto v_resetjp_1864_;
}
v___jp_1858_:
{
lean_object* v___x_1860_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1849_);
v___x_1860_ = v___x_1856_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1849_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
v_resetjp_1864_:
{
if (lean_obj_tag(v_fst_1863_) == 0)
{
lean_del_object(v___x_1865_);
lean_dec(v_snd_1862_);
goto v___jp_1858_;
}
else
{
lean_object* v_fst_1867_; 
v_fst_1867_ = lean_ctor_get(v_snd_1862_, 0);
lean_inc(v_fst_1867_);
if (lean_obj_tag(v_fst_1867_) == 0)
{
lean_dec_ref_known(v_fst_1863_, 1);
lean_del_object(v___x_1865_);
lean_dec(v_snd_1862_);
goto v___jp_1858_;
}
else
{
lean_object* v_snd_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1894_; 
lean_del_object(v___x_1856_);
v_snd_1868_ = lean_ctor_get(v_snd_1862_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_snd_1862_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v_snd_1862_, 0);
lean_dec(v_unused_1895_);
v___x_1870_ = v_snd_1862_;
v_isShared_1871_ = v_isSharedCheck_1894_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_snd_1868_);
lean_dec(v_snd_1862_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1894_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_val_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1893_; 
v_val_1872_ = lean_ctor_get(v_fst_1863_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_fst_1863_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1874_ = v_fst_1863_;
v_isShared_1875_ = v_isSharedCheck_1893_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_val_1872_);
lean_dec(v_fst_1863_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1893_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_val_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1892_; 
v_val_1876_ = lean_ctor_get(v_fst_1867_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_fst_1867_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1878_ = v_fst_1867_;
v_isShared_1879_ = v_isSharedCheck_1892_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_val_1876_);
lean_dec(v_fst_1867_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1892_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v_val_1876_);
v___x_1881_ = v___x_1870_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_val_1876_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_snd_1868_);
v___x_1881_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v___x_1881_);
lean_ctor_set(v___x_1865_, 0, v_val_1872_);
v___x_1883_ = v___x_1865_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_val_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1883_);
v___x_1885_ = v___x_1878_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1885_);
v___x_1887_ = v___x_1874_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
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
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1853_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1853_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints___boxed(lean_object* v_vcs_1906_, lean_object* v_inv_1907_, lean_object* v_xs_1908_, lean_object* v_letMuts_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_vcs_1906_, v_inv_1907_, v_xs_1908_, v_letMuts_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec_ref(v_vcs_1906_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(lean_object* v_inst_1916_, lean_object* v_a_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___redArg(v_a_1917_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0___boxed(lean_object* v_inst_1924_, lean_object* v_a_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__0(v_inst_1924_, v_a_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(lean_object* v_m_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_MVarId_getDecl(v_m_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_userName_1940_; lean_object* v_lctx_1941_; lean_object* v_type_1942_; lean_object* v_localInstances_1943_; uint8_t v_kind_1944_; lean_object* v_numScopeArgs_1945_; lean_object* v___x_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v_userName_1940_ = lean_ctor_get(v_a_1939_, 0);
lean_inc(v_userName_1940_);
v_lctx_1941_ = lean_ctor_get(v_a_1939_, 1);
lean_inc_ref(v_lctx_1941_);
v_type_1942_ = lean_ctor_get(v_a_1939_, 2);
lean_inc_ref(v_type_1942_);
v_localInstances_1943_ = lean_ctor_get(v_a_1939_, 4);
lean_inc_ref(v_localInstances_1943_);
v_kind_1944_ = lean_ctor_get_uint8(v_a_1939_, sizeof(void*)*7);
v_numScopeArgs_1945_ = lean_ctor_get(v_a_1939_, 5);
lean_inc(v_numScopeArgs_1945_);
lean_dec(v_a_1939_);
v___x_1946_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_1941_, v_localInstances_1943_, v_type_1942_, v_kind_1944_, v_userName_1940_, v_numScopeArgs_1945_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1955_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1951_ = l_Lean_Expr_mvarId_x21(v_a_1947_);
lean_dec(v_a_1947_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1951_);
v___x_1953_ = v___x_1949_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
v_a_1956_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1946_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1946_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_a_1964_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1938_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1938_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar___boxed(lean_object* v_m_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v_m_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(lean_object* v_msg_1979_){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = l_String_instInhabitedSlice;
v___x_1981_ = lean_panic_fn_borrowed(v___x_1980_, v_msg_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(lean_object* v_s_1982_, lean_object* v_a_1983_, uint8_t v_b_1984_){
_start:
{
lean_object* v_str_1985_; lean_object* v_startInclusive_1986_; lean_object* v_endExclusive_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_str_1985_ = lean_ctor_get(v_s_1982_, 0);
v_startInclusive_1986_ = lean_ctor_get(v_s_1982_, 1);
v_endExclusive_1987_ = lean_ctor_get(v_s_1982_, 2);
v___x_1988_ = lean_nat_sub(v_endExclusive_1987_, v_startInclusive_1986_);
v___x_1989_ = lean_nat_dec_eq(v_a_1983_, v___x_1988_);
lean_dec(v___x_1988_);
if (v___x_1989_ == 0)
{
uint32_t v___x_1990_; lean_object* v___x_1991_; uint32_t v___x_1992_; uint8_t v___x_1993_; 
v___x_1990_ = 64;
v___x_1991_ = lean_nat_add(v_startInclusive_1986_, v_a_1983_);
lean_dec(v_a_1983_);
v___x_1992_ = lean_string_utf8_get_fast(v_str_1985_, v___x_1991_);
v___x_1993_ = lean_uint32_dec_eq(v___x_1992_, v___x_1990_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_string_utf8_next_fast(v_str_1985_, v___x_1991_);
lean_dec(v___x_1991_);
v___x_1995_ = lean_nat_sub(v___x_1994_, v_startInclusive_1986_);
v_a_1983_ = v___x_1995_;
v_b_1984_ = v___x_1993_;
goto _start;
}
else
{
lean_dec(v___x_1991_);
return v___x_1993_;
}
}
else
{
lean_dec(v_a_1983_);
return v_b_1984_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg___boxed(lean_object* v_s_1997_, lean_object* v_a_1998_, lean_object* v_b_1999_){
_start:
{
uint8_t v_b_boxed_2000_; uint8_t v_res_2001_; lean_object* v_r_2002_; 
v_b_boxed_2000_ = lean_unbox(v_b_1999_);
v_res_2001_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_1997_, v_a_1998_, v_b_boxed_2000_);
lean_dec_ref(v_s_1997_);
v_r_2002_ = lean_box(v_res_2001_);
return v_r_2002_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(lean_object* v_s_2003_){
_start:
{
lean_object* v_searcher_2004_; uint8_t v___x_2005_; uint8_t v___x_2006_; 
v_searcher_2004_ = lean_unsigned_to_nat(0u);
v___x_2005_ = 0;
v___x_2006_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2003_, v_searcher_2004_, v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2___boxed(lean_object* v_s_2007_){
_start:
{
uint8_t v_res_2008_; lean_object* v_r_2009_; 
v_res_2008_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v_s_2007_);
lean_dec_ref(v_s_2007_);
v_r_2009_ = lean_box(v_res_2008_);
return v_r_2009_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__2));
v___x_2014_ = lean_unsigned_to_nat(14u);
v___x_2015_ = lean_unsigned_to_nat(22u);
v___x_2016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__1));
v___x_2017_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__0));
v___x_2018_ = l_mkPanicMessageWithDecl(v___x_2017_, v___x_2016_, v___x_2015_, v___x_2014_, v___x_2013_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(lean_object* v_x_2019_){
_start:
{
switch(lean_obj_tag(v_x_2019_))
{
case 1:
{
lean_object* v_info_2020_; lean_object* v_kind_2021_; lean_object* v_args_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2032_; 
v_info_2020_ = lean_ctor_get(v_x_2019_, 0);
v_kind_2021_ = lean_ctor_get(v_x_2019_, 1);
v_args_2022_ = lean_ctor_get(v_x_2019_, 2);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_x_2019_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2024_ = v_x_2019_;
v_isShared_2025_ = v_isSharedCheck_2032_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_args_2022_);
lean_inc(v_kind_2021_);
lean_inc(v_info_2020_);
lean_dec(v_x_2019_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2032_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
size_t v_sz_2026_; size_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
v_sz_2026_ = lean_array_size(v_args_2022_);
v___x_2027_ = ((size_t)0ULL);
v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_2026_, v___x_2027_, v_args_2022_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 2, v___x_2028_);
v___x_2030_ = v___x_2024_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_info_2020_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_kind_2021_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
case 3:
{
lean_object* v_info_2033_; lean_object* v_rawVal_2034_; lean_object* v_val_2035_; lean_object* v_preresolved_2036_; uint8_t v___y_2038_; lean_object* v_str_2055_; lean_object* v_startPos_2056_; lean_object* v_stopPos_2057_; uint8_t v___x_2058_; 
v_info_2033_ = lean_ctor_get(v_x_2019_, 0);
v_rawVal_2034_ = lean_ctor_get(v_x_2019_, 1);
v_val_2035_ = lean_ctor_get(v_x_2019_, 2);
v_preresolved_2036_ = lean_ctor_get(v_x_2019_, 3);
v_str_2055_ = lean_ctor_get(v_rawVal_2034_, 0);
v_startPos_2056_ = lean_ctor_get(v_rawVal_2034_, 1);
v_stopPos_2057_ = lean_ctor_get(v_rawVal_2034_, 2);
v___x_2058_ = lean_string_is_valid_pos(v_str_2055_, v_startPos_2056_);
if (v___x_2058_ == 0)
{
goto v___jp_2051_;
}
else
{
uint8_t v___x_2059_; 
v___x_2059_ = lean_string_is_valid_pos(v_str_2055_, v_stopPos_2057_);
if (v___x_2059_ == 0)
{
goto v___jp_2051_;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_nat_dec_le(v_startPos_2056_, v_stopPos_2057_);
if (v___x_2060_ == 0)
{
goto v___jp_2051_;
}
else
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
lean_inc(v_stopPos_2057_);
lean_inc(v_startPos_2056_);
lean_inc_ref(v_str_2055_);
v___x_2061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2061_, 0, v_str_2055_);
lean_ctor_set(v___x_2061_, 1, v_startPos_2056_);
lean_ctor_set(v___x_2061_, 2, v_stopPos_2057_);
v___x_2062_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2061_);
lean_dec_ref_known(v___x_2061_, 3);
v___y_2038_ = v___x_2062_;
goto v___jp_2037_;
}
}
}
v___jp_2037_:
{
if (v___y_2038_ == 0)
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2046_; 
lean_inc(v_preresolved_2036_);
lean_inc(v_val_2035_);
lean_inc_ref(v_rawVal_2034_);
lean_inc(v_info_2033_);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_x_2019_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; 
v_unused_2047_ = lean_ctor_get(v_x_2019_, 3);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_x_2019_, 2);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_x_2019_, 1);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_x_2019_, 0);
lean_dec(v_unused_2050_);
v___x_2040_ = v_x_2019_;
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v_x_2019_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_erase_macro_scopes(v_val_2035_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 2, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_info_2033_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_rawVal_2034_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_preresolved_2036_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
return v_x_2019_;
}
}
v___jp_2051_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2052_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax___closed__3);
v___x_2053_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__1(v___x_2052_);
v___x_2054_ = l_String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2(v___x_2053_);
lean_dec_ref(v___x_2053_);
v___y_2038_ = v___x_2054_;
goto v___jp_2037_;
}
}
default: 
{
return v_x_2019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(size_t v_sz_2063_, size_t v_i_2064_, lean_object* v_bs_2065_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_usize_dec_lt(v_i_2064_, v_sz_2063_);
if (v___x_2066_ == 0)
{
return v_bs_2065_;
}
else
{
lean_object* v_v_2067_; lean_object* v___x_2068_; lean_object* v_bs_x27_2069_; lean_object* v___x_2070_; size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v_v_2067_ = lean_array_uget(v_bs_2065_, v_i_2064_);
v___x_2068_ = lean_unsigned_to_nat(0u);
v_bs_x27_2069_ = lean_array_uset(v_bs_2065_, v_i_2064_, v___x_2068_);
v___x_2070_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_v_2067_);
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = lean_usize_add(v_i_2064_, v___x_2071_);
v___x_2073_ = lean_array_uset(v_bs_x27_2069_, v_i_2064_, v___x_2070_);
v_i_2064_ = v___x_2072_;
v_bs_2065_ = v___x_2073_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0___boxed(lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_bs_2077_){
_start:
{
size_t v_sz_boxed_2078_; size_t v_i_boxed_2079_; lean_object* v_res_2080_; 
v_sz_boxed_2078_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2079_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__0(v_sz_boxed_2078_, v_i_boxed_2079_, v_bs_2077_);
return v_res_2080_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(lean_object* v_s_2081_, lean_object* v_inst_2082_, lean_object* v_R_2083_, lean_object* v_a_2084_, uint8_t v_b_2085_, lean_object* v_c_2086_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___redArg(v_s_2081_, v_a_2084_, v_b_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2___boxed(lean_object* v_s_2088_, lean_object* v_inst_2089_, lean_object* v_R_2090_, lean_object* v_a_2091_, lean_object* v_b_2092_, lean_object* v_c_2093_){
_start:
{
uint8_t v_b_boxed_2094_; uint8_t v_res_2095_; lean_object* v_r_2096_; 
v_b_boxed_2094_ = lean_unbox(v_b_2092_);
v_res_2095_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_spec__2_spec__2(v_s_2088_, v_inst_2089_, v_R_2090_, v_a_2091_, v_b_boxed_2094_, v_c_2093_);
lean_dec_ref(v_s_2088_);
v_r_2096_ = lean_box(v_res_2095_);
return v_r_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter___redArg(lean_object* v_x_2097_, lean_object* v_h__1_2098_, lean_object* v_h__2_2099_, lean_object* v_h__3_2100_, lean_object* v_h__4_2101_){
_start:
{
switch(lean_obj_tag(v_x_2097_))
{
case 0:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_dec(v_h__3_2100_);
lean_dec(v_h__2_2099_);
lean_dec(v_h__1_2098_);
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_apply_1(v_h__4_2101_, v___x_2102_);
return v___x_2103_;
}
case 1:
{
lean_object* v_info_2104_; lean_object* v_kind_2105_; lean_object* v_args_2106_; lean_object* v___x_2107_; 
lean_dec(v_h__4_2101_);
lean_dec(v_h__3_2100_);
lean_dec(v_h__1_2098_);
v_info_2104_ = lean_ctor_get(v_x_2097_, 0);
lean_inc(v_info_2104_);
v_kind_2105_ = lean_ctor_get(v_x_2097_, 1);
lean_inc(v_kind_2105_);
v_args_2106_ = lean_ctor_get(v_x_2097_, 2);
lean_inc_ref(v_args_2106_);
lean_dec_ref_known(v_x_2097_, 3);
v___x_2107_ = lean_apply_3(v_h__2_2099_, v_info_2104_, v_kind_2105_, v_args_2106_);
return v___x_2107_;
}
case 2:
{
lean_object* v_info_2108_; lean_object* v_val_2109_; lean_object* v___x_2110_; 
lean_dec(v_h__4_2101_);
lean_dec(v_h__2_2099_);
lean_dec(v_h__1_2098_);
v_info_2108_ = lean_ctor_get(v_x_2097_, 0);
lean_inc(v_info_2108_);
v_val_2109_ = lean_ctor_get(v_x_2097_, 1);
lean_inc_ref(v_val_2109_);
lean_dec_ref_known(v_x_2097_, 2);
v___x_2110_ = lean_apply_2(v_h__3_2100_, v_info_2108_, v_val_2109_);
return v___x_2110_;
}
default: 
{
lean_object* v_info_2111_; lean_object* v_rawVal_2112_; lean_object* v_val_2113_; lean_object* v_preresolved_2114_; lean_object* v___x_2115_; 
lean_dec(v_h__4_2101_);
lean_dec(v_h__3_2100_);
lean_dec(v_h__2_2099_);
v_info_2111_ = lean_ctor_get(v_x_2097_, 0);
lean_inc(v_info_2111_);
v_rawVal_2112_ = lean_ctor_get(v_x_2097_, 1);
lean_inc_ref(v_rawVal_2112_);
v_val_2113_ = lean_ctor_get(v_x_2097_, 2);
lean_inc(v_val_2113_);
v_preresolved_2114_ = lean_ctor_get(v_x_2097_, 3);
lean_inc(v_preresolved_2114_);
lean_dec_ref_known(v_x_2097_, 4);
v___x_2115_ = lean_apply_4(v_h__1_2098_, v_info_2111_, v_rawVal_2112_, v_val_2113_, v_preresolved_2114_);
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax_match__1_splitter(lean_object* v_motive_2116_, lean_object* v_x_2117_, lean_object* v_h__1_2118_, lean_object* v_h__2_2119_, lean_object* v_h__3_2120_, lean_object* v_h__4_2121_){
_start:
{
switch(lean_obj_tag(v_x_2117_))
{
case 0:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec(v_h__3_2120_);
lean_dec(v_h__2_2119_);
lean_dec(v_h__1_2118_);
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_apply_1(v_h__4_2121_, v___x_2122_);
return v___x_2123_;
}
case 1:
{
lean_object* v_info_2124_; lean_object* v_kind_2125_; lean_object* v_args_2126_; lean_object* v___x_2127_; 
lean_dec(v_h__4_2121_);
lean_dec(v_h__3_2120_);
lean_dec(v_h__1_2118_);
v_info_2124_ = lean_ctor_get(v_x_2117_, 0);
lean_inc(v_info_2124_);
v_kind_2125_ = lean_ctor_get(v_x_2117_, 1);
lean_inc(v_kind_2125_);
v_args_2126_ = lean_ctor_get(v_x_2117_, 2);
lean_inc_ref(v_args_2126_);
lean_dec_ref_known(v_x_2117_, 3);
v___x_2127_ = lean_apply_3(v_h__2_2119_, v_info_2124_, v_kind_2125_, v_args_2126_);
return v___x_2127_;
}
case 2:
{
lean_object* v_info_2128_; lean_object* v_val_2129_; lean_object* v___x_2130_; 
lean_dec(v_h__4_2121_);
lean_dec(v_h__2_2119_);
lean_dec(v_h__1_2118_);
v_info_2128_ = lean_ctor_get(v_x_2117_, 0);
lean_inc(v_info_2128_);
v_val_2129_ = lean_ctor_get(v_x_2117_, 1);
lean_inc_ref(v_val_2129_);
lean_dec_ref_known(v_x_2117_, 2);
v___x_2130_ = lean_apply_2(v_h__3_2120_, v_info_2128_, v_val_2129_);
return v___x_2130_;
}
default: 
{
lean_object* v_info_2131_; lean_object* v_rawVal_2132_; lean_object* v_val_2133_; lean_object* v_preresolved_2134_; lean_object* v___x_2135_; 
lean_dec(v_h__4_2121_);
lean_dec(v_h__3_2120_);
lean_dec(v_h__2_2119_);
v_info_2131_ = lean_ctor_get(v_x_2117_, 0);
lean_inc(v_info_2131_);
v_rawVal_2132_ = lean_ctor_get(v_x_2117_, 1);
lean_inc_ref(v_rawVal_2132_);
v_val_2133_ = lean_ctor_get(v_x_2117_, 2);
lean_inc(v_val_2133_);
v_preresolved_2134_ = lean_ctor_get(v_x_2117_, 3);
lean_inc(v_preresolved_2134_);
lean_dec_ref_known(v_x_2117_, 4);
v___x_2135_ = lean_apply_4(v_h__1_2118_, v_info_2131_, v_rawVal_2132_, v_val_2133_, v_preresolved_2134_);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_2136_, lean_object* v_h__1_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_apply_2(v_h__1_2137_, v_x_2136_, lean_box(0));
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2139_, lean_object* v_P_2140_, lean_object* v_motive_2141_, lean_object* v_x_2142_, lean_object* v_h__1_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_apply_2(v_h__1_2143_, v_x_2142_, lean_box(0));
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___redArg(lean_object* v_syn_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(lean_object* v_name_2147_, lean_object* v_syn_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_syn_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax___boxed(lean_object* v_name_2150_, lean_object* v_syn_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromTSyntax(v_name_2150_, v_syn_2151_);
lean_dec(v_name_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(lean_object* v_e_2159_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go___closed__1));
v___x_2187_ = lean_unsigned_to_nat(2u);
v___x_2188_ = l_Lean_Expr_isAppOfArity(v_e_2159_, v___x_2186_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkAnd___closed__1));
v___x_2190_ = lean_unsigned_to_nat(3u);
v___x_2191_ = l_Lean_Expr_isAppOfArity(v_e_2159_, v___x_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr___closed__1));
v___x_2193_ = l_Lean_Expr_isAppOfArity(v_e_2159_, v___x_2192_, v___x_2190_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_revertFVarsInTypeExcept_spec__0___redArg___closed__1));
v___x_2195_ = l_Lean_Expr_isAppOfArity(v_e_2159_, v___x_2194_, v___x_2190_);
if (v___x_2195_ == 0)
{
goto v___jp_2160_;
}
else
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Expr_appArg_x21(v_e_2159_);
if (lean_obj_tag(v___x_2196_) == 6)
{
lean_object* v_binderName_2197_; lean_object* v_binderType_2198_; lean_object* v_body_2199_; uint8_t v_binderInfo_2200_; lean_object* v___x_2201_; 
lean_dec_ref(v_e_2159_);
v_binderName_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_binderName_2197_);
v_binderType_2198_ = lean_ctor_get(v___x_2196_, 1);
lean_inc_ref(v_binderType_2198_);
v_body_2199_ = lean_ctor_get(v___x_2196_, 2);
lean_inc_ref(v_body_2199_);
v_binderInfo_2200_ = lean_ctor_get_uint8(v___x_2196_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_2196_, 3);
v___x_2201_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2199_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_dec_ref(v_binderType_2198_);
lean_dec(v_binderName_2197_);
return v___x_2201_;
}
else
{
lean_object* v_val_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2219_; 
v_val_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2219_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_val_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2219_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_fst_2206_; lean_object* v_snd_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2218_; 
v_fst_2206_ = lean_ctor_get(v_val_2202_, 0);
v_snd_2207_ = lean_ctor_get(v_val_2202_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_val_2202_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2209_ = v_val_2202_;
v_isShared_2210_ = v_isSharedCheck_2218_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_snd_2207_);
lean_inc(v_fst_2206_);
lean_dec(v_val_2202_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2218_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = l_Lean_mkForall(v_binderName_2197_, v_binderInfo_2200_, v_binderType_2198_, v_snd_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_fst_2206_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2215_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2213_);
v___x_2215_ = v___x_2204_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2196_);
goto v___jp_2160_;
}
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = l_Lean_Expr_appFn_x21(v_e_2159_);
v___x_2221_ = l_Lean_Expr_appArg_x21(v___x_2220_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2221_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_dec_ref(v_e_2159_);
return v___x_2222_;
}
else
{
lean_object* v_val_2223_; lean_object* v_snd_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_val_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v___x_2222_, 1);
v_snd_2224_ = lean_ctor_get(v_val_2223_, 1);
lean_inc(v_snd_2224_);
lean_dec(v_val_2223_);
v___x_2225_ = l_Lean_Expr_appArg_x21(v_e_2159_);
lean_dec_ref(v_e_2159_);
v___x_2226_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2225_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_dec(v_snd_2224_);
return v___x_2226_;
}
else
{
lean_object* v_val_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2244_; 
v_val_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2244_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_val_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2244_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_fst_2231_; lean_object* v_snd_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2243_; 
v_fst_2231_ = lean_ctor_get(v_val_2227_, 0);
v_snd_2232_ = lean_ctor_get(v_val_2227_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_val_2227_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2234_ = v_val_2227_;
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_snd_2232_);
lean_inc(v_fst_2231_);
lean_dec(v_val_2227_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = l_Lean_mkOr(v_snd_2224_, v_snd_2232_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v___x_2236_);
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_fst_2231_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2240_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2238_);
v___x_2240_ = v___x_2229_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
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
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = l_Lean_Expr_appFn_x21(v_e_2159_);
v___x_2246_ = l_Lean_Expr_appArg_x21(v___x_2245_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_dec_ref(v_e_2159_);
return v___x_2247_;
}
else
{
lean_object* v_val_2248_; lean_object* v_snd_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_val_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v___x_2247_, 1);
v_snd_2249_ = lean_ctor_get(v_val_2248_, 1);
lean_inc(v_snd_2249_);
lean_dec(v_val_2248_);
v___x_2250_ = l_Lean_Expr_appArg_x21(v_e_2159_);
lean_dec_ref(v_e_2159_);
v___x_2251_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v___x_2250_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_dec(v_snd_2249_);
return v___x_2251_;
}
else
{
lean_object* v_val_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2269_; 
v_val_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2269_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_val_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2269_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_fst_2256_; lean_object* v_snd_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2268_; 
v_fst_2256_ = lean_ctor_get(v_val_2252_, 0);
v_snd_2257_ = lean_ctor_get(v_val_2252_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_val_2252_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2259_ = v_val_2252_;
v_isShared_2260_ = v_isSharedCheck_2268_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_snd_2257_);
lean_inc(v_fst_2256_);
lean_dec(v_val_2252_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2268_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2261_ = l_Lean_mkAnd(v_snd_2249_, v_snd_2257_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v___x_2261_);
v___x_2263_ = v___x_2259_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_fst_2256_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2265_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2263_);
v___x_2265_ = v___x_2254_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
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
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2270_ = lean_box(0);
v___x_2271_ = l_Lean_Expr_getAppFn(v_e_2159_);
v___x_2272_ = l_Lean_Expr_constLevels_x21(v___x_2271_);
lean_dec_ref(v___x_2271_);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = l_List_get_x21Internal___redArg(v___x_2270_, v___x_2272_, v___x_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_unsigned_to_nat(1u);
v___x_2276_ = l_Lean_Expr_getAppNumArgs(v_e_2159_);
v___x_2277_ = lean_nat_sub(v___x_2276_, v___x_2275_);
lean_dec(v___x_2276_);
v___x_2278_ = lean_nat_sub(v___x_2277_, v___x_2275_);
lean_dec(v___x_2277_);
v___x_2279_ = l_Lean_Expr_getRevArg_x21(v_e_2159_, v___x_2278_);
lean_dec_ref(v_e_2159_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2274_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
v___jp_2160_:
{
if (lean_obj_tag(v_e_2159_) == 8)
{
lean_object* v_declName_2161_; lean_object* v_type_2162_; lean_object* v_value_2163_; lean_object* v_body_2164_; uint8_t v_nondep_2165_; lean_object* v___x_2166_; 
v_declName_2161_ = lean_ctor_get(v_e_2159_, 0);
lean_inc(v_declName_2161_);
v_type_2162_ = lean_ctor_get(v_e_2159_, 1);
lean_inc_ref(v_type_2162_);
v_value_2163_ = lean_ctor_get(v_e_2159_, 2);
lean_inc_ref(v_value_2163_);
v_body_2164_ = lean_ctor_get(v_e_2159_, 3);
lean_inc_ref(v_body_2164_);
v_nondep_2165_ = lean_ctor_get_uint8(v_e_2159_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2159_, 4);
v___x_2166_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_body_2164_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_dec_ref(v_value_2163_);
lean_dec_ref(v_type_2162_);
lean_dec(v_declName_2161_);
return v___x_2166_;
}
else
{
lean_object* v_val_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2184_; 
v_val_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2184_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_val_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2184_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v_fst_2171_; lean_object* v_snd_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2183_; 
v_fst_2171_ = lean_ctor_get(v_val_2167_, 0);
v_snd_2172_ = lean_ctor_get(v_val_2167_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_val_2167_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2174_ = v_val_2167_;
v_isShared_2175_ = v_isSharedCheck_2183_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snd_2172_);
lean_inc(v_fst_2171_);
lean_dec(v_val_2167_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2183_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2176_ = l_Lean_Expr_letE___override(v_declName_2161_, v_type_2162_, v_value_2163_, v_snd_2172_, v_nondep_2165_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v___x_2176_);
v___x_2178_ = v___x_2174_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_fst_2171_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2178_);
v___x_2180_ = v___x_2169_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
}
else
{
lean_object* v___x_2185_; 
lean_dec_ref(v_e_2159_);
v___x_2185_ = lean_box(0);
return v___x_2185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(lean_object* v_e_2282_){
_start:
{
lean_object* v___x_2283_; 
lean_inc_ref(v_e_2282_);
v___x_2283_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure_go(v_e_2282_);
if (lean_obj_tag(v___x_2283_) == 0)
{
return v_e_2282_;
}
else
{
lean_object* v_val_2284_; lean_object* v_fst_2285_; lean_object* v_snd_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec_ref(v_e_2282_);
v_val_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_val_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v_fst_2285_ = lean_ctor_get(v_val_2284_, 0);
lean_inc_n(v_fst_2285_, 2);
v_snd_2286_ = lean_ctor_get(v_val_2284_, 1);
lean_inc(v_snd_2286_);
lean_dec(v_val_2284_);
v___x_2287_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(v_fst_2285_);
v___x_2288_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_fst_2285_, v___x_2287_, v_snd_2286_);
return v___x_2288_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6(void){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Array_mkArray0(lean_box(0));
return v___x_2299_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__23));
v___x_2338_ = l_String_toRawSubstring_x27(v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__29));
v___x_2355_ = l_String_toRawSubstring_x27(v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(lean_object* v_handlers_2370_, lean_object* v_default_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; lean_object* v_handlers_2378_; 
v___x_2377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v_handlers_2378_ = l_Lean_Syntax_SepArray_ofElems(v___x_2377_, v_handlers_2370_);
switch(lean_obj_tag(v_default_2371_))
{
case 0:
{
lean_object* v_ref_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_ref_2379_ = lean_ctor_get(v_a_2374_, 5);
v___x_2380_ = 0;
v___x_2381_ = l_Lean_SourceInfo_fromRef(v_ref_2379_, v___x_2380_);
v___x_2382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__2));
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__3));
lean_inc_n(v___x_2381_, 3);
v___x_2384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2381_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2386_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2387_ = l_Array_append___redArg(v___x_2386_, v_handlers_2378_);
lean_dec_ref(v_handlers_2378_);
v___x_2388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2381_);
lean_ctor_set(v___x_2388_, 1, v___x_2385_);
lean_ctor_set(v___x_2388_, 2, v___x_2387_);
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2381_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = l_Lean_Syntax_node3(v___x_2381_, v___x_2382_, v___x_2384_, v___x_2388_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
case 1:
{
lean_object* v_ref_2393_; lean_object* v_quotContext_2394_; lean_object* v_currMacroScope_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_ref_2393_ = lean_ctor_get(v_a_2374_, 5);
v_quotContext_2394_ = lean_ctor_get(v_a_2374_, 10);
v_currMacroScope_2395_ = lean_ctor_get(v_a_2374_, 11);
v___x_2396_ = 0;
v___x_2397_ = l_Lean_SourceInfo_fromRef(v_ref_2393_, v___x_2396_);
v___x_2398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2397_, 12);
v___x_2400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2397_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2397_);
lean_ctor_set(v___x_2406_, 1, v___x_2404_);
v___x_2407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2397_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2411_ = l_Array_append___redArg(v___x_2410_, v_handlers_2378_);
lean_dec_ref(v_handlers_2378_);
v___x_2412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2397_);
lean_ctor_set(v___x_2412_, 1, v___x_2377_);
v___x_2413_ = lean_array_push(v___x_2411_, v___x_2412_);
v___x_2414_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__24);
v___x_2415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__25));
lean_inc(v_currMacroScope_2395_);
lean_inc(v_quotContext_2394_);
v___x_2416_ = l_Lean_addMacroScope(v_quotContext_2394_, v___x_2415_, v_currMacroScope_2395_);
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__28));
v___x_2418_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2397_);
lean_ctor_set(v___x_2418_, 1, v___x_2414_);
lean_ctor_set(v___x_2418_, 2, v___x_2416_);
lean_ctor_set(v___x_2418_, 3, v___x_2417_);
v___x_2419_ = lean_array_push(v___x_2413_, v___x_2418_);
v___x_2420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2397_);
lean_ctor_set(v___x_2420_, 1, v___x_2403_);
lean_ctor_set(v___x_2420_, 2, v___x_2419_);
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2397_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = l_Lean_Syntax_node3(v___x_2397_, v___x_2407_, v___x_2409_, v___x_2420_, v___x_2422_);
v___x_2424_ = l_Lean_Syntax_node2(v___x_2397_, v___x_2405_, v___x_2406_, v___x_2423_);
v___x_2425_ = l_Lean_Syntax_node1(v___x_2397_, v___x_2403_, v___x_2424_);
v___x_2426_ = l_Lean_Syntax_node1(v___x_2397_, v___x_2402_, v___x_2425_);
v___x_2427_ = l_Lean_Syntax_node1(v___x_2397_, v___x_2401_, v___x_2426_);
v___x_2428_ = l_Lean_Syntax_node2(v___x_2397_, v___x_2398_, v___x_2400_, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
case 2:
{
lean_object* v_ref_2430_; lean_object* v_quotContext_2431_; lean_object* v_currMacroScope_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_ref_2430_ = lean_ctor_get(v_a_2374_, 5);
v_quotContext_2431_ = lean_ctor_get(v_a_2374_, 10);
v_currMacroScope_2432_ = lean_ctor_get(v_a_2374_, 11);
v___x_2433_ = 0;
v___x_2434_ = l_Lean_SourceInfo_fromRef(v_ref_2430_, v___x_2433_);
v___x_2435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2434_, 12);
v___x_2437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2434_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2439_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2434_);
lean_ctor_set(v___x_2443_, 1, v___x_2441_);
v___x_2444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2434_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2448_ = l_Array_append___redArg(v___x_2447_, v_handlers_2378_);
lean_dec_ref(v_handlers_2378_);
v___x_2449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2434_);
lean_ctor_set(v___x_2449_, 1, v___x_2377_);
v___x_2450_ = lean_array_push(v___x_2448_, v___x_2449_);
v___x_2451_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_2452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
lean_inc(v_currMacroScope_2432_);
lean_inc(v_quotContext_2431_);
v___x_2453_ = l_Lean_addMacroScope(v_quotContext_2431_, v___x_2452_, v_currMacroScope_2432_);
v___x_2454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__34));
v___x_2455_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2434_);
lean_ctor_set(v___x_2455_, 1, v___x_2451_);
lean_ctor_set(v___x_2455_, 2, v___x_2453_);
lean_ctor_set(v___x_2455_, 3, v___x_2454_);
v___x_2456_ = lean_array_push(v___x_2450_, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2434_);
lean_ctor_set(v___x_2457_, 1, v___x_2440_);
lean_ctor_set(v___x_2457_, 2, v___x_2456_);
v___x_2458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2434_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = l_Lean_Syntax_node3(v___x_2434_, v___x_2444_, v___x_2446_, v___x_2457_, v___x_2459_);
v___x_2461_ = l_Lean_Syntax_node2(v___x_2434_, v___x_2442_, v___x_2443_, v___x_2460_);
v___x_2462_ = l_Lean_Syntax_node1(v___x_2434_, v___x_2440_, v___x_2461_);
v___x_2463_ = l_Lean_Syntax_node1(v___x_2434_, v___x_2439_, v___x_2462_);
v___x_2464_ = l_Lean_Syntax_node1(v___x_2434_, v___x_2438_, v___x_2463_);
v___x_2465_ = l_Lean_Syntax_node2(v___x_2434_, v___x_2435_, v___x_2437_, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
return v___x_2466_;
}
default: 
{
lean_object* v_e_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_e_2467_ = lean_ctor_get(v_default_2371_, 0);
lean_inc_ref(v_e_2467_);
lean_dec_ref_known(v_default_2371_, 1);
v___x_2468_ = lean_box(1);
v___x_2469_ = l_Lean_PrettyPrinter_delab(v_e_2467_, v___x_2468_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2506_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2472_ = v___x_2469_;
v_isShared_2473_ = v_isSharedCheck_2506_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2469_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2506_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v_ref_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
v_ref_2474_ = lean_ctor_get(v_a_2374_, 5);
v___x_2475_ = 0;
v___x_2476_ = l_Lean_SourceInfo_fromRef(v_ref_2474_, v___x_2475_);
v___x_2477_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__12));
v___x_2478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__13));
lean_inc_n(v___x_2476_, 11);
v___x_2479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2476_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__15));
v___x_2481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__17));
v___x_2482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_2483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__18));
v___x_2484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__19));
v___x_2485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2476_);
lean_ctor_set(v___x_2485_, 1, v___x_2483_);
v___x_2486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_2487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_2488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2476_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_2490_ = l_Array_append___redArg(v___x_2489_, v_handlers_2378_);
lean_dec_ref(v_handlers_2378_);
v___x_2491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2476_);
lean_ctor_set(v___x_2491_, 1, v___x_2377_);
v___x_2492_ = lean_array_push(v___x_2490_, v___x_2491_);
v___x_2493_ = lean_array_push(v___x_2492_, v_a_2470_);
v___x_2494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2476_);
lean_ctor_set(v___x_2494_, 1, v___x_2482_);
lean_ctor_set(v___x_2494_, 2, v___x_2493_);
v___x_2495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_2496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2476_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = l_Lean_Syntax_node3(v___x_2476_, v___x_2486_, v___x_2488_, v___x_2494_, v___x_2496_);
v___x_2498_ = l_Lean_Syntax_node2(v___x_2476_, v___x_2484_, v___x_2485_, v___x_2497_);
v___x_2499_ = l_Lean_Syntax_node1(v___x_2476_, v___x_2482_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_node1(v___x_2476_, v___x_2481_, v___x_2499_);
v___x_2501_ = l_Lean_Syntax_node1(v___x_2476_, v___x_2480_, v___x_2500_);
v___x_2502_ = l_Lean_Syntax_node2(v___x_2476_, v___x_2477_, v___x_2479_, v___x_2501_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2502_);
v___x_2504_ = v___x_2472_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
else
{
lean_dec_ref(v_handlers_2378_);
return v___x_2469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___boxed(lean_object* v_handlers_2507_, lean_object* v_default_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_handlers_2507_, v_default_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec_ref(v_handlers_2507_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object* v_e_2515_, lean_object* v___y_2516_){
_start:
{
uint8_t v___x_2518_; 
v___x_2518_ = l_Lean_Expr_hasMVar(v_e_2515_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2519_, 0, v_e_2515_);
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; lean_object* v_mctx_2521_; lean_object* v___x_2522_; lean_object* v_fst_2523_; lean_object* v_snd_2524_; lean_object* v___x_2525_; lean_object* v_cache_2526_; lean_object* v_zetaDeltaFVarIds_2527_; lean_object* v_postponed_2528_; lean_object* v_diag_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2538_; 
v___x_2520_ = lean_st_ref_get(v___y_2516_);
v_mctx_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc_ref(v_mctx_2521_);
lean_dec(v___x_2520_);
v___x_2522_ = l_Lean_instantiateMVarsCore(v_mctx_2521_, v_e_2515_);
v_fst_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_fst_2523_);
v_snd_2524_ = lean_ctor_get(v___x_2522_, 1);
lean_inc(v_snd_2524_);
lean_dec_ref(v___x_2522_);
v___x_2525_ = lean_st_ref_take(v___y_2516_);
v_cache_2526_ = lean_ctor_get(v___x_2525_, 1);
v_zetaDeltaFVarIds_2527_ = lean_ctor_get(v___x_2525_, 2);
v_postponed_2528_ = lean_ctor_get(v___x_2525_, 3);
v_diag_2529_ = lean_ctor_get(v___x_2525_, 4);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v___x_2525_, 0);
lean_dec(v_unused_2539_);
v___x_2531_ = v___x_2525_;
v_isShared_2532_ = v_isSharedCheck_2538_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_diag_2529_);
lean_inc(v_postponed_2528_);
lean_inc(v_zetaDeltaFVarIds_2527_);
lean_inc(v_cache_2526_);
lean_dec(v___x_2525_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2538_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v_snd_2524_);
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_snd_2524_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_cache_2526_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_zetaDeltaFVarIds_2527_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_postponed_2528_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v_diag_2529_);
v___x_2534_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_st_ref_set(v___y_2516_, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_fst_2523_);
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg___boxed(lean_object* v_e_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2540_, v___y_2541_);
lean_dec(v___y_2541_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(lean_object* v_e_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_e_2544_, v___y_2550_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___boxed(lean_object* v_e_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0(v_e_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(lean_object* v_x_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; 
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc(v___y_2568_);
lean_inc_ref(v___y_2567_);
v___x_2576_ = lean_apply_9(v_x_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, lean_box(0));
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed(lean_object* v_x_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0(v_x_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(lean_object* v_mvarId_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___f_2599_; lean_object* v___x_2600_; 
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
v___f_2599_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2599_, 0, v_x_2589_);
lean_closure_set(v___f_2599_, 1, v___y_2590_);
lean_closure_set(v___f_2599_, 2, v___y_2591_);
lean_closure_set(v___f_2599_, 3, v___y_2592_);
lean_closure_set(v___f_2599_, 4, v___y_2593_);
v___x_2600_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2588_, v___f_2599_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
if (lean_obj_tag(v___x_2600_) == 0)
{
return v___x_2600_;
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2600_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg___boxed(lean_object* v_mvarId_2609_, lean_object* v_x_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2609_, v_x_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(lean_object* v_00_u03b1_2621_, lean_object* v_mvarId_2622_, lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_mvarId_2622_, v_x_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___boxed(lean_object* v_00_u03b1_2634_, lean_object* v_mvarId_2635_, lean_object* v_x_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5(v_00_u03b1_2634_, v_mvarId_2635_, v_x_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(lean_object* v_a_2647_, lean_object* v_inv_2648_, lean_object* v_xs_2649_, uint8_t v___x_2650_, lean_object* v___x_2651_, lean_object* v_letMuts_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
lean_inc_ref(v_letMuts_2652_);
lean_inc_ref(v_xs_2649_);
v___x_2662_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints(v_a_2647_, v_inv_2648_, v_xs_2649_, v_letMuts_2652_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2739_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2739_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2739_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
if (lean_obj_tag(v_a_2663_) == 1)
{
lean_object* v_val_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2734_; 
lean_del_object(v___x_2665_);
v_val_2667_ = lean_ctor_get(v_a_2663_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2669_ = v_a_2663_;
v_isShared_2670_ = v_isSharedCheck_2734_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_val_2667_);
lean_dec(v_a_2663_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2734_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v_snd_2671_; lean_object* v_fst_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2733_; 
v_snd_2671_ = lean_ctor_get(v_val_2667_, 1);
v_fst_2672_ = lean_ctor_get(v_val_2667_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_val_2667_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2674_ = v_val_2667_;
v_isShared_2675_ = v_isSharedCheck_2733_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_snd_2671_);
lean_inc(v_fst_2672_);
lean_dec(v_val_2667_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2733_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_fst_2676_; lean_object* v_snd_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2732_; 
v_fst_2676_ = lean_ctor_get(v_snd_2671_, 0);
v_snd_2677_ = lean_ctor_get(v_snd_2671_, 1);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_snd_2671_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2679_ = v_snd_2671_;
v_isShared_2680_ = v_isSharedCheck_2732_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_snd_2677_);
lean_inc(v_fst_2676_);
lean_dec(v_snd_2671_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2732_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v_lvl_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; 
v_lvl_2681_ = lean_ctor_get(v_fst_2672_, 0);
lean_inc(v_lvl_2681_);
v___x_2682_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2672_);
lean_inc(v_fst_2676_);
v___x_2683_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SuccessPoint_clause(v_fst_2676_);
v___x_2684_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_SPredNil_mkOr(v_lvl_2681_, v___x_2682_, v___x_2683_);
v___x_2685_ = lean_unsigned_to_nat(2u);
v___x_2686_ = lean_mk_empty_array_with_capacity(v___x_2685_);
v___x_2687_ = lean_array_push(v___x_2686_, v_xs_2649_);
lean_inc_ref(v_letMuts_2652_);
v___x_2688_ = lean_array_push(v___x_2687_, v_letMuts_2652_);
v___x_2689_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v___x_2684_);
v___x_2690_ = 0;
v___x_2691_ = 1;
v___x_2692_ = l_Lean_Meta_mkLambdaFVars(v___x_2688_, v___x_2689_, v___x_2690_, v___x_2650_, v___x_2690_, v___x_2650_, v___x_2691_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec_ref(v___x_2688_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v_letMutsPred_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v_letMutsPred_2694_ = lean_ctor_get(v_fst_2676_, 2);
lean_inc_ref(v_letMutsPred_2694_);
lean_dec(v_fst_2676_);
v___x_2695_ = lean_mk_empty_array_with_capacity(v___x_2651_);
v___x_2696_ = lean_array_push(v___x_2695_, v_letMuts_2652_);
v___x_2697_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_tryHoistPure(v_letMutsPred_2694_);
v___x_2698_ = l_Lean_Meta_mkLambdaFVars(v___x_2696_, v___x_2697_, v___x_2690_, v___x_2650_, v___x_2690_, v___x_2650_, v___x_2691_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec_ref(v___x_2696_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2715_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2715_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2715_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v_a_2699_);
v___x_2704_ = v___x_2679_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2699_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_snd_2677_);
v___x_2704_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 1, v___x_2704_);
lean_ctor_set(v___x_2674_, 0, v_a_2693_);
v___x_2706_ = v___x_2674_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2693_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2706_);
v___x_2708_ = v___x_2669_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2710_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___x_2708_);
v___x_2710_ = v___x_2701_;
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
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec(v_a_2693_);
lean_del_object(v___x_2679_);
lean_dec(v_snd_2677_);
lean_del_object(v___x_2674_);
lean_del_object(v___x_2669_);
v_a_2716_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2698_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2698_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_del_object(v___x_2679_);
lean_dec(v_snd_2677_);
lean_dec(v_fst_2676_);
lean_del_object(v___x_2674_);
lean_del_object(v___x_2669_);
lean_dec_ref(v_letMuts_2652_);
v_a_2724_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2692_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2692_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_dec(v_a_2663_);
lean_dec_ref(v_letMuts_2652_);
lean_dec_ref(v_xs_2649_);
v___x_2735_ = lean_box(0);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2735_);
v___x_2737_ = v___x_2665_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v_letMuts_2652_);
lean_dec_ref(v_xs_2649_);
v_a_2740_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2662_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2662_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed(lean_object* v_a_2748_, lean_object* v_inv_2749_, lean_object* v_xs_2750_, lean_object* v___x_2751_, lean_object* v___x_2752_, lean_object* v_letMuts_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
uint8_t v___x_92046__boxed_2763_; lean_object* v_res_2764_; 
v___x_92046__boxed_2763_ = lean_unbox(v___x_2751_);
v_res_2764_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0(v_a_2748_, v_inv_2749_, v_xs_2750_, v___x_92046__boxed_2763_, v___x_2752_, v_letMuts_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___x_2752_);
lean_dec_ref(v_a_2748_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(lean_object* v_k_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
lean_inc(v___y_2774_);
lean_inc_ref(v___y_2773_);
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
lean_inc(v___y_2769_);
lean_inc_ref(v___y_2768_);
lean_inc(v___y_2767_);
lean_inc_ref(v___y_2766_);
v___x_2776_ = lean_apply_10(v_k_2765_, v_b_2770_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, lean_box(0));
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v_b_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0(v_k_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v_b_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(lean_object* v_name_2789_, uint8_t v_bi_2790_, lean_object* v_type_2791_, lean_object* v_k_2792_, uint8_t v_kind_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___f_2803_; lean_object* v___x_2804_; 
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc_ref(v___y_2794_);
v___f_2803_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2803_, 0, v_k_2792_);
lean_closure_set(v___f_2803_, 1, v___y_2794_);
lean_closure_set(v___f_2803_, 2, v___y_2795_);
lean_closure_set(v___f_2803_, 3, v___y_2796_);
lean_closure_set(v___f_2803_, 4, v___y_2797_);
v___x_2804_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2789_, v_bi_2790_, v_type_2791_, v___f_2803_, v_kind_2793_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2804_) == 0)
{
return v___x_2804_;
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg___boxed(lean_object* v_name_2813_, lean_object* v_bi_2814_, lean_object* v_type_2815_, lean_object* v_k_2816_, lean_object* v_kind_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
uint8_t v_bi_boxed_2827_; uint8_t v_kind_boxed_2828_; lean_object* v_res_2829_; 
v_bi_boxed_2827_ = lean_unbox(v_bi_2814_);
v_kind_boxed_2828_ = lean_unbox(v_kind_2817_);
v_res_2829_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2813_, v_bi_boxed_2827_, v_type_2815_, v_k_2816_, v_kind_boxed_2828_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(lean_object* v_name_2830_, lean_object* v_type_2831_, lean_object* v_k_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
uint8_t v___x_2842_; uint8_t v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = 0;
v___x_2843_ = 0;
v___x_2844_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_2830_, v___x_2842_, v_type_2831_, v_k_2832_, v___x_2843_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg___boxed(lean_object* v_name_2845_, lean_object* v_type_2846_, lean_object* v_k_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_2845_, v_type_2846_, v_k_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(lean_object* v_a_2861_, lean_object* v_inv_2862_, uint8_t v___x_2863_, lean_object* v___x_2864_, lean_object* v_arg_2865_, lean_object* v_xs_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; lean_object* v___f_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2876_ = lean_box(v___x_2863_);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__0___boxed), 15, 5);
lean_closure_set(v___f_2877_, 0, v_a_2861_);
lean_closure_set(v___f_2877_, 1, v_inv_2862_);
lean_closure_set(v___f_2877_, 2, v_xs_2866_);
lean_closure_set(v___f_2877_, 3, v___x_2876_);
lean_closure_set(v___f_2877_, 4, v___x_2864_);
v___x_2878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_2879_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_2878_, v_arg_2865_, v___f_2877_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed(lean_object* v_a_2880_, lean_object* v_inv_2881_, lean_object* v___x_2882_, lean_object* v___x_2883_, lean_object* v_arg_2884_, lean_object* v_xs_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
uint8_t v___x_92366__boxed_2895_; lean_object* v_res_2896_; 
v___x_92366__boxed_2895_ = lean_unbox(v___x_2882_);
v_res_2896_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1(v_a_2880_, v_inv_2881_, v___x_92366__boxed_2895_, v___x_2883_, v_arg_2884_, v_xs_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2896_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2900_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__2);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_unsigned_to_nat(32u);
v___x_2904_ = lean_mk_empty_array_with_capacity(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(lean_object* v_fst_2906_, lean_object* v_r_2907_, uint8_t v___x_2908_, lean_object* v___x_2909_, lean_object* v___x_2910_, lean_object* v_xs_2911_, lean_object* v_fst_2912_, lean_object* v_fst_2913_, lean_object* v_letMuts_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; 
lean_inc_ref(v_fst_2906_);
v___x_2924_ = l_Lean_Meta_mkNone(v_fst_2906_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_classifyInvariantUse_spec__1___redArg___closed__2));
v___x_2927_ = lean_unsigned_to_nat(2u);
v___x_2928_ = lean_mk_empty_array_with_capacity(v___x_2927_);
lean_inc_ref(v___x_2928_);
v___x_2929_ = lean_array_push(v___x_2928_, v_a_2925_);
lean_inc_ref(v_letMuts_2914_);
v___x_2930_ = lean_array_push(v___x_2929_, v_letMuts_2914_);
v___x_2931_ = l_Lean_Meta_mkAppM(v___x_2926_, v___x_2930_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2931_, 1);
v___x_2933_ = l_Lean_Meta_mkSome(v_fst_2906_, v_r_2907_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
lean_inc_ref(v___x_2928_);
v___x_2935_ = lean_array_push(v___x_2928_, v_a_2934_);
v___x_2936_ = lean_array_push(v___x_2935_, v_letMuts_2914_);
v___x_2937_ = l_Lean_Meta_mkAppM(v___x_2926_, v___x_2936_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2939_ = l_Lean_Meta_getSimpTheorems___redArg(v___y_2922_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2922_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; uint8_t v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v___x_2943_ = lean_unsigned_to_nat(100000u);
v___x_2944_ = 0;
v___x_2945_ = 0;
v___x_2946_ = lean_box(0);
v___x_2947_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2947_, 0, v___x_2943_);
lean_ctor_set(v___x_2947_, 1, v___x_2927_);
lean_ctor_set(v___x_2947_, 2, v___x_2946_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 1, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 2, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 3, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 4, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 5, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 6, v___x_2945_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 7, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 8, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 9, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 10, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 11, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 12, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 13, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 14, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 15, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 16, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 17, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 18, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 19, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 20, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 21, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 22, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 23, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 24, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 25, v___x_2908_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 26, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 27, v___x_2944_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 28, v___x_2944_);
v___x_2948_ = lean_mk_empty_array_with_capacity(v___x_2909_);
lean_inc_ref(v___x_2948_);
v___x_2949_ = lean_array_push(v___x_2948_, v_a_2940_);
v___x_2950_ = l_Lean_Options_empty;
v___x_2951_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2947_, v___x_2949_, v_a_2942_, v___x_2950_, v___y_2919_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = lean_mk_empty_array_with_capacity(v___x_2910_);
v___x_2954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__1));
v___x_2955_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_2953_, v___x_2954_, v___x_2944_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; size_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc_n(v_a_2956_, 2);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = lean_array_push(v___x_2928_, v_xs_2911_);
v___x_2958_ = lean_array_push(v___x_2957_, v_a_2932_);
v___x_2959_ = l_Lean_Expr_beta(v_fst_2912_, v___x_2958_);
v___x_2960_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__3);
lean_inc_n(v___x_2910_, 2);
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v___x_2910_);
v___x_2962_ = lean_unsigned_to_nat(32u);
v___x_2963_ = lean_mk_empty_array_with_capacity(v___x_2962_);
v___x_2964_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___closed__4);
v___x_2965_ = ((size_t)5ULL);
v___x_2966_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2963_);
lean_ctor_set(v___x_2966_, 2, v___x_2910_);
lean_ctor_set(v___x_2966_, 3, v___x_2910_);
lean_ctor_set_usize(v___x_2966_, 4, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2960_);
lean_ctor_set(v___x_2967_, 1, v___x_2960_);
lean_ctor_set(v___x_2967_, 2, v___x_2960_);
lean_ctor_set(v___x_2967_, 3, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2961_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
lean_inc(v_a_2952_);
v___x_2969_ = l_Lean_Meta_simp(v___x_2959_, v_a_2952_, v_a_2956_, v___x_2946_, v___x_2968_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v_fst_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v_fst_2971_ = lean_ctor_get(v_a_2970_, 0);
lean_inc(v_fst_2971_);
lean_dec(v_a_2970_);
v___x_2972_ = lean_array_push(v___x_2948_, v_a_2938_);
v___x_2973_ = l_Lean_Expr_beta(v_fst_2913_, v___x_2972_);
v___x_2974_ = l_Lean_Meta_simp(v___x_2973_, v_a_2952_, v_a_2956_, v___x_2946_, v___x_2968_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec_ref_known(v___x_2968_, 2);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v_fst_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3013_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v_fst_2976_ = lean_ctor_get(v_a_2975_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_a_2975_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v_a_2975_, 1);
lean_dec(v_unused_3014_);
v___x_2978_ = v_a_2975_;
v_isShared_2979_ = v_isSharedCheck_3013_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_fst_2976_);
lean_dec(v_a_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3013_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v_expr_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_expr_2980_ = lean_ctor_get(v_fst_2971_, 0);
lean_inc_ref(v_expr_2980_);
lean_dec(v_fst_2971_);
v___x_2981_ = lean_box(1);
v___x_2982_ = l_Lean_PrettyPrinter_delab(v_expr_2980_, v___x_2981_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v_expr_2984_; lean_object* v___x_2985_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v_expr_2984_ = lean_ctor_get(v_fst_2976_, 0);
lean_inc_ref(v_expr_2984_);
lean_dec(v_fst_2976_);
v___x_2985_ = l_Lean_PrettyPrinter_delab(v_expr_2984_, v___x_2981_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2996_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2996_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2996_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v_a_2986_);
lean_ctor_set(v___x_2978_, 0, v_a_2983_);
v___x_2991_ = v___x_2978_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2983_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2993_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_2991_);
v___x_2993_ = v___x_2988_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec(v_a_2983_);
lean_del_object(v___x_2978_);
v_a_2997_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2985_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2985_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_del_object(v___x_2978_);
lean_dec(v_fst_2976_);
v_a_3005_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2982_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2982_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v_fst_2971_);
v_a_3015_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2974_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2974_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref_known(v___x_2968_, 2);
lean_dec(v_a_2956_);
lean_dec(v_a_2952_);
lean_dec_ref(v___x_2948_);
lean_dec(v_a_2938_);
lean_dec_ref(v_fst_2913_);
v_a_3023_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2969_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2969_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v_a_2952_);
lean_dec_ref(v___x_2948_);
lean_dec(v_a_2938_);
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_fst_2913_);
lean_dec_ref(v_fst_2912_);
lean_dec_ref(v_xs_2911_);
lean_dec(v___x_2910_);
v_a_3031_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_2955_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_2955_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v___x_2948_);
lean_dec(v_a_2938_);
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_fst_2913_);
lean_dec_ref(v_fst_2912_);
lean_dec_ref(v_xs_2911_);
lean_dec(v___x_2910_);
v_a_3039_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_2951_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_2951_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v_a_2940_);
lean_dec(v_a_2938_);
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_fst_2913_);
lean_dec_ref(v_fst_2912_);
lean_dec_ref(v_xs_2911_);
lean_dec(v___x_2910_);
v_a_3047_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_2941_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_2941_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_a_2938_);
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_fst_2913_);
lean_dec_ref(v_fst_2912_);
lean_dec_ref(v_xs_2911_);
lean_dec(v___x_2910_);
v_a_3055_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_2939_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_2939_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_fst_2913_);
lean_dec_ref(v_fst_2912_);
lean_dec_ref(v_xs_2911_);
lean_dec(v___x_2910_);
v_a_3063_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2937_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2937_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v_a_2932_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_letMuts_2914_);
lean_dec_ref(v_fst_2913_);
lean_dec_ref(v_fst_2912_);
lean_dec_ref(v_xs_2911_);
lean_dec(v___x_2910_);
v_a_3071_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2933_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2933_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_letMuts_2914_);
lean_dec_ref(v_fst_2913_);
lean_dec_ref(v_fst_2912_);
lean_dec_ref(v_xs_2911_);
lean_dec(v___x_2910_);
lean_dec_ref(v_r_2907_);
lean_dec_ref(v_fst_2906_);
v_a_3079_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2931_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2931_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref(v_letMuts_2914_);
lean_dec_ref(v_fst_2913_);
lean_dec_ref(v_fst_2912_);
lean_dec_ref(v_xs_2911_);
lean_dec(v___x_2910_);
lean_dec_ref(v_r_2907_);
lean_dec_ref(v_fst_2906_);
v_a_3087_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_2924_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_2924_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed(lean_object** _args){
lean_object* v_fst_3095_ = _args[0];
lean_object* v_r_3096_ = _args[1];
lean_object* v___x_3097_ = _args[2];
lean_object* v___x_3098_ = _args[3];
lean_object* v___x_3099_ = _args[4];
lean_object* v_xs_3100_ = _args[5];
lean_object* v_fst_3101_ = _args[6];
lean_object* v_fst_3102_ = _args[7];
lean_object* v_letMuts_3103_ = _args[8];
lean_object* v___y_3104_ = _args[9];
lean_object* v___y_3105_ = _args[10];
lean_object* v___y_3106_ = _args[11];
lean_object* v___y_3107_ = _args[12];
lean_object* v___y_3108_ = _args[13];
lean_object* v___y_3109_ = _args[14];
lean_object* v___y_3110_ = _args[15];
lean_object* v___y_3111_ = _args[16];
lean_object* v___y_3112_ = _args[17];
_start:
{
uint8_t v___x_92439__boxed_3113_; lean_object* v_res_3114_; 
v___x_92439__boxed_3113_ = lean_unbox(v___x_3097_);
v_res_3114_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2(v_fst_3095_, v_r_3096_, v___x_92439__boxed_3113_, v___x_3098_, v___x_3099_, v_xs_3100_, v_fst_3101_, v_fst_3102_, v_letMuts_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___x_3098_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(lean_object* v_fst_3115_, uint8_t v___x_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v_xs_3119_, lean_object* v_fst_3120_, lean_object* v_fst_3121_, lean_object* v_snd_3122_, lean_object* v_r_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; lean_object* v___f_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3133_ = lean_box(v___x_3116_);
v___f_3134_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__2___boxed), 18, 8);
lean_closure_set(v___f_3134_, 0, v_fst_3115_);
lean_closure_set(v___f_3134_, 1, v_r_3123_);
lean_closure_set(v___f_3134_, 2, v___x_3133_);
lean_closure_set(v___f_3134_, 3, v___x_3117_);
lean_closure_set(v___f_3134_, 4, v___x_3118_);
lean_closure_set(v___f_3134_, 5, v_xs_3119_);
lean_closure_set(v___f_3134_, 6, v_fst_3120_);
lean_closure_set(v___f_3134_, 7, v_fst_3121_);
v___x_3135_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3136_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3135_, v_snd_3122_, v___f_3134_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed(lean_object** _args){
lean_object* v_fst_3137_ = _args[0];
lean_object* v___x_3138_ = _args[1];
lean_object* v___x_3139_ = _args[2];
lean_object* v___x_3140_ = _args[3];
lean_object* v_xs_3141_ = _args[4];
lean_object* v_fst_3142_ = _args[5];
lean_object* v_fst_3143_ = _args[6];
lean_object* v_snd_3144_ = _args[7];
lean_object* v_r_3145_ = _args[8];
lean_object* v___y_3146_ = _args[9];
lean_object* v___y_3147_ = _args[10];
lean_object* v___y_3148_ = _args[11];
lean_object* v___y_3149_ = _args[12];
lean_object* v___y_3150_ = _args[13];
lean_object* v___y_3151_ = _args[14];
lean_object* v___y_3152_ = _args[15];
lean_object* v___y_3153_ = _args[16];
lean_object* v___y_3154_ = _args[17];
_start:
{
uint8_t v___x_92835__boxed_3155_; lean_object* v_res_3156_; 
v___x_92835__boxed_3155_ = lean_unbox(v___x_3138_);
v_res_3156_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3(v_fst_3137_, v___x_92835__boxed_3155_, v___x_3139_, v___x_3140_, v_xs_3141_, v_fst_3142_, v_fst_3143_, v_snd_3144_, v_r_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(lean_object* v_fst_3160_, uint8_t v___x_3161_, lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_fst_3164_, lean_object* v_fst_3165_, lean_object* v_snd_3166_, lean_object* v_xs_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3177_ = lean_box(v___x_3161_);
lean_inc_ref(v_fst_3160_);
v___f_3178_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__3___boxed), 18, 8);
lean_closure_set(v___f_3178_, 0, v_fst_3160_);
lean_closure_set(v___f_3178_, 1, v___x_3177_);
lean_closure_set(v___f_3178_, 2, v___x_3162_);
lean_closure_set(v___f_3178_, 3, v___x_3163_);
lean_closure_set(v___f_3178_, 4, v_xs_3167_);
lean_closure_set(v___f_3178_, 5, v_fst_3164_);
lean_closure_set(v___f_3178_, 6, v_fst_3165_);
lean_closure_set(v___f_3178_, 7, v_snd_3166_);
v___x_3179_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_3180_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3179_, v_fst_3160_, v___f_3178_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed(lean_object** _args){
lean_object* v_fst_3181_ = _args[0];
lean_object* v___x_3182_ = _args[1];
lean_object* v___x_3183_ = _args[2];
lean_object* v___x_3184_ = _args[3];
lean_object* v_fst_3185_ = _args[4];
lean_object* v_fst_3186_ = _args[5];
lean_object* v_snd_3187_ = _args[6];
lean_object* v_xs_3188_ = _args[7];
lean_object* v___y_3189_ = _args[8];
lean_object* v___y_3190_ = _args[9];
lean_object* v___y_3191_ = _args[10];
lean_object* v___y_3192_ = _args[11];
lean_object* v___y_3193_ = _args[12];
lean_object* v___y_3194_ = _args[13];
lean_object* v___y_3195_ = _args[14];
lean_object* v___y_3196_ = _args[15];
lean_object* v___y_3197_ = _args[16];
_start:
{
uint8_t v___x_92898__boxed_3198_; lean_object* v_res_3199_; 
v___x_92898__boxed_3198_ = lean_unbox(v___x_3182_);
v_res_3199_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4(v_fst_3181_, v___x_92898__boxed_3198_, v___x_3183_, v___x_3184_, v_fst_3185_, v_fst_3186_, v_snd_3187_, v_xs_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(lean_object* v_as_3200_, size_t v_sz_3201_, size_t v_i_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v___x_3209_; 
v___x_3209_ = lean_usize_dec_lt(v_i_3202_, v_sz_3201_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_b_3203_);
return v___x_3210_;
}
else
{
lean_object* v___x_3211_; lean_object* v_a_3212_; lean_object* v___x_3213_; 
v___x_3211_ = lean_box(1);
v_a_3212_ = lean_array_uget_borrowed(v_as_3200_, v_i_3202_);
lean_inc(v_a_3212_);
v___x_3213_ = l_Lean_PrettyPrinter_delab(v_a_3212_, v___x_3211_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3215_; size_t v___x_3216_; size_t v___x_3217_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = lean_array_push(v_b_3203_, v_a_3214_);
v___x_3216_ = ((size_t)1ULL);
v___x_3217_ = lean_usize_add(v_i_3202_, v___x_3216_);
v_i_3202_ = v___x_3217_;
v_b_3203_ = v___x_3215_;
goto _start;
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v_b_3203_);
v_a_3219_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3213_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3213_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg___boxed(lean_object* v_as_3227_, lean_object* v_sz_3228_, lean_object* v_i_3229_, lean_object* v_b_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
size_t v_sz_boxed_3236_; size_t v_i_boxed_3237_; lean_object* v_res_3238_; 
v_sz_boxed_3236_ = lean_unbox_usize(v_sz_3228_);
lean_dec(v_sz_3228_);
v_i_boxed_3237_ = lean_unbox_usize(v_i_3229_);
lean_dec(v_i_3229_);
v_res_3238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_3227_, v_sz_boxed_3236_, v_i_boxed_3237_, v_b_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec_ref(v_as_3227_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(lean_object* v_xs_3259_, lean_object* v_fst_3260_, lean_object* v_snd_3261_, lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v___x_3266_, lean_object* v___x_3267_, lean_object* v___x_3268_, uint8_t v___x_3269_, lean_object* v___x_3270_, lean_object* v_letMuts_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3281_ = lean_unsigned_to_nat(2u);
v___x_3282_ = lean_mk_empty_array_with_capacity(v___x_3281_);
v___x_3283_ = lean_array_push(v___x_3282_, v_xs_3259_);
v___x_3284_ = lean_array_push(v___x_3283_, v_letMuts_3271_);
v___x_3285_ = l_Lean_Expr_beta(v_fst_3260_, v___x_3284_);
v___x_3286_ = lean_box(1);
v___x_3287_ = l_Lean_PrettyPrinter_delab(v___x_3285_, v___x_3286_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3426_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3426_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3426_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
uint8_t v___y_3293_; lean_object* v_points_3329_; lean_object* v_default_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3425_; 
v_points_3329_ = lean_ctor_get(v_snd_3261_, 0);
v_default_3330_ = lean_ctor_get(v_snd_3261_, 1);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_snd_3261_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3332_ = v_snd_3261_;
v_isShared_3333_ = v_isSharedCheck_3425_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_default_3330_);
lean_inc(v_points_3329_);
lean_dec(v_snd_3261_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3425_;
goto v_resetjp_3331_;
}
v___jp_3292_:
{
lean_object* v_ref_3294_; lean_object* v_quotContext_3295_; lean_object* v_currMacroScope_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3327_; 
v_ref_3294_ = lean_ctor_get(v___y_3278_, 5);
v_quotContext_3295_ = lean_ctor_get(v___y_3278_, 10);
v_currMacroScope_3296_ = lean_ctor_get(v___y_3278_, 11);
v___x_3297_ = l_Lean_SourceInfo_fromRef(v_ref_3294_, v___y_3293_);
v___x_3298_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_3299_ = l_Lean_Name_mkStr3(v___x_3262_, v___x_3263_, v___x_3298_);
v___x_3300_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3301_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3297_, 11);
v___x_3302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3297_);
lean_ctor_set(v___x_3302_, 1, v___x_3300_);
lean_ctor_set(v___x_3302_, 2, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_3304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3297_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3297_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_String_toRawSubstring_x27(v___x_3264_);
lean_inc_n(v_currMacroScope_3296_, 2);
lean_inc_n(v_quotContext_3295_, 2);
v___x_3310_ = l_Lean_addMacroScope(v_quotContext_3295_, v___x_3265_, v_currMacroScope_3296_);
v___x_3311_ = lean_box(0);
v___x_3312_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3297_);
lean_ctor_set(v___x_3312_, 1, v___x_3309_);
lean_ctor_set(v___x_3312_, 2, v___x_3310_);
lean_ctor_set(v___x_3312_, 3, v___x_3311_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3297_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = l_String_toRawSubstring_x27(v___x_3266_);
v___x_3316_ = l_Lean_addMacroScope(v_quotContext_3295_, v___x_3267_, v_currMacroScope_3296_);
v___x_3317_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3297_);
lean_ctor_set(v___x_3317_, 1, v___x_3315_);
lean_ctor_set(v___x_3317_, 2, v___x_3316_);
lean_ctor_set(v___x_3317_, 3, v___x_3311_);
v___x_3318_ = l_Lean_Syntax_node3(v___x_3297_, v___x_3305_, v___x_3312_, v___x_3314_, v___x_3317_);
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3297_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = l_Lean_Syntax_node3(v___x_3297_, v___x_3306_, v___x_3308_, v___x_3318_, v___x_3320_);
v___x_3322_ = l_Lean_Syntax_node1(v___x_3297_, v___x_3305_, v___x_3321_);
v___x_3323_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3297_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = l_Lean_Syntax_node5(v___x_3297_, v___x_3299_, v___x_3302_, v___x_3304_, v___x_3322_, v___x_3324_, v_a_3288_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3325_);
v___x_3327_ = v___x_3290_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
v_resetjp_3331_:
{
uint8_t v___y_3335_; uint8_t v___y_3386_; lean_object* v___x_3422_; uint8_t v___x_3423_; 
v___x_3422_ = lean_array_get_size(v_points_3329_);
v___x_3423_ = lean_nat_dec_eq(v___x_3422_, v___x_3270_);
if (v___x_3423_ == 0)
{
v___y_3386_ = v___x_3423_;
goto v___jp_3385_;
}
else
{
if (lean_obj_tag(v_default_3330_) == 3)
{
if (v___x_3423_ == 0)
{
v___y_3386_ = v___x_3423_;
goto v___jp_3385_;
}
else
{
uint8_t v___x_3424_; 
lean_del_object(v___x_3290_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___x_3262_);
v___x_3424_ = 0;
v___y_3335_ = v___x_3424_;
goto v___jp_3334_;
}
}
else
{
v___y_3386_ = v___x_3423_;
goto v___jp_3385_;
}
}
v___jp_3334_:
{
lean_object* v_ref_3336_; lean_object* v_quotContext_3337_; lean_object* v_currMacroScope_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
v_ref_3336_ = lean_ctor_get(v___y_3278_, 5);
v_quotContext_3337_ = lean_ctor_get(v___y_3278_, 10);
v_currMacroScope_3338_ = lean_ctor_get(v___y_3278_, 11);
v___x_3339_ = l_Lean_SourceInfo_fromRef(v_ref_3336_, v___y_3335_);
v___x_3340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3341_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc(v___x_3339_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 2);
lean_ctor_set(v___x_3332_, 1, v___x_3340_);
lean_ctor_set(v___x_3332_, 0, v___x_3339_);
v___x_3343_ = v___x_3332_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3340_);
v___x_3343_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; size_t v_sz_3371_; size_t v___x_3372_; lean_object* v___x_3373_; 
v___x_3344_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
lean_inc_n(v___x_3339_, 11);
v___x_3348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3339_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = l_String_toRawSubstring_x27(v___x_3264_);
lean_inc_n(v_currMacroScope_3338_, 2);
lean_inc_n(v_quotContext_3337_, 2);
v___x_3350_ = l_Lean_addMacroScope(v_quotContext_3337_, v___x_3265_, v_currMacroScope_3338_);
v___x_3351_ = lean_box(0);
v___x_3352_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3339_);
lean_ctor_set(v___x_3352_, 1, v___x_3349_);
lean_ctor_set(v___x_3352_, 2, v___x_3350_);
lean_ctor_set(v___x_3352_, 3, v___x_3351_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3339_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l_String_toRawSubstring_x27(v___x_3266_);
v___x_3356_ = l_Lean_addMacroScope(v_quotContext_3337_, v___x_3267_, v_currMacroScope_3338_);
v___x_3357_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3339_);
lean_ctor_set(v___x_3357_, 1, v___x_3355_);
lean_ctor_set(v___x_3357_, 2, v___x_3356_);
lean_ctor_set(v___x_3357_, 3, v___x_3351_);
v___x_3358_ = l_Lean_Syntax_node3(v___x_3339_, v___x_3345_, v___x_3352_, v___x_3354_, v___x_3357_);
v___x_3359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3339_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = l_Lean_Syntax_node3(v___x_3339_, v___x_3346_, v___x_3348_, v___x_3358_, v___x_3360_);
v___x_3362_ = l_Lean_Syntax_node1(v___x_3339_, v___x_3345_, v___x_3361_);
v___x_3363_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3339_);
lean_ctor_set(v___x_3364_, 1, v___x_3345_);
lean_ctor_set(v___x_3364_, 2, v___x_3363_);
v___x_3365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3339_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_Syntax_node4(v___x_3339_, v___x_3344_, v___x_3362_, v___x_3364_, v___x_3366_, v_a_3288_);
v___x_3368_ = l_Lean_Syntax_node2(v___x_3339_, v___x_3341_, v___x_3343_, v___x_3367_);
v___x_3369_ = lean_mk_empty_array_with_capacity(v___x_3268_);
v___x_3370_ = lean_array_push(v___x_3369_, v___x_3368_);
v_sz_3371_ = lean_array_size(v_points_3329_);
v___x_3372_ = ((size_t)0ULL);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_points_3329_, v_sz_3371_, v___x_3372_, v___x_3370_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec_ref(v_points_3329_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
v___x_3375_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3374_, v_default_3330_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec(v_a_3374_);
return v___x_3375_;
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v_default_3330_);
v_a_3376_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3373_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3373_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
v___jp_3385_:
{
if (v___y_3386_ == 0)
{
lean_del_object(v___x_3290_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___x_3262_);
v___y_3335_ = v___y_3386_;
goto v___jp_3334_;
}
else
{
lean_del_object(v___x_3332_);
lean_dec_ref(v_points_3329_);
if (lean_obj_tag(v_default_3330_) == 2)
{
if (v___x_3269_ == 0)
{
v___y_3293_ = v___x_3269_;
goto v___jp_3292_;
}
else
{
lean_object* v_ref_3387_; lean_object* v_quotContext_3388_; lean_object* v_currMacroScope_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
lean_del_object(v___x_3290_);
v_ref_3387_ = lean_ctor_get(v___y_3278_, 5);
v_quotContext_3388_ = lean_ctor_get(v___y_3278_, 10);
v_currMacroScope_3389_ = lean_ctor_get(v___y_3278_, 11);
v___x_3390_ = 0;
v___x_3391_ = l_Lean_SourceInfo_fromRef(v_ref_3387_, v___x_3390_);
v___x_3392_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__9));
v___x_3393_ = l_Lean_Name_mkStr3(v___x_3262_, v___x_3263_, v___x_3392_);
v___x_3394_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_3395_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_3391_, 11);
v___x_3396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3391_);
lean_ctor_set(v___x_3396_, 1, v___x_3394_);
lean_ctor_set(v___x_3396_, 2, v___x_3395_);
v___x_3397_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__10));
v___x_3398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3391_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_3401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_3402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3391_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = l_String_toRawSubstring_x27(v___x_3264_);
lean_inc_n(v_currMacroScope_3389_, 2);
lean_inc_n(v_quotContext_3388_, 2);
v___x_3404_ = l_Lean_addMacroScope(v_quotContext_3388_, v___x_3265_, v_currMacroScope_3389_);
v___x_3405_ = lean_box(0);
v___x_3406_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3391_);
lean_ctor_set(v___x_3406_, 1, v___x_3403_);
lean_ctor_set(v___x_3406_, 2, v___x_3404_);
lean_ctor_set(v___x_3406_, 3, v___x_3405_);
v___x_3407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_3408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3391_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = l_String_toRawSubstring_x27(v___x_3266_);
v___x_3410_ = l_Lean_addMacroScope(v_quotContext_3388_, v___x_3267_, v_currMacroScope_3389_);
v___x_3411_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3391_);
lean_ctor_set(v___x_3411_, 1, v___x_3409_);
lean_ctor_set(v___x_3411_, 2, v___x_3410_);
lean_ctor_set(v___x_3411_, 3, v___x_3405_);
v___x_3412_ = l_Lean_Syntax_node3(v___x_3391_, v___x_3399_, v___x_3406_, v___x_3408_, v___x_3411_);
v___x_3413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_3414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3391_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v___x_3415_ = l_Lean_Syntax_node3(v___x_3391_, v___x_3400_, v___x_3402_, v___x_3412_, v___x_3414_);
v___x_3416_ = l_Lean_Syntax_node1(v___x_3391_, v___x_3399_, v___x_3415_);
v___x_3417_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3391_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = l_Lean_Syntax_node5(v___x_3391_, v___x_3393_, v___x_3396_, v___x_3398_, v___x_3416_, v___x_3418_, v_a_3288_);
v___x_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
return v___x_3420_;
}
}
else
{
uint8_t v___x_3421_; 
lean_dec(v_default_3330_);
v___x_3421_ = 0;
v___y_3293_ = v___x_3421_;
goto v___jp_3292_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3267_);
lean_dec_ref(v___x_3266_);
lean_dec(v___x_3265_);
lean_dec_ref(v___x_3264_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___x_3262_);
lean_dec_ref(v_snd_3261_);
return v___x_3287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed(lean_object** _args){
lean_object* v_xs_3427_ = _args[0];
lean_object* v_fst_3428_ = _args[1];
lean_object* v_snd_3429_ = _args[2];
lean_object* v___x_3430_ = _args[3];
lean_object* v___x_3431_ = _args[4];
lean_object* v___x_3432_ = _args[5];
lean_object* v___x_3433_ = _args[6];
lean_object* v___x_3434_ = _args[7];
lean_object* v___x_3435_ = _args[8];
lean_object* v___x_3436_ = _args[9];
lean_object* v___x_3437_ = _args[10];
lean_object* v___x_3438_ = _args[11];
lean_object* v_letMuts_3439_ = _args[12];
lean_object* v___y_3440_ = _args[13];
lean_object* v___y_3441_ = _args[14];
lean_object* v___y_3442_ = _args[15];
lean_object* v___y_3443_ = _args[16];
lean_object* v___y_3444_ = _args[17];
lean_object* v___y_3445_ = _args[18];
lean_object* v___y_3446_ = _args[19];
lean_object* v___y_3447_ = _args[20];
lean_object* v___y_3448_ = _args[21];
_start:
{
uint8_t v___x_93107__boxed_3449_; lean_object* v_res_3450_; 
v___x_93107__boxed_3449_ = lean_unbox(v___x_3437_);
v_res_3450_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5(v_xs_3427_, v_fst_3428_, v_snd_3429_, v___x_3430_, v___x_3431_, v___x_3432_, v___x_3433_, v___x_3434_, v___x_3435_, v___x_3436_, v___x_93107__boxed_3449_, v___x_3438_, v_letMuts_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___x_3438_);
lean_dec(v___x_3436_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(lean_object* v_fst_3451_, lean_object* v_snd_3452_, lean_object* v___x_3453_, lean_object* v___x_3454_, lean_object* v___x_3455_, lean_object* v___x_3456_, lean_object* v___x_3457_, uint8_t v___x_3458_, lean_object* v___x_3459_, lean_object* v_arg_3460_, lean_object* v_xs_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___f_3474_; lean_object* v___x_3475_; 
v___x_3471_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3472_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3473_ = lean_box(v___x_3458_);
v___f_3474_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___boxed), 22, 12);
lean_closure_set(v___f_3474_, 0, v_xs_3461_);
lean_closure_set(v___f_3474_, 1, v_fst_3451_);
lean_closure_set(v___f_3474_, 2, v_snd_3452_);
lean_closure_set(v___f_3474_, 3, v___x_3453_);
lean_closure_set(v___f_3474_, 4, v___x_3454_);
lean_closure_set(v___f_3474_, 5, v___x_3455_);
lean_closure_set(v___f_3474_, 6, v___x_3456_);
lean_closure_set(v___f_3474_, 7, v___x_3471_);
lean_closure_set(v___f_3474_, 8, v___x_3472_);
lean_closure_set(v___f_3474_, 9, v___x_3457_);
lean_closure_set(v___f_3474_, 10, v___x_3473_);
lean_closure_set(v___f_3474_, 11, v___x_3459_);
v___x_3475_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3472_, v_arg_3460_, v___f_3474_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed(lean_object** _args){
lean_object* v_fst_3476_ = _args[0];
lean_object* v_snd_3477_ = _args[1];
lean_object* v___x_3478_ = _args[2];
lean_object* v___x_3479_ = _args[3];
lean_object* v___x_3480_ = _args[4];
lean_object* v___x_3481_ = _args[5];
lean_object* v___x_3482_ = _args[6];
lean_object* v___x_3483_ = _args[7];
lean_object* v___x_3484_ = _args[8];
lean_object* v_arg_3485_ = _args[9];
lean_object* v_xs_3486_ = _args[10];
lean_object* v___y_3487_ = _args[11];
lean_object* v___y_3488_ = _args[12];
lean_object* v___y_3489_ = _args[13];
lean_object* v___y_3490_ = _args[14];
lean_object* v___y_3491_ = _args[15];
lean_object* v___y_3492_ = _args[16];
lean_object* v___y_3493_ = _args[17];
lean_object* v___y_3494_ = _args[18];
lean_object* v___y_3495_ = _args[19];
_start:
{
uint8_t v___x_93457__boxed_3496_; lean_object* v_res_3497_; 
v___x_93457__boxed_3496_ = lean_unbox(v___x_3483_);
v_res_3497_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6(v_fst_3476_, v_snd_3477_, v___x_3478_, v___x_3479_, v___x_3480_, v___x_3481_, v___x_3482_, v___x_93457__boxed_3496_, v___x_3484_, v_arg_3485_, v_xs_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(lean_object* v_as_3498_, size_t v_sz_3499_, size_t v_i_3500_, lean_object* v_b_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_usize_dec_lt(v_i_3500_, v_sz_3499_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_b_3501_);
return v___x_3508_;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_a_3509_ = lean_array_uget_borrowed(v_as_3498_, v_i_3500_);
v___x_3510_ = lean_box(1);
lean_inc(v_a_3509_);
v___x_3511_ = l_Lean_PrettyPrinter_delab(v_a_3509_, v___x_3510_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; size_t v___x_3514_; size_t v___x_3515_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = lean_array_push(v_b_3501_, v_a_3512_);
v___x_3514_ = ((size_t)1ULL);
v___x_3515_ = lean_usize_add(v_i_3500_, v___x_3514_);
v_i_3500_ = v___x_3515_;
v_b_3501_ = v___x_3513_;
goto _start;
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v_b_3501_);
v_a_3517_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3511_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3511_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg___boxed(lean_object* v_as_3525_, lean_object* v_sz_3526_, lean_object* v_i_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
size_t v_sz_boxed_3534_; size_t v_i_boxed_3535_; lean_object* v_res_3536_; 
v_sz_boxed_3534_ = lean_unbox_usize(v_sz_3526_);
lean_dec(v_sz_3526_);
v_i_boxed_3535_ = lean_unbox_usize(v_i_3527_);
lean_dec(v_i_3527_);
v_res_3536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_3525_, v_sz_boxed_3534_, v_i_boxed_3535_, v_b_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec_ref(v_as_3525_);
return v_res_3536_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__2));
v___x_3545_ = l_String_toRawSubstring_x27(v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__8));
v___x_3556_ = l_String_toRawSubstring_x27(v___x_3555_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__0));
v___x_3561_ = l_String_toRawSubstring_x27(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__0));
v___x_3563_ = l_String_toRawSubstring_x27(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__15));
v___x_3567_ = l_String_toRawSubstring_x27(v___x_3566_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__18));
v___x_3572_ = l_String_toRawSubstring_x27(v___x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(lean_object* v___x_3582_, lean_object* v___x_3583_, lean_object* v___f_3584_, lean_object* v_a_3585_, lean_object* v_inv_3586_, lean_object* v_arg_3587_, uint8_t v___x_3588_, lean_object* v___x_3589_, lean_object* v___x_3590_, lean_object* v___x_3591_, lean_object* v___x_3592_, lean_object* v___x_3593_, lean_object* v___x_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_a_3605_; lean_object* v___y_3609_; lean_object* v___x_3611_; 
lean_inc_ref(v___x_3583_);
lean_inc(v___x_3582_);
v___x_3611_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3582_, v___x_3583_, v___f_3584_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3613_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
v___x_3613_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_hasEarlyReturn(v_a_3585_, v_inv_3586_, v_arg_3587_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_val_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_4095_; 
lean_dec_ref(v_arg_3587_);
v_val_3615_ = lean_ctor_get(v_a_3614_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_a_3614_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_3617_ = v_a_3614_;
v_isShared_3618_ = v_isSharedCheck_4095_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_val_3615_);
lean_dec(v_a_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_4095_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
if (lean_obj_tag(v_a_3612_) == 1)
{
lean_object* v_val_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_4018_; 
lean_del_object(v___x_3617_);
v_val_3619_ = lean_ctor_get(v_a_3612_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_a_3612_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_3621_ = v_a_3612_;
v_isShared_3622_ = v_isSharedCheck_4018_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_val_3619_);
lean_dec(v_a_3612_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_4018_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v_snd_3623_; lean_object* v_fst_3624_; lean_object* v_snd_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_4017_; 
v_snd_3623_ = lean_ctor_get(v_val_3619_, 1);
lean_inc(v_snd_3623_);
v_fst_3624_ = lean_ctor_get(v_val_3615_, 0);
v_snd_3625_ = lean_ctor_get(v_val_3615_, 1);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_val_3615_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_3627_ = v_val_3615_;
v_isShared_3628_ = v_isSharedCheck_4017_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_snd_3625_);
lean_inc(v_fst_3624_);
lean_dec(v_val_3615_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_4017_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_fst_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_4015_; 
v_fst_3629_ = lean_ctor_get(v_val_3619_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v_val_3619_);
if (v_isSharedCheck_4015_ == 0)
{
lean_object* v_unused_4016_; 
v_unused_4016_ = lean_ctor_get(v_val_3619_, 1);
lean_dec(v_unused_4016_);
v___x_3631_ = v_val_3619_;
v_isShared_3632_ = v_isSharedCheck_4015_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_fst_3629_);
lean_dec(v_val_3619_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_4015_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v_fst_3633_; lean_object* v_snd_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_4014_; 
v_fst_3633_ = lean_ctor_get(v_snd_3623_, 0);
v_snd_3634_ = lean_ctor_get(v_snd_3623_, 1);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_snd_3623_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3636_ = v_snd_3623_;
v_isShared_3637_ = v_isSharedCheck_4014_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_snd_3634_);
lean_inc(v_fst_3633_);
lean_dec(v_snd_3623_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_4014_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; lean_object* v___f_3639_; lean_object* v___x_3640_; 
v___x_3638_ = lean_box(v___x_3588_);
lean_inc(v___x_3590_);
v___f_3639_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___boxed), 17, 7);
lean_closure_set(v___f_3639_, 0, v_fst_3624_);
lean_closure_set(v___f_3639_, 1, v___x_3638_);
lean_closure_set(v___f_3639_, 2, v___x_3589_);
lean_closure_set(v___f_3639_, 3, v___x_3590_);
lean_closure_set(v___f_3639_, 4, v_fst_3629_);
lean_closure_set(v___f_3639_, 5, v_fst_3633_);
lean_closure_set(v___f_3639_, 6, v_snd_3625_);
lean_inc(v___x_3582_);
v___x_3640_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3582_, v___x_3583_, v___f_3639_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v_fst_3642_; lean_object* v_snd_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_4005_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3640_, 1);
v_fst_3642_ = lean_ctor_get(v_a_3641_, 0);
v_snd_3643_ = lean_ctor_get(v_a_3641_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_a_3641_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3645_ = v_a_3641_;
v_isShared_3646_ = v_isSharedCheck_4005_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_snd_3643_);
lean_inc(v_fst_3642_);
lean_dec(v_a_3641_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_4005_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v_points_3647_; lean_object* v_default_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_4004_; 
v_points_3647_ = lean_ctor_get(v_snd_3634_, 0);
v_default_3648_ = lean_ctor_get(v_snd_3634_, 1);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_snd_3634_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3650_ = v_snd_3634_;
v_isShared_3651_ = v_isSharedCheck_4004_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_default_3648_);
lean_inc(v_points_3647_);
lean_dec(v_snd_3634_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_4004_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; uint8_t v___x_3653_; 
v___x_3652_ = lean_array_get_size(v_points_3647_);
v___x_3653_ = lean_nat_dec_eq(v___x_3652_, v___x_3590_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; size_t v_sz_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
lean_del_object(v___x_3621_);
v___x_3654_ = lean_mk_empty_array_with_capacity(v___x_3590_);
lean_dec(v___x_3590_);
v_sz_3655_ = lean_array_size(v_points_3647_);
v___x_3656_ = ((size_t)0ULL);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_points_3647_, v_sz_3655_, v___x_3656_, v___x_3654_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec_ref(v_points_3647_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3659_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___x_3657_, 1);
v___x_3659_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions(v_a_3658_, v_default_3648_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v_a_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3742_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3742_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3742_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v_ref_3664_; lean_object* v_quotContext_3665_; lean_object* v_currMacroScope_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v_ref_3664_ = lean_ctor_get(v___y_3601_, 5);
lean_inc(v_ref_3664_);
v_quotContext_3665_ = lean_ctor_get(v___y_3601_, 10);
lean_inc_n(v_quotContext_3665_, 2);
v_currMacroScope_3666_ = lean_ctor_get(v___y_3601_, 11);
lean_inc_n(v_currMacroScope_3666_, 2);
lean_dec_ref(v___y_3601_);
v___x_3667_ = l_Lean_SourceInfo_fromRef(v_ref_3664_, v___x_3653_);
lean_dec(v_ref_3664_);
v___x_3668_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3669_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3670_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3591_);
v___x_3671_ = l_Lean_Name_mkStr2(v___x_3591_, v___x_3670_);
v___x_3672_ = l_Lean_addMacroScope(v_quotContext_3665_, v___x_3671_, v_currMacroScope_3666_);
v___x_3673_ = l_Lean_Name_mkStr4(v___x_3592_, v___x_3593_, v___x_3591_, v___x_3670_);
v___x_3674_ = lean_box(0);
lean_inc(v___x_3673_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 1);
lean_ctor_set(v___x_3650_, 1, v___x_3674_);
lean_ctor_set(v___x_3650_, 0, v___x_3673_);
v___x_3676_ = v___x_3650_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3678_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3673_);
v___x_3678_ = v___x_3662_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3673_);
v___x_3678_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3680_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3674_);
lean_ctor_set(v___x_3645_, 0, v___x_3678_);
v___x_3680_ = v___x_3645_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___x_3674_);
v___x_3680_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3682_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 1);
lean_ctor_set(v___x_3636_, 1, v___x_3680_);
lean_ctor_set(v___x_3636_, 0, v___x_3676_);
v___x_3682_ = v___x_3636_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
lean_inc_n(v___x_3667_, 2);
v___x_3683_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3667_);
lean_ctor_set(v___x_3683_, 1, v___x_3669_);
lean_ctor_set(v___x_3683_, 2, v___x_3672_);
lean_ctor_set(v___x_3683_, 3, v___x_3682_);
v___x_3684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3685_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3686_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3632_ == 0)
{
lean_ctor_set_tag(v___x_3631_, 2);
lean_ctor_set(v___x_3631_, 1, v___x_3686_);
lean_ctor_set(v___x_3631_, 0, v___x_3667_);
v___x_3688_ = v___x_3631_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3695_; 
v___x_3689_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3690_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3666_);
lean_inc(v_quotContext_3665_);
v___x_3691_ = l_Lean_addMacroScope(v_quotContext_3665_, v___x_3690_, v_currMacroScope_3666_);
lean_inc_n(v___x_3667_, 2);
v___x_3692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3667_);
lean_ctor_set(v___x_3692_, 1, v___x_3689_);
lean_ctor_set(v___x_3692_, 2, v___x_3691_);
lean_ctor_set(v___x_3692_, 3, v___x_3674_);
v___x_3693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 2);
lean_ctor_set(v___x_3627_, 1, v___x_3693_);
lean_ctor_set(v___x_3627_, 0, v___x_3667_);
v___x_3695_ = v___x_3627_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3697_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3667_, 19);
v___x_3698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3667_);
lean_ctor_set(v___x_3698_, 1, v___x_3696_);
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3700_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3701_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3666_, 4);
lean_inc_n(v_quotContext_3665_, 4);
v___x_3702_ = l_Lean_addMacroScope(v_quotContext_3665_, v___x_3701_, v_currMacroScope_3666_);
v___x_3703_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3667_);
lean_ctor_set(v___x_3703_, 1, v___x_3700_);
lean_ctor_set(v___x_3703_, 2, v___x_3702_);
lean_ctor_set(v___x_3703_, 3, v___x_3674_);
v___x_3704_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3705_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3706_ = l_Lean_addMacroScope(v_quotContext_3665_, v___x_3705_, v_currMacroScope_3666_);
v___x_3707_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3667_);
lean_ctor_set(v___x_3707_, 1, v___x_3704_);
lean_ctor_set(v___x_3707_, 2, v___x_3706_);
lean_ctor_set(v___x_3707_, 3, v___x_3674_);
lean_inc_ref(v___x_3707_);
v___x_3708_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3684_, v___x_3703_, v___x_3707_);
v___x_3709_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3667_);
lean_ctor_set(v___x_3710_, 1, v___x_3684_);
lean_ctor_set(v___x_3710_, 2, v___x_3709_);
v___x_3711_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3667_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
lean_inc_ref(v___x_3712_);
lean_inc_ref(v___x_3710_);
v___x_3713_ = l_Lean_Syntax_node4(v___x_3667_, v___x_3699_, v___x_3708_, v___x_3710_, v___x_3712_, v_snd_3643_);
lean_inc_ref(v___x_3698_);
v___x_3714_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3697_, v___x_3698_, v___x_3713_);
v___x_3715_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3667_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
lean_inc_ref_n(v___x_3716_, 2);
lean_inc_ref_n(v___x_3695_, 2);
lean_inc_ref_n(v___x_3688_, 2);
v___x_3717_ = l_Lean_Syntax_node5(v___x_3667_, v___x_3685_, v___x_3688_, v___x_3692_, v___x_3695_, v___x_3714_, v___x_3716_);
v___x_3718_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3720_ = l_Lean_addMacroScope(v_quotContext_3665_, v___x_3719_, v_currMacroScope_3666_);
v___x_3721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3667_);
lean_ctor_set(v___x_3721_, 1, v___x_3718_);
lean_ctor_set(v___x_3721_, 2, v___x_3720_);
lean_ctor_set(v___x_3721_, 3, v___x_3674_);
v___x_3722_ = l_String_toRawSubstring_x27(v___x_3594_);
v___x_3723_ = l_Lean_addMacroScope(v_quotContext_3665_, v___x_3582_, v_currMacroScope_3666_);
v___x_3724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3667_);
lean_ctor_set(v___x_3724_, 1, v___x_3722_);
lean_ctor_set(v___x_3724_, 2, v___x_3723_);
lean_ctor_set(v___x_3724_, 3, v___x_3674_);
v___x_3725_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3684_, v___x_3724_, v___x_3707_);
v___x_3726_ = l_Lean_Syntax_node4(v___x_3667_, v___x_3699_, v___x_3725_, v___x_3710_, v___x_3712_, v_fst_3642_);
v___x_3727_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3697_, v___x_3698_, v___x_3726_);
v___x_3728_ = l_Lean_Syntax_node5(v___x_3667_, v___x_3685_, v___x_3688_, v___x_3721_, v___x_3695_, v___x_3727_, v___x_3716_);
v___x_3729_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3730_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3731_ = l_Lean_addMacroScope(v_quotContext_3665_, v___x_3730_, v_currMacroScope_3666_);
v___x_3732_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3667_);
lean_ctor_set(v___x_3732_, 1, v___x_3729_);
lean_ctor_set(v___x_3732_, 2, v___x_3731_);
lean_ctor_set(v___x_3732_, 3, v___x_3674_);
v___x_3733_ = l_Lean_Syntax_node5(v___x_3667_, v___x_3685_, v___x_3688_, v___x_3732_, v___x_3695_, v_a_3660_, v___x_3716_);
v___x_3734_ = l_Lean_Syntax_node3(v___x_3667_, v___x_3684_, v___x_3717_, v___x_3728_, v___x_3733_);
v___x_3735_ = l_Lean_Syntax_node2(v___x_3667_, v___x_3668_, v___x_3683_, v___x_3734_);
v_a_3605_ = v___x_3735_;
goto v___jp_3604_;
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
lean_del_object(v___x_3650_);
lean_del_object(v___x_3645_);
lean_dec(v_snd_3643_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3636_);
lean_del_object(v___x_3631_);
lean_del_object(v___x_3627_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v___x_3592_);
lean_dec_ref(v___x_3591_);
lean_dec(v___x_3582_);
v___y_3609_ = v___x_3659_;
goto v___jp_3608_;
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_del_object(v___x_3650_);
lean_dec(v_default_3648_);
lean_del_object(v___x_3645_);
lean_dec(v_snd_3643_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3636_);
lean_del_object(v___x_3631_);
lean_del_object(v___x_3627_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v___x_3592_);
lean_dec_ref(v___x_3591_);
lean_dec(v___x_3582_);
v_a_3743_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3657_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3657_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_dec_ref(v_points_3647_);
lean_dec(v___x_3590_);
switch(lean_obj_tag(v_default_3648_))
{
case 2:
{
lean_object* v_ref_3751_; lean_object* v_quotContext_3752_; lean_object* v_currMacroScope_3753_; uint8_t v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3764_; 
v_ref_3751_ = lean_ctor_get(v___y_3601_, 5);
lean_inc(v_ref_3751_);
v_quotContext_3752_ = lean_ctor_get(v___y_3601_, 10);
lean_inc_n(v_quotContext_3752_, 2);
v_currMacroScope_3753_ = lean_ctor_get(v___y_3601_, 11);
lean_inc_n(v_currMacroScope_3753_, 2);
lean_dec_ref(v___y_3601_);
v___x_3754_ = 0;
v___x_3755_ = l_Lean_SourceInfo_fromRef(v_ref_3751_, v___x_3754_);
lean_dec(v_ref_3751_);
v___x_3756_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3757_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3591_);
v___x_3759_ = l_Lean_Name_mkStr2(v___x_3591_, v___x_3758_);
v___x_3760_ = l_Lean_addMacroScope(v_quotContext_3752_, v___x_3759_, v_currMacroScope_3753_);
lean_inc_ref(v___x_3593_);
lean_inc_ref(v___x_3592_);
v___x_3761_ = l_Lean_Name_mkStr4(v___x_3592_, v___x_3593_, v___x_3591_, v___x_3758_);
v___x_3762_ = lean_box(0);
lean_inc(v___x_3761_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 1);
lean_ctor_set(v___x_3650_, 1, v___x_3762_);
lean_ctor_set(v___x_3650_, 0, v___x_3761_);
v___x_3764_ = v___x_3650_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3766_; 
if (v_isShared_3622_ == 0)
{
lean_ctor_set_tag(v___x_3621_, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3761_);
v___x_3766_ = v___x_3621_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3761_);
v___x_3766_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3768_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3762_);
lean_ctor_set(v___x_3645_, 0, v___x_3766_);
v___x_3768_ = v___x_3645_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v___x_3762_);
v___x_3768_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 1);
lean_ctor_set(v___x_3636_, 1, v___x_3768_);
lean_ctor_set(v___x_3636_, 0, v___x_3764_);
v___x_3770_ = v___x_3636_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_inc_n(v___x_3755_, 2);
v___x_3771_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3755_);
lean_ctor_set(v___x_3771_, 1, v___x_3757_);
lean_ctor_set(v___x_3771_, 2, v___x_3760_);
lean_ctor_set(v___x_3771_, 3, v___x_3770_);
v___x_3772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3773_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3632_ == 0)
{
lean_ctor_set_tag(v___x_3631_, 2);
lean_ctor_set(v___x_3631_, 1, v___x_3774_);
lean_ctor_set(v___x_3631_, 0, v___x_3755_);
v___x_3776_ = v___x_3631_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3777_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3778_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3753_);
lean_inc(v_quotContext_3752_);
v___x_3779_ = l_Lean_addMacroScope(v_quotContext_3752_, v___x_3778_, v_currMacroScope_3753_);
lean_inc_n(v___x_3755_, 2);
v___x_3780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3755_);
lean_ctor_set(v___x_3780_, 1, v___x_3777_);
lean_ctor_set(v___x_3780_, 2, v___x_3779_);
lean_ctor_set(v___x_3780_, 3, v___x_3762_);
v___x_3781_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 2);
lean_ctor_set(v___x_3627_, 1, v___x_3781_);
lean_ctor_set(v___x_3627_, 0, v___x_3755_);
v___x_3783_ = v___x_3627_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3784_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3755_, 22);
v___x_3786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3755_);
lean_ctor_set(v___x_3786_, 1, v___x_3784_);
v___x_3787_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3788_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3789_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3753_, 5);
lean_inc_n(v_quotContext_3752_, 5);
v___x_3790_ = l_Lean_addMacroScope(v_quotContext_3752_, v___x_3789_, v_currMacroScope_3753_);
v___x_3791_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3755_);
lean_ctor_set(v___x_3791_, 1, v___x_3788_);
lean_ctor_set(v___x_3791_, 2, v___x_3790_);
lean_ctor_set(v___x_3791_, 3, v___x_3762_);
v___x_3792_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3793_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3794_ = l_Lean_addMacroScope(v_quotContext_3752_, v___x_3793_, v_currMacroScope_3753_);
v___x_3795_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3755_);
lean_ctor_set(v___x_3795_, 1, v___x_3792_);
lean_ctor_set(v___x_3795_, 2, v___x_3794_);
lean_ctor_set(v___x_3795_, 3, v___x_3762_);
lean_inc_ref(v___x_3795_);
v___x_3796_ = l_Lean_Syntax_node2(v___x_3755_, v___x_3772_, v___x_3791_, v___x_3795_);
v___x_3797_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3755_);
lean_ctor_set(v___x_3798_, 1, v___x_3772_);
lean_ctor_set(v___x_3798_, 2, v___x_3797_);
v___x_3799_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3755_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
lean_inc_ref(v___x_3800_);
lean_inc_ref(v___x_3798_);
v___x_3801_ = l_Lean_Syntax_node4(v___x_3755_, v___x_3787_, v___x_3796_, v___x_3798_, v___x_3800_, v_snd_3643_);
lean_inc_ref(v___x_3786_);
v___x_3802_ = l_Lean_Syntax_node2(v___x_3755_, v___x_3785_, v___x_3786_, v___x_3801_);
v___x_3803_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3755_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
lean_inc_ref_n(v___x_3804_, 2);
lean_inc_ref_n(v___x_3783_, 2);
lean_inc_ref_n(v___x_3776_, 2);
v___x_3805_ = l_Lean_Syntax_node5(v___x_3755_, v___x_3773_, v___x_3776_, v___x_3780_, v___x_3783_, v___x_3802_, v___x_3804_);
v___x_3806_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3807_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3808_ = l_Lean_addMacroScope(v_quotContext_3752_, v___x_3807_, v_currMacroScope_3753_);
v___x_3809_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3755_);
lean_ctor_set(v___x_3809_, 1, v___x_3806_);
lean_ctor_set(v___x_3809_, 2, v___x_3808_);
lean_ctor_set(v___x_3809_, 3, v___x_3762_);
v___x_3810_ = l_String_toRawSubstring_x27(v___x_3594_);
v___x_3811_ = l_Lean_addMacroScope(v_quotContext_3752_, v___x_3582_, v_currMacroScope_3753_);
v___x_3812_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3755_);
lean_ctor_set(v___x_3812_, 1, v___x_3810_);
lean_ctor_set(v___x_3812_, 2, v___x_3811_);
lean_ctor_set(v___x_3812_, 3, v___x_3762_);
v___x_3813_ = l_Lean_Syntax_node2(v___x_3755_, v___x_3772_, v___x_3812_, v___x_3795_);
v___x_3814_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3815_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3816_ = l_Lean_addMacroScope(v_quotContext_3752_, v___x_3815_, v_currMacroScope_3753_);
v___x_3817_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3755_);
lean_ctor_set(v___x_3817_, 1, v___x_3814_);
lean_ctor_set(v___x_3817_, 2, v___x_3816_);
lean_ctor_set(v___x_3817_, 3, v___x_3762_);
v___x_3818_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__30);
v___x_3819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__5));
v___x_3820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_collectInvariantHints_spec__1___closed__4));
v___x_3821_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__31));
v___x_3822_ = l_Lean_addMacroScope(v_quotContext_3752_, v___x_3821_, v_currMacroScope_3753_);
v___x_3823_ = l_Lean_Name_mkStr4(v___x_3592_, v___x_3593_, v___x_3819_, v___x_3820_);
v___x_3824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set(v___x_3824_, 1, v___x_3762_);
v___x_3825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
lean_ctor_set(v___x_3825_, 1, v___x_3762_);
v___x_3826_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3755_);
lean_ctor_set(v___x_3826_, 1, v___x_3818_);
lean_ctor_set(v___x_3826_, 2, v___x_3822_);
lean_ctor_set(v___x_3826_, 3, v___x_3825_);
v___x_3827_ = l_Lean_Syntax_node5(v___x_3755_, v___x_3773_, v___x_3776_, v___x_3817_, v___x_3783_, v___x_3826_, v___x_3804_);
v___x_3828_ = l_Lean_Syntax_node1(v___x_3755_, v___x_3772_, v___x_3827_);
v___x_3829_ = l_Lean_Syntax_node2(v___x_3755_, v___x_3756_, v_fst_3642_, v___x_3828_);
v___x_3830_ = l_Lean_Syntax_node4(v___x_3755_, v___x_3787_, v___x_3813_, v___x_3798_, v___x_3800_, v___x_3829_);
v___x_3831_ = l_Lean_Syntax_node2(v___x_3755_, v___x_3785_, v___x_3786_, v___x_3830_);
v___x_3832_ = l_Lean_Syntax_node5(v___x_3755_, v___x_3773_, v___x_3776_, v___x_3809_, v___x_3783_, v___x_3831_, v___x_3804_);
v___x_3833_ = l_Lean_Syntax_node2(v___x_3755_, v___x_3772_, v___x_3805_, v___x_3832_);
v___x_3834_ = l_Lean_Syntax_node2(v___x_3755_, v___x_3756_, v___x_3771_, v___x_3833_);
v_a_3605_ = v___x_3834_;
goto v___jp_3604_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_e_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_del_object(v___x_3621_);
v_e_3841_ = lean_ctor_get(v_default_3648_, 0);
lean_inc_ref(v_e_3841_);
lean_dec_ref_known(v_default_3648_, 1);
v___x_3842_ = lean_box(1);
v___x_3843_ = l_Lean_PrettyPrinter_delab(v_e_3841_, v___x_3842_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3929_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3846_ = v___x_3843_;
v_isShared_3847_ = v_isSharedCheck_3929_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3843_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3929_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v_ref_3848_; lean_object* v_quotContext_3849_; lean_object* v_currMacroScope_3850_; uint8_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
v_ref_3848_ = lean_ctor_get(v___y_3601_, 5);
lean_inc(v_ref_3848_);
v_quotContext_3849_ = lean_ctor_get(v___y_3601_, 10);
lean_inc_n(v_quotContext_3849_, 2);
v_currMacroScope_3850_ = lean_ctor_get(v___y_3601_, 11);
lean_inc_n(v_currMacroScope_3850_, 2);
lean_dec_ref(v___y_3601_);
v___x_3851_ = 0;
v___x_3852_ = l_Lean_SourceInfo_fromRef(v_ref_3848_, v___x_3851_);
lean_dec(v_ref_3848_);
v___x_3853_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3854_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3855_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3591_);
v___x_3856_ = l_Lean_Name_mkStr2(v___x_3591_, v___x_3855_);
v___x_3857_ = l_Lean_addMacroScope(v_quotContext_3849_, v___x_3856_, v_currMacroScope_3850_);
v___x_3858_ = l_Lean_Name_mkStr4(v___x_3592_, v___x_3593_, v___x_3591_, v___x_3855_);
v___x_3859_ = lean_box(0);
lean_inc(v___x_3858_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 1);
lean_ctor_set(v___x_3650_, 1, v___x_3859_);
lean_ctor_set(v___x_3650_, 0, v___x_3858_);
v___x_3861_ = v___x_3650_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v___x_3858_);
v___x_3863_ = v___x_3846_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3858_);
v___x_3863_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3865_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3859_);
lean_ctor_set(v___x_3645_, 0, v___x_3863_);
v___x_3865_ = v___x_3645_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v___x_3859_);
v___x_3865_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3867_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 1);
lean_ctor_set(v___x_3636_, 1, v___x_3865_);
lean_ctor_set(v___x_3636_, 0, v___x_3861_);
v___x_3867_ = v___x_3636_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
lean_inc_n(v___x_3852_, 2);
v___x_3868_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3852_);
lean_ctor_set(v___x_3868_, 1, v___x_3854_);
lean_ctor_set(v___x_3868_, 2, v___x_3857_);
lean_ctor_set(v___x_3868_, 3, v___x_3867_);
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3870_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3871_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3632_ == 0)
{
lean_ctor_set_tag(v___x_3631_, 2);
lean_ctor_set(v___x_3631_, 1, v___x_3871_);
lean_ctor_set(v___x_3631_, 0, v___x_3852_);
v___x_3873_ = v___x_3631_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3880_; 
v___x_3874_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3875_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3850_);
lean_inc(v_quotContext_3849_);
v___x_3876_ = l_Lean_addMacroScope(v_quotContext_3849_, v___x_3875_, v_currMacroScope_3850_);
lean_inc_n(v___x_3852_, 2);
v___x_3877_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3852_);
lean_ctor_set(v___x_3877_, 1, v___x_3874_);
lean_ctor_set(v___x_3877_, 2, v___x_3876_);
lean_ctor_set(v___x_3877_, 3, v___x_3859_);
v___x_3878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 2);
lean_ctor_set(v___x_3627_, 1, v___x_3878_);
lean_ctor_set(v___x_3627_, 0, v___x_3852_);
v___x_3880_ = v___x_3627_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v___x_3878_);
v___x_3880_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3881_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3882_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3852_, 21);
v___x_3883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3852_);
lean_ctor_set(v___x_3883_, 1, v___x_3881_);
v___x_3884_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3885_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3886_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3850_, 4);
lean_inc_n(v_quotContext_3849_, 4);
v___x_3887_ = l_Lean_addMacroScope(v_quotContext_3849_, v___x_3886_, v_currMacroScope_3850_);
v___x_3888_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3852_);
lean_ctor_set(v___x_3888_, 1, v___x_3885_);
lean_ctor_set(v___x_3888_, 2, v___x_3887_);
lean_ctor_set(v___x_3888_, 3, v___x_3859_);
v___x_3889_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3890_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3891_ = l_Lean_addMacroScope(v_quotContext_3849_, v___x_3890_, v_currMacroScope_3850_);
v___x_3892_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3852_);
lean_ctor_set(v___x_3892_, 1, v___x_3889_);
lean_ctor_set(v___x_3892_, 2, v___x_3891_);
lean_ctor_set(v___x_3892_, 3, v___x_3859_);
lean_inc_ref(v___x_3892_);
v___x_3893_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3869_, v___x_3888_, v___x_3892_);
v___x_3894_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3852_);
lean_ctor_set(v___x_3895_, 1, v___x_3869_);
lean_ctor_set(v___x_3895_, 2, v___x_3894_);
v___x_3896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3852_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
lean_inc_ref(v___x_3897_);
lean_inc_ref(v___x_3895_);
v___x_3898_ = l_Lean_Syntax_node4(v___x_3852_, v___x_3884_, v___x_3893_, v___x_3895_, v___x_3897_, v_snd_3643_);
lean_inc_ref(v___x_3883_);
v___x_3899_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3882_, v___x_3883_, v___x_3898_);
v___x_3900_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3852_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
lean_inc_ref_n(v___x_3901_, 2);
lean_inc_ref_n(v___x_3880_, 2);
lean_inc_ref_n(v___x_3873_, 2);
v___x_3902_ = l_Lean_Syntax_node5(v___x_3852_, v___x_3870_, v___x_3873_, v___x_3877_, v___x_3880_, v___x_3899_, v___x_3901_);
v___x_3903_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3905_ = l_Lean_addMacroScope(v_quotContext_3849_, v___x_3904_, v_currMacroScope_3850_);
v___x_3906_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3852_);
lean_ctor_set(v___x_3906_, 1, v___x_3903_);
lean_ctor_set(v___x_3906_, 2, v___x_3905_);
lean_ctor_set(v___x_3906_, 3, v___x_3859_);
v___x_3907_ = l_String_toRawSubstring_x27(v___x_3594_);
v___x_3908_ = l_Lean_addMacroScope(v_quotContext_3849_, v___x_3582_, v_currMacroScope_3850_);
v___x_3909_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3852_);
lean_ctor_set(v___x_3909_, 1, v___x_3907_);
lean_ctor_set(v___x_3909_, 2, v___x_3908_);
lean_ctor_set(v___x_3909_, 3, v___x_3859_);
v___x_3910_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3869_, v___x_3909_, v___x_3892_);
v___x_3911_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__19);
v___x_3912_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__20));
v___x_3913_ = l_Lean_addMacroScope(v_quotContext_3849_, v___x_3912_, v_currMacroScope_3850_);
v___x_3914_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3852_);
lean_ctor_set(v___x_3914_, 1, v___x_3911_);
lean_ctor_set(v___x_3914_, 2, v___x_3913_);
lean_ctor_set(v___x_3914_, 3, v___x_3859_);
v___x_3915_ = l_Lean_Syntax_node5(v___x_3852_, v___x_3870_, v___x_3873_, v___x_3914_, v___x_3880_, v_a_3844_, v___x_3901_);
v___x_3916_ = l_Lean_Syntax_node1(v___x_3852_, v___x_3869_, v___x_3915_);
v___x_3917_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3853_, v_fst_3642_, v___x_3916_);
v___x_3918_ = l_Lean_Syntax_node4(v___x_3852_, v___x_3884_, v___x_3910_, v___x_3895_, v___x_3897_, v___x_3917_);
v___x_3919_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3882_, v___x_3883_, v___x_3918_);
v___x_3920_ = l_Lean_Syntax_node5(v___x_3852_, v___x_3870_, v___x_3873_, v___x_3906_, v___x_3880_, v___x_3919_, v___x_3901_);
v___x_3921_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3869_, v___x_3902_, v___x_3920_);
v___x_3922_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3853_, v___x_3868_, v___x_3921_);
v_a_3605_ = v___x_3922_;
goto v___jp_3604_;
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
lean_del_object(v___x_3650_);
lean_del_object(v___x_3645_);
lean_dec(v_snd_3643_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3636_);
lean_del_object(v___x_3631_);
lean_del_object(v___x_3627_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v___x_3592_);
lean_dec_ref(v___x_3591_);
lean_dec(v___x_3582_);
v___y_3609_ = v___x_3843_;
goto v___jp_3608_;
}
}
default: 
{
lean_object* v_ref_3930_; lean_object* v_quotContext_3931_; lean_object* v_currMacroScope_3932_; uint8_t v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3943_; 
lean_dec(v_default_3648_);
v_ref_3930_ = lean_ctor_get(v___y_3601_, 5);
lean_inc(v_ref_3930_);
v_quotContext_3931_ = lean_ctor_get(v___y_3601_, 10);
lean_inc_n(v_quotContext_3931_, 2);
v_currMacroScope_3932_ = lean_ctor_get(v___y_3601_, 11);
lean_inc_n(v_currMacroScope_3932_, 2);
lean_dec_ref(v___y_3601_);
v___x_3933_ = 0;
v___x_3934_ = l_Lean_SourceInfo_fromRef(v_ref_3930_, v___x_3933_);
lean_dec(v_ref_3930_);
v___x_3935_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_3936_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_3937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3591_);
v___x_3938_ = l_Lean_Name_mkStr2(v___x_3591_, v___x_3937_);
v___x_3939_ = l_Lean_addMacroScope(v_quotContext_3931_, v___x_3938_, v_currMacroScope_3932_);
v___x_3940_ = l_Lean_Name_mkStr4(v___x_3592_, v___x_3593_, v___x_3591_, v___x_3937_);
v___x_3941_ = lean_box(0);
lean_inc(v___x_3940_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 1);
lean_ctor_set(v___x_3650_, 1, v___x_3941_);
lean_ctor_set(v___x_3650_, 0, v___x_3940_);
v___x_3943_ = v___x_3650_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___x_3945_; 
if (v_isShared_3622_ == 0)
{
lean_ctor_set_tag(v___x_3621_, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3940_);
v___x_3945_ = v___x_3621_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3940_);
v___x_3945_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
lean_object* v___x_3947_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 1, v___x_3941_);
lean_ctor_set(v___x_3645_, 0, v___x_3945_);
v___x_3947_ = v___x_3645_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3945_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v___x_3941_);
v___x_3947_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3949_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 1);
lean_ctor_set(v___x_3636_, 1, v___x_3947_);
lean_ctor_set(v___x_3636_, 0, v___x_3943_);
v___x_3949_ = v___x_3636_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3955_; 
lean_inc_n(v___x_3934_, 2);
v___x_3950_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3934_);
lean_ctor_set(v___x_3950_, 1, v___x_3936_);
lean_ctor_set(v___x_3950_, 2, v___x_3939_);
lean_ctor_set(v___x_3950_, 3, v___x_3949_);
v___x_3951_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_3952_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_3953_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
if (v_isShared_3632_ == 0)
{
lean_ctor_set_tag(v___x_3631_, 2);
lean_ctor_set(v___x_3631_, 1, v___x_3953_);
lean_ctor_set(v___x_3631_, 0, v___x_3934_);
v___x_3955_ = v___x_3631_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3956_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_3957_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc(v_currMacroScope_3932_);
lean_inc(v_quotContext_3931_);
v___x_3958_ = l_Lean_addMacroScope(v_quotContext_3931_, v___x_3957_, v_currMacroScope_3932_);
lean_inc_n(v___x_3934_, 2);
v___x_3959_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3934_);
lean_ctor_set(v___x_3959_, 1, v___x_3956_);
lean_ctor_set(v___x_3959_, 2, v___x_3958_);
lean_ctor_set(v___x_3959_, 3, v___x_3941_);
v___x_3960_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 2);
lean_ctor_set(v___x_3627_, 1, v___x_3960_);
lean_ctor_set(v___x_3627_, 0, v___x_3934_);
v___x_3962_ = v___x_3627_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3963_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_3964_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
lean_inc_n(v___x_3934_, 17);
v___x_3965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3934_);
lean_ctor_set(v___x_3965_, 1, v___x_3963_);
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_3967_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_3968_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
lean_inc_n(v_currMacroScope_3932_, 3);
lean_inc_n(v_quotContext_3931_, 3);
v___x_3969_ = l_Lean_addMacroScope(v_quotContext_3931_, v___x_3968_, v_currMacroScope_3932_);
v___x_3970_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3934_);
lean_ctor_set(v___x_3970_, 1, v___x_3967_);
lean_ctor_set(v___x_3970_, 2, v___x_3969_);
lean_ctor_set(v___x_3970_, 3, v___x_3941_);
v___x_3971_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_3972_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_3973_ = l_Lean_addMacroScope(v_quotContext_3931_, v___x_3972_, v_currMacroScope_3932_);
v___x_3974_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3934_);
lean_ctor_set(v___x_3974_, 1, v___x_3971_);
lean_ctor_set(v___x_3974_, 2, v___x_3973_);
lean_ctor_set(v___x_3974_, 3, v___x_3941_);
lean_inc_ref(v___x_3974_);
v___x_3975_ = l_Lean_Syntax_node2(v___x_3934_, v___x_3951_, v___x_3970_, v___x_3974_);
v___x_3976_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_3977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3934_);
lean_ctor_set(v___x_3977_, 1, v___x_3951_);
lean_ctor_set(v___x_3977_, 2, v___x_3976_);
v___x_3978_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_3979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3934_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
lean_inc_ref(v___x_3979_);
lean_inc_ref(v___x_3977_);
v___x_3980_ = l_Lean_Syntax_node4(v___x_3934_, v___x_3966_, v___x_3975_, v___x_3977_, v___x_3979_, v_snd_3643_);
lean_inc_ref(v___x_3965_);
v___x_3981_ = l_Lean_Syntax_node2(v___x_3934_, v___x_3964_, v___x_3965_, v___x_3980_);
v___x_3982_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_3983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3934_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
lean_inc_ref(v___x_3983_);
lean_inc_ref(v___x_3962_);
lean_inc_ref(v___x_3955_);
v___x_3984_ = l_Lean_Syntax_node5(v___x_3934_, v___x_3952_, v___x_3955_, v___x_3959_, v___x_3962_, v___x_3981_, v___x_3983_);
v___x_3985_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_3987_ = l_Lean_addMacroScope(v_quotContext_3931_, v___x_3986_, v_currMacroScope_3932_);
v___x_3988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3934_);
lean_ctor_set(v___x_3988_, 1, v___x_3985_);
lean_ctor_set(v___x_3988_, 2, v___x_3987_);
lean_ctor_set(v___x_3988_, 3, v___x_3941_);
v___x_3989_ = l_String_toRawSubstring_x27(v___x_3594_);
v___x_3990_ = l_Lean_addMacroScope(v_quotContext_3931_, v___x_3582_, v_currMacroScope_3932_);
v___x_3991_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3934_);
lean_ctor_set(v___x_3991_, 1, v___x_3989_);
lean_ctor_set(v___x_3991_, 2, v___x_3990_);
lean_ctor_set(v___x_3991_, 3, v___x_3941_);
v___x_3992_ = l_Lean_Syntax_node2(v___x_3934_, v___x_3951_, v___x_3991_, v___x_3974_);
v___x_3993_ = l_Lean_Syntax_node4(v___x_3934_, v___x_3966_, v___x_3992_, v___x_3977_, v___x_3979_, v_fst_3642_);
v___x_3994_ = l_Lean_Syntax_node2(v___x_3934_, v___x_3964_, v___x_3965_, v___x_3993_);
v___x_3995_ = l_Lean_Syntax_node5(v___x_3934_, v___x_3952_, v___x_3955_, v___x_3988_, v___x_3962_, v___x_3994_, v___x_3983_);
v___x_3996_ = l_Lean_Syntax_node2(v___x_3934_, v___x_3951_, v___x_3984_, v___x_3995_);
v___x_3997_ = l_Lean_Syntax_node2(v___x_3934_, v___x_3935_, v___x_3950_, v___x_3996_);
v_a_3605_ = v___x_3997_;
goto v___jp_3604_;
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
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_del_object(v___x_3636_);
lean_dec(v_snd_3634_);
lean_del_object(v___x_3631_);
lean_del_object(v___x_3627_);
lean_del_object(v___x_3621_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v___x_3592_);
lean_dec_ref(v___x_3591_);
lean_dec(v___x_3590_);
lean_dec(v___x_3582_);
v_a_4006_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3640_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3640_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
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
lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4092_; 
lean_dec(v_a_3612_);
lean_dec(v___x_3590_);
lean_dec(v___x_3589_);
lean_dec_ref(v___x_3583_);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_val_3615_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; lean_object* v_unused_4094_; 
v_unused_4093_ = lean_ctor_get(v_val_3615_, 1);
lean_dec(v_unused_4093_);
v_unused_4094_ = lean_ctor_get(v_val_3615_, 0);
lean_dec(v_unused_4094_);
v___x_4020_ = v_val_3615_;
v_isShared_4021_ = v_isSharedCheck_4092_;
goto v_resetjp_4019_;
}
else
{
lean_dec(v_val_3615_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4092_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v_ref_4022_; lean_object* v_quotContext_4023_; lean_object* v_currMacroScope_4024_; uint8_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4035_; 
v_ref_4022_ = lean_ctor_get(v___y_3601_, 5);
lean_inc(v_ref_4022_);
v_quotContext_4023_ = lean_ctor_get(v___y_3601_, 10);
lean_inc_n(v_quotContext_4023_, 2);
v_currMacroScope_4024_ = lean_ctor_get(v___y_3601_, 11);
lean_inc_n(v_currMacroScope_4024_, 2);
lean_dec_ref(v___y_3601_);
v___x_4025_ = 0;
v___x_4026_ = l_Lean_SourceInfo_fromRef(v_ref_4022_, v___x_4025_);
lean_dec(v_ref_4022_);
v___x_4027_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__1));
v___x_4028_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__3);
v___x_4029_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__4));
lean_inc_ref(v___x_3591_);
v___x_4030_ = l_Lean_Name_mkStr2(v___x_3591_, v___x_4029_);
v___x_4031_ = l_Lean_addMacroScope(v_quotContext_4023_, v___x_4030_, v_currMacroScope_4024_);
v___x_4032_ = l_Lean_Name_mkStr4(v___x_3592_, v___x_3593_, v___x_3591_, v___x_4029_);
v___x_4033_ = lean_box(0);
lean_inc(v___x_4032_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set_tag(v___x_4020_, 1);
lean_ctor_set(v___x_4020_, 1, v___x_4033_);
lean_ctor_set(v___x_4020_, 0, v___x_4032_);
v___x_4035_ = v___x_4020_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4033_);
v___x_4035_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4037_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 0);
lean_ctor_set(v___x_3617_, 0, v___x_4032_);
v___x_4037_ = v___x_3617_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4032_);
v___x_4037_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
lean_ctor_set(v___x_4038_, 1, v___x_4033_);
v___x_4039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4035_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
lean_inc_n(v___x_4026_, 23);
v___x_4040_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4026_);
lean_ctor_set(v___x_4040_, 1, v___x_4028_);
lean_ctor_set(v___x_4040_, 2, v___x_4031_);
lean_ctor_set(v___x_4040_, 3, v___x_4039_);
v___x_4041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__6));
v___x_4043_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__7));
v___x_4044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4026_);
lean_ctor_set(v___x_4044_, 1, v___x_4043_);
v___x_4045_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__9);
v___x_4046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__10));
lean_inc_n(v_currMacroScope_4024_, 4);
lean_inc_n(v_quotContext_4023_, 4);
v___x_4047_ = l_Lean_addMacroScope(v_quotContext_4023_, v___x_4046_, v_currMacroScope_4024_);
v___x_4048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4026_);
lean_ctor_set(v___x_4048_, 1, v___x_4045_);
lean_ctor_set(v___x_4048_, 2, v___x_4047_);
lean_ctor_set(v___x_4048_, 3, v___x_4033_);
v___x_4049_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__11));
v___x_4050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4026_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
v___x_4051_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__5));
v___x_4052_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__6));
v___x_4053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4026_);
lean_ctor_set(v___x_4053_, 1, v___x_4051_);
v___x_4054_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__8));
v___x_4055_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__12);
v___x_4056_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__4___closed__1));
v___x_4057_ = l_Lean_addMacroScope(v_quotContext_4023_, v___x_4056_, v_currMacroScope_4024_);
v___x_4058_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4026_);
lean_ctor_set(v___x_4058_, 1, v___x_4055_);
lean_ctor_set(v___x_4058_, 2, v___x_4057_);
lean_ctor_set(v___x_4058_, 3, v___x_4033_);
v___x_4059_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4061_ = l_Lean_addMacroScope(v_quotContext_4023_, v___x_4060_, v_currMacroScope_4024_);
v___x_4062_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4026_);
lean_ctor_set(v___x_4062_, 1, v___x_4059_);
lean_ctor_set(v___x_4062_, 2, v___x_4061_);
lean_ctor_set(v___x_4062_, 3, v___x_4033_);
lean_inc_ref(v___x_4062_);
v___x_4063_ = l_Lean_Syntax_node2(v___x_4026_, v___x_4041_, v___x_4058_, v___x_4062_);
v___x_4064_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
v___x_4065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4026_);
lean_ctor_set(v___x_4065_, 1, v___x_4041_);
lean_ctor_set(v___x_4065_, 2, v___x_4064_);
v___x_4066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4026_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4069_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4026_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = l_Lean_Syntax_node1(v___x_4026_, v___x_4068_, v___x_4070_);
lean_inc(v___x_4071_);
lean_inc_ref(v___x_4067_);
lean_inc_ref(v___x_4065_);
v___x_4072_ = l_Lean_Syntax_node4(v___x_4026_, v___x_4054_, v___x_4063_, v___x_4065_, v___x_4067_, v___x_4071_);
lean_inc_ref(v___x_4053_);
v___x_4073_ = l_Lean_Syntax_node2(v___x_4026_, v___x_4052_, v___x_4053_, v___x_4072_);
v___x_4074_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__14));
v___x_4075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4026_);
lean_ctor_set(v___x_4075_, 1, v___x_4074_);
lean_inc_ref(v___x_4075_);
lean_inc_ref(v___x_4050_);
lean_inc_ref(v___x_4044_);
v___x_4076_ = l_Lean_Syntax_node5(v___x_4026_, v___x_4042_, v___x_4044_, v___x_4048_, v___x_4050_, v___x_4073_, v___x_4075_);
v___x_4077_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__16);
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__17));
v___x_4079_ = l_Lean_addMacroScope(v_quotContext_4023_, v___x_4078_, v_currMacroScope_4024_);
v___x_4080_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4026_);
lean_ctor_set(v___x_4080_, 1, v___x_4077_);
lean_ctor_set(v___x_4080_, 2, v___x_4079_);
lean_ctor_set(v___x_4080_, 3, v___x_4033_);
v___x_4081_ = l_String_toRawSubstring_x27(v___x_3594_);
v___x_4082_ = l_Lean_addMacroScope(v_quotContext_4023_, v___x_3582_, v_currMacroScope_4024_);
v___x_4083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4026_);
lean_ctor_set(v___x_4083_, 1, v___x_4081_);
lean_ctor_set(v___x_4083_, 2, v___x_4082_);
lean_ctor_set(v___x_4083_, 3, v___x_4033_);
v___x_4084_ = l_Lean_Syntax_node2(v___x_4026_, v___x_4041_, v___x_4083_, v___x_4062_);
v___x_4085_ = l_Lean_Syntax_node4(v___x_4026_, v___x_4054_, v___x_4084_, v___x_4065_, v___x_4067_, v___x_4071_);
v___x_4086_ = l_Lean_Syntax_node2(v___x_4026_, v___x_4052_, v___x_4053_, v___x_4085_);
v___x_4087_ = l_Lean_Syntax_node5(v___x_4026_, v___x_4042_, v___x_4044_, v___x_4080_, v___x_4050_, v___x_4086_, v___x_4075_);
v___x_4088_ = l_Lean_Syntax_node2(v___x_4026_, v___x_4041_, v___x_4076_, v___x_4087_);
v___x_4089_ = l_Lean_Syntax_node2(v___x_4026_, v___x_4027_, v___x_4040_, v___x_4088_);
v_a_3605_ = v___x_4089_;
goto v___jp_3604_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3614_);
lean_dec_ref(v___x_3591_);
if (lean_obj_tag(v_a_3612_) == 1)
{
lean_object* v_val_4096_; lean_object* v_snd_4097_; lean_object* v_fst_4098_; lean_object* v_snd_4099_; lean_object* v___x_4100_; lean_object* v___f_4101_; lean_object* v___x_4102_; 
v_val_4096_ = lean_ctor_get(v_a_3612_, 0);
lean_inc(v_val_4096_);
lean_dec_ref_known(v_a_3612_, 1);
v_snd_4097_ = lean_ctor_get(v_val_4096_, 1);
lean_inc(v_snd_4097_);
v_fst_4098_ = lean_ctor_get(v_val_4096_, 0);
lean_inc(v_fst_4098_);
lean_dec(v_val_4096_);
v_snd_4099_ = lean_ctor_get(v_snd_4097_, 1);
lean_inc(v_snd_4099_);
lean_dec(v_snd_4097_);
v___x_4100_ = lean_box(v___x_3588_);
lean_inc(v___x_3582_);
v___f_4101_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__6___boxed), 20, 10);
lean_closure_set(v___f_4101_, 0, v_fst_4098_);
lean_closure_set(v___f_4101_, 1, v_snd_4099_);
lean_closure_set(v___f_4101_, 2, v___x_3592_);
lean_closure_set(v___f_4101_, 3, v___x_3593_);
lean_closure_set(v___f_4101_, 4, v___x_3594_);
lean_closure_set(v___f_4101_, 5, v___x_3582_);
lean_closure_set(v___f_4101_, 6, v___x_3589_);
lean_closure_set(v___f_4101_, 7, v___x_4100_);
lean_closure_set(v___f_4101_, 8, v___x_3590_);
lean_closure_set(v___f_4101_, 9, v_arg_3587_);
v___x_4102_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v___x_3582_, v___x_3583_, v___f_4101_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec_ref(v___y_3601_);
v___y_3609_ = v___x_4102_;
goto v___jp_3608_;
}
else
{
lean_object* v_ref_4103_; lean_object* v_quotContext_4104_; lean_object* v_currMacroScope_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
lean_dec(v_a_3612_);
lean_dec(v___x_3590_);
lean_dec(v___x_3589_);
lean_dec_ref(v_arg_3587_);
lean_dec_ref(v___x_3583_);
v_ref_4103_ = lean_ctor_get(v___y_3601_, 5);
lean_inc(v_ref_4103_);
v_quotContext_4104_ = lean_ctor_get(v___y_3601_, 10);
lean_inc_n(v_quotContext_4104_, 2);
v_currMacroScope_4105_ = lean_ctor_get(v___y_3601_, 11);
lean_inc_n(v_currMacroScope_4105_, 2);
lean_dec_ref(v___y_3601_);
v___x_4106_ = 0;
v___x_4107_ = l_Lean_SourceInfo_fromRef(v_ref_4103_, v___x_4106_);
lean_dec(v_ref_4103_);
v___x_4108_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__0));
v___x_4109_ = l_Lean_Name_mkStr3(v___x_3592_, v___x_3593_, v___x_4108_);
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__2));
v___x_4111_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__6);
lean_inc_n(v___x_4107_, 13);
v___x_4112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4107_);
lean_ctor_set(v___x_4112_, 1, v___x_4110_);
lean_ctor_set(v___x_4112_, 2, v___x_4111_);
v___x_4113_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__3));
v___x_4114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4107_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__5));
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__21));
v___x_4117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__22));
v___x_4118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4107_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = l_String_toRawSubstring_x27(v___x_3594_);
v___x_4120_ = l_Lean_addMacroScope(v_quotContext_4104_, v___x_3582_, v_currMacroScope_4105_);
v___x_4121_ = lean_box(0);
v___x_4122_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4107_);
lean_ctor_set(v___x_4122_, 1, v___x_4119_);
lean_ctor_set(v___x_4122_, 2, v___x_4120_);
lean_ctor_set(v___x_4122_, 3, v___x_4121_);
v___x_4123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__0));
v___x_4124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4107_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13, &l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__13);
v___x_4126_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___closed__1));
v___x_4127_ = l_Lean_addMacroScope(v_quotContext_4104_, v___x_4126_, v_currMacroScope_4105_);
v___x_4128_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4107_);
lean_ctor_set(v___x_4128_, 1, v___x_4125_);
lean_ctor_set(v___x_4128_, 2, v___x_4127_);
lean_ctor_set(v___x_4128_, 3, v___x_4121_);
v___x_4129_ = l_Lean_Syntax_node3(v___x_4107_, v___x_4115_, v___x_4122_, v___x_4124_, v___x_4128_);
v___x_4130_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_suggestInvariant_postCondWithMultipleConditions___closed__7));
v___x_4131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4107_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = l_Lean_Syntax_node3(v___x_4107_, v___x_4116_, v___x_4118_, v___x_4129_, v___x_4131_);
v___x_4133_ = l_Lean_Syntax_node1(v___x_4107_, v___x_4115_, v___x_4132_);
v___x_4134_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__5___closed__4));
v___x_4135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4107_);
lean_ctor_set(v___x_4135_, 1, v___x_4134_);
v___x_4136_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__22));
v___x_4137_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___closed__23));
v___x_4138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4107_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = l_Lean_Syntax_node1(v___x_4107_, v___x_4136_, v___x_4138_);
v___x_4140_ = l_Lean_Syntax_node5(v___x_4107_, v___x_4109_, v___x_4112_, v___x_4114_, v___x_4133_, v___x_4135_, v___x_4139_);
v_a_3605_ = v___x_4140_;
goto v___jp_3604_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec(v_a_3612_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v___x_3592_);
lean_dec_ref(v___x_3591_);
lean_dec(v___x_3590_);
lean_dec(v___x_3589_);
lean_dec_ref(v_arg_3587_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3582_);
v_a_4141_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_3613_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_3613_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v___x_3592_);
lean_dec_ref(v___x_3591_);
lean_dec(v___x_3590_);
lean_dec(v___x_3589_);
lean_dec_ref(v_arg_3587_);
lean_dec(v_inv_3586_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3582_);
v_a_4149_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_3611_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_3611_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
v___jp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_eraseQuoteMacroScopesFromSyntax(v_a_3605_);
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
return v___x_3607_;
}
v___jp_3608_:
{
if (lean_obj_tag(v___y_3609_) == 0)
{
lean_object* v_a_3610_; 
v_a_3610_ = lean_ctor_get(v___y_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___y_3609_, 1);
v_a_3605_ = v_a_3610_;
goto v___jp_3604_;
}
else
{
return v___y_3609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed(lean_object** _args){
lean_object* v___x_4157_ = _args[0];
lean_object* v___x_4158_ = _args[1];
lean_object* v___f_4159_ = _args[2];
lean_object* v_a_4160_ = _args[3];
lean_object* v_inv_4161_ = _args[4];
lean_object* v_arg_4162_ = _args[5];
lean_object* v___x_4163_ = _args[6];
lean_object* v___x_4164_ = _args[7];
lean_object* v___x_4165_ = _args[8];
lean_object* v___x_4166_ = _args[9];
lean_object* v___x_4167_ = _args[10];
lean_object* v___x_4168_ = _args[11];
lean_object* v___x_4169_ = _args[12];
lean_object* v___y_4170_ = _args[13];
lean_object* v___y_4171_ = _args[14];
lean_object* v___y_4172_ = _args[15];
lean_object* v___y_4173_ = _args[16];
lean_object* v___y_4174_ = _args[17];
lean_object* v___y_4175_ = _args[18];
lean_object* v___y_4176_ = _args[19];
lean_object* v___y_4177_ = _args[20];
lean_object* v___y_4178_ = _args[21];
_start:
{
uint8_t v___x_93975__boxed_4179_; lean_object* v_res_4180_; 
v___x_93975__boxed_4179_ = lean_unbox(v___x_4163_);
v_res_4180_ = l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7(v___x_4157_, v___x_4158_, v___f_4159_, v_a_4160_, v_inv_4161_, v_arg_4162_, v___x_93975__boxed_4179_, v___x_4164_, v___x_4165_, v___x_4166_, v___x_4167_, v___x_4168_, v___x_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec_ref(v_a_4160_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(lean_object* v_msgData_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; lean_object* v_env_4188_; lean_object* v___x_4189_; lean_object* v_mctx_4190_; lean_object* v_lctx_4191_; lean_object* v_options_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4187_ = lean_st_ref_get(v___y_4185_);
v_env_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc_ref(v_env_4188_);
lean_dec(v___x_4187_);
v___x_4189_ = lean_st_ref_get(v___y_4183_);
v_mctx_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc_ref(v_mctx_4190_);
lean_dec(v___x_4189_);
v_lctx_4191_ = lean_ctor_get(v___y_4182_, 2);
v_options_4192_ = lean_ctor_get(v___y_4184_, 2);
lean_inc_ref(v_options_4192_);
lean_inc_ref(v_lctx_4191_);
v___x_4193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4193_, 0, v_env_4188_);
lean_ctor_set(v___x_4193_, 1, v_mctx_4190_);
lean_ctor_set(v___x_4193_, 2, v_lctx_4191_);
lean_ctor_set(v___x_4193_, 3, v_options_4192_);
v___x_4194_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
lean_ctor_set(v___x_4194_, 1, v_msgData_4181_);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1___boxed(lean_object* v_msgData_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msgData_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(lean_object* v_msg_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v_ref_4209_; lean_object* v___x_4210_; lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4219_; 
v_ref_4209_ = lean_ctor_get(v___y_4206_, 5);
v___x_4210_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1_spec__1(v_msg_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
lean_inc(v_ref_4209_);
v___x_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4215_, 0, v_ref_4209_);
lean_ctor_set(v___x_4215_, 1, v_a_4211_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set_tag(v___x_4213_, 1);
lean_ctor_set(v___x_4213_, 0, v___x_4215_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg___boxed(lean_object* v_msg_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(lean_object* v_as_4233_, size_t v_i_4234_, size_t v_stop_4235_, lean_object* v_b_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_a_4247_; lean_object* v_a_4252_; uint8_t v___x_4254_; 
v___x_4254_ = lean_usize_dec_eq(v_i_4234_, v_stop_4235_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4238_, v___y_4240_, v___y_4242_, v___y_4244_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4257_; lean_object* v___y_4259_; uint8_t v___y_4260_; lean_object* v___y_4275_; lean_object* v_a_4276_; lean_object* v___x_4279_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___x_4257_ = lean_array_uget_borrowed(v_as_4233_, v_i_4234_);
lean_inc(v___x_4257_);
v___x_4279_ = l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_duplicateMVar(v___x_4257_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v_ref_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v_ref_4281_ = lean_ctor_get(v___y_4243_, 5);
v___x_4282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__0));
v___x_4283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___closed__1));
v___x_4284_ = l_Lean_SourceInfo_fromRef(v_ref_4281_, v___x_4254_);
lean_inc(v___x_4284_);
v___x_4285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4284_);
lean_ctor_set(v___x_4285_, 1, v___x_4282_);
v___x_4286_ = l_Lean_Syntax_node1(v___x_4284_, v___x_4283_, v___x_4285_);
v___x_4287_ = l_Lean_Elab_Tactic_evalTacticAt(v___x_4286_, v_a_4280_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; 
lean_dec(v_a_4256_);
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
v___x_4289_ = lean_array_mk(v_a_4288_);
v_a_4252_ = v___x_4289_;
goto v___jp_4251_;
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
v_a_4290_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4287_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4287_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
lean_inc(v_a_4290_);
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
v___y_4275_ = v___x_4295_;
v_a_4276_ = v_a_4290_;
goto v___jp_4274_;
}
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
v_a_4298_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4279_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4279_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
lean_inc(v_a_4298_);
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
v___y_4275_ = v___x_4303_;
v_a_4276_ = v_a_4298_;
goto v___jp_4274_;
}
}
}
v___jp_4258_:
{
if (v___y_4260_ == 0)
{
lean_object* v___x_4261_; 
lean_dec_ref(v___y_4259_);
v___x_4261_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4256_, v___y_4260_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
lean_dec_ref_known(v___x_4261_, 1);
v___x_4262_ = lean_unsigned_to_nat(1u);
v___x_4263_ = lean_mk_empty_array_with_capacity(v___x_4262_);
lean_inc(v___x_4257_);
v___x_4264_ = lean_array_push(v___x_4263_, v___x_4257_);
v_a_4252_ = v___x_4264_;
goto v___jp_4251_;
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec_ref(v_b_4236_);
v_a_4265_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4261_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4261_);
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
lean_dec(v_a_4256_);
lean_dec_ref(v_b_4236_);
if (lean_obj_tag(v___y_4259_) == 0)
{
lean_object* v_a_4273_; 
v_a_4273_ = lean_ctor_get(v___y_4259_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___y_4259_, 1);
v_a_4247_ = v_a_4273_;
goto v___jp_4246_;
}
else
{
return v___y_4259_;
}
}
}
v___jp_4274_:
{
uint8_t v___x_4277_; 
v___x_4277_ = l_Lean_Exception_isInterrupt(v_a_4276_);
if (v___x_4277_ == 0)
{
uint8_t v___x_4278_; 
v___x_4278_ = l_Lean_Exception_isRuntime(v_a_4276_);
v___y_4259_ = v___y_4275_;
v___y_4260_ = v___x_4278_;
goto v___jp_4258_;
}
else
{
lean_dec_ref(v_a_4276_);
v___y_4259_ = v___y_4275_;
v___y_4260_ = v___x_4277_;
goto v___jp_4258_;
}
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec_ref(v_b_4236_);
v_a_4306_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4255_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4255_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
else
{
lean_object* v___x_4314_; 
v___x_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4314_, 0, v_b_4236_);
return v___x_4314_;
}
v___jp_4246_:
{
size_t v___x_4248_; size_t v___x_4249_; 
v___x_4248_ = ((size_t)1ULL);
v___x_4249_ = lean_usize_add(v_i_4234_, v___x_4248_);
v_i_4234_ = v___x_4249_;
v_b_4236_ = v_a_4247_;
goto _start;
}
v___jp_4251_:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Array_append___redArg(v_b_4236_, v_a_4252_);
lean_dec_ref(v_a_4252_);
v_a_4247_ = v___x_4253_;
goto v___jp_4246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6___boxed(lean_object* v_as_4315_, lean_object* v_i_4316_, lean_object* v_stop_4317_, lean_object* v_b_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
size_t v_i_boxed_4328_; size_t v_stop_boxed_4329_; lean_object* v_res_4330_; 
v_i_boxed_4328_ = lean_unbox_usize(v_i_4316_);
lean_dec(v_i_4316_);
v_stop_boxed_4329_ = lean_unbox_usize(v_stop_4317_);
lean_dec(v_stop_4317_);
v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_as_4315_, v_i_boxed_4328_, v_stop_boxed_4329_, v_b_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec_ref(v_as_4315_);
return v_res_4330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__0));
v___x_4333_ = l_Lean_stringToMessageData(v___x_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant(lean_object* v_vcs_4349_, lean_object* v_inv_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v___x_4360_; 
lean_inc(v_inv_4350_);
v___x_4360_ = l_Lean_MVarId_getType(v_inv_4350_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4362_; lean_object* v_a_4363_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___x_4377_; uint8_t v___x_4378_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
v___x_4362_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_4361_, v_a_4356_);
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc_n(v_a_4363_, 2);
lean_dec_ref(v___x_4362_);
v___x_4377_ = l_Lean_Expr_cleanupAnnotations(v_a_4363_);
v___x_4378_ = l_Lean_Expr_isApp(v___x_4377_);
if (v___x_4378_ == 0)
{
lean_dec_ref(v___x_4377_);
lean_dec(v_inv_4350_);
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
v___y_4368_ = v_a_4354_;
v___y_4369_ = v_a_4355_;
v___y_4370_ = v_a_4356_;
v___y_4371_ = v_a_4357_;
v___y_4372_ = v_a_4358_;
goto v___jp_4364_;
}
else
{
lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4377_);
v___x_4380_ = l_Lean_Expr_isApp(v___x_4379_);
if (v___x_4380_ == 0)
{
lean_dec_ref(v___x_4379_);
lean_dec(v_inv_4350_);
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
v___y_4368_ = v_a_4354_;
v___y_4369_ = v_a_4355_;
v___y_4370_ = v_a_4356_;
v___y_4371_ = v_a_4357_;
v___y_4372_ = v_a_4358_;
goto v___jp_4364_;
}
else
{
lean_object* v_arg_4381_; lean_object* v___x_4382_; uint8_t v___x_4383_; 
v_arg_4381_ = lean_ctor_get(v___x_4379_, 1);
lean_inc_ref(v_arg_4381_);
v___x_4382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4379_);
v___x_4383_ = l_Lean_Expr_isApp(v___x_4382_);
if (v___x_4383_ == 0)
{
lean_dec_ref(v___x_4382_);
lean_dec_ref(v_arg_4381_);
lean_dec(v_inv_4350_);
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
v___y_4368_ = v_a_4354_;
v___y_4369_ = v_a_4355_;
v___y_4370_ = v_a_4356_;
v___y_4371_ = v_a_4357_;
v___y_4372_ = v_a_4358_;
goto v___jp_4364_;
}
else
{
lean_object* v_arg_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v_arg_4384_ = lean_ctor_get(v___x_4382_, 1);
lean_inc_ref(v_arg_4384_);
v___x_4385_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4382_);
v___x_4386_ = l_Lean_Expr_isApp(v___x_4385_);
if (v___x_4386_ == 0)
{
lean_dec_ref(v___x_4385_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
lean_dec(v_inv_4350_);
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
v___y_4368_ = v_a_4354_;
v___y_4369_ = v_a_4355_;
v___y_4370_ = v_a_4356_;
v___y_4371_ = v_a_4357_;
v___y_4372_ = v_a_4358_;
goto v___jp_4364_;
}
else
{
lean_object* v_arg_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v_arg_4387_ = lean_ctor_get(v___x_4385_, 1);
lean_inc_ref(v_arg_4387_);
v___x_4388_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4385_);
v___x_4389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__1));
v___x_4390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant_0__Lean_Elab_Tactic_Do_getSPredGoalHypsAndTarget___redArg___closed__3));
v___x_4391_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__2));
v___x_4392_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__3));
v___x_4393_ = l_Lean_Expr_isConstOf(v___x_4388_, v___x_4392_);
if (v___x_4393_ == 0)
{
lean_dec_ref(v___x_4388_);
lean_dec_ref(v_arg_4387_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
lean_dec(v_inv_4350_);
v___y_4365_ = v_a_4351_;
v___y_4366_ = v_a_4352_;
v___y_4367_ = v_a_4353_;
v___y_4368_ = v_a_4354_;
v___y_4369_ = v_a_4355_;
v___y_4370_ = v_a_4356_;
v___y_4371_ = v_a_4357_;
v___y_4372_ = v_a_4358_;
goto v___jp_4364_;
}
else
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v_a_4400_; lean_object* v___y_4412_; lean_object* v___x_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; 
lean_dec(v_a_4363_);
v___x_4394_ = lean_unsigned_to_nat(1u);
v___x_4395_ = l_Lean_Expr_constLevels_x21(v___x_4388_);
lean_dec_ref(v___x_4388_);
v___x_4396_ = lean_unsigned_to_nat(0u);
v___x_4397_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__4));
lean_inc(v___x_4395_);
v___x_4398_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_4395_, v___x_4395_, v___x_4394_, v___x_4397_);
lean_dec(v___x_4395_);
v___x_4422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__8));
v___x_4423_ = lean_array_get_size(v_vcs_4349_);
v___x_4424_ = lean_nat_dec_lt(v___x_4396_, v___x_4423_);
if (v___x_4424_ == 0)
{
v_a_4400_ = v___x_4422_;
goto v___jp_4399_;
}
else
{
uint8_t v___x_4425_; 
v___x_4425_ = lean_nat_dec_le(v___x_4423_, v___x_4423_);
if (v___x_4425_ == 0)
{
if (v___x_4424_ == 0)
{
v_a_4400_ = v___x_4422_;
goto v___jp_4399_;
}
else
{
size_t v___x_4426_; size_t v___x_4427_; lean_object* v___x_4428_; 
v___x_4426_ = ((size_t)0ULL);
v___x_4427_ = lean_usize_of_nat(v___x_4423_);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4349_, v___x_4426_, v___x_4427_, v___x_4422_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
v___y_4412_ = v___x_4428_;
goto v___jp_4411_;
}
}
else
{
size_t v___x_4429_; size_t v___x_4430_; lean_object* v___x_4431_; 
v___x_4429_ = ((size_t)0ULL);
v___x_4430_ = lean_usize_of_nat(v___x_4423_);
v___x_4431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__6(v_vcs_4349_, v___x_4429_, v___x_4430_, v___x_4422_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
v___y_4412_ = v___x_4431_;
goto v___jp_4411_;
}
}
v___jp_4399_:
{
lean_object* v___x_4401_; lean_object* v___f_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___f_4409_; lean_object* v___x_4410_; 
v___x_4401_ = lean_box(v___x_4393_);
lean_inc_ref(v_arg_4381_);
lean_inc_n(v_inv_4350_, 2);
lean_inc_ref(v_a_4400_);
v___f_4402_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__1___boxed), 15, 5);
lean_closure_set(v___f_4402_, 0, v_a_4400_);
lean_closure_set(v___f_4402_, 1, v_inv_4350_);
lean_closure_set(v___f_4402_, 2, v___x_4401_);
lean_closure_set(v___f_4402_, 3, v___x_4394_);
lean_closure_set(v___f_4402_, 4, v_arg_4381_);
v___x_4403_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__5));
v___x_4404_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__6));
v___x_4405_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_suggestInvariant___closed__7));
v___x_4406_ = l_Lean_mkConst(v___x_4405_, v___x_4398_);
v___x_4407_ = l_Lean_mkAppB(v___x_4406_, v_arg_4387_, v_arg_4384_);
v___x_4408_ = lean_box(v___x_4393_);
v___f_4409_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___lam__7___boxed), 22, 13);
lean_closure_set(v___f_4409_, 0, v___x_4404_);
lean_closure_set(v___f_4409_, 1, v___x_4407_);
lean_closure_set(v___f_4409_, 2, v___f_4402_);
lean_closure_set(v___f_4409_, 3, v_a_4400_);
lean_closure_set(v___f_4409_, 4, v_inv_4350_);
lean_closure_set(v___f_4409_, 5, v_arg_4381_);
lean_closure_set(v___f_4409_, 6, v___x_4408_);
lean_closure_set(v___f_4409_, 7, v___x_4394_);
lean_closure_set(v___f_4409_, 8, v___x_4396_);
lean_closure_set(v___f_4409_, 9, v___x_4391_);
lean_closure_set(v___f_4409_, 10, v___x_4389_);
lean_closure_set(v___f_4409_, 11, v___x_4390_);
lean_closure_set(v___f_4409_, 12, v___x_4403_);
v___x_4410_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__5___redArg(v_inv_4350_, v___f_4409_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
return v___x_4410_;
}
v___jp_4411_:
{
if (lean_obj_tag(v___y_4412_) == 0)
{
lean_object* v_a_4413_; 
v_a_4413_ = lean_ctor_get(v___y_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___y_4412_, 1);
v_a_4400_ = v_a_4413_;
goto v___jp_4399_;
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
lean_dec(v___x_4398_);
lean_dec_ref(v_arg_4387_);
lean_dec_ref(v_arg_4384_);
lean_dec_ref(v_arg_4381_);
lean_dec(v_inv_4350_);
v_a_4414_ = lean_ctor_get(v___y_4412_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___y_4412_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___y_4412_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___y_4412_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
}
}
}
}
}
v___jp_4364_:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4373_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1, &l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1_once, _init_l_Lean_Elab_Tactic_Do_suggestInvariant___closed__1);
v___x_4374_ = l_Lean_MessageData_ofExpr(v_a_4363_);
v___x_4375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4373_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
v___x_4376_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v___x_4375_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
return v___x_4376_;
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec(v_inv_4350_);
v_a_4432_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4360_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4360_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object* v_vcs_4440_, lean_object* v_inv_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_Elab_Tactic_Do_suggestInvariant(v_vcs_4440_, v_inv_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
lean_dec(v_a_4449_);
lean_dec_ref(v_a_4448_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec_ref(v_vcs_4440_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(lean_object* v_00_u03b1_4452_, lean_object* v_msg_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___redArg(v_msg_4453_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1___boxed(lean_object* v_00_u03b1_4464_, lean_object* v_msg_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__1(v_00_u03b1_4464_, v_msg_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(lean_object* v_00_u03b1_4476_, lean_object* v_name_4477_, uint8_t v_bi_4478_, lean_object* v_type_4479_, lean_object* v_k_4480_, uint8_t v_kind_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___redArg(v_name_4477_, v_bi_4478_, v_type_4479_, v_k_4480_, v_kind_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4492_, lean_object* v_name_4493_, lean_object* v_bi_4494_, lean_object* v_type_4495_, lean_object* v_k_4496_, lean_object* v_kind_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
uint8_t v_bi_boxed_4507_; uint8_t v_kind_boxed_4508_; lean_object* v_res_4509_; 
v_bi_boxed_4507_ = lean_unbox(v_bi_4494_);
v_kind_boxed_4508_ = lean_unbox(v_kind_4497_);
v_res_4509_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2_spec__3(v_00_u03b1_4492_, v_name_4493_, v_bi_boxed_4507_, v_type_4495_, v_k_4496_, v_kind_boxed_4508_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(lean_object* v_00_u03b1_4510_, lean_object* v_name_4511_, lean_object* v_type_4512_, lean_object* v_k_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___redArg(v_name_4511_, v_type_4512_, v_k_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2___boxed(lean_object* v_00_u03b1_4524_, lean_object* v_name_4525_, lean_object* v_type_4526_, lean_object* v_k_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__2(v_00_u03b1_4524_, v_name_4525_, v_type_4526_, v_k_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(lean_object* v_as_4538_, size_t v_sz_4539_, size_t v_i_4540_, lean_object* v_b_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___redArg(v_as_4538_, v_sz_4539_, v_i_4540_, v_b_4541_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3___boxed(lean_object* v_as_4552_, lean_object* v_sz_4553_, lean_object* v_i_4554_, lean_object* v_b_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
size_t v_sz_boxed_4565_; size_t v_i_boxed_4566_; lean_object* v_res_4567_; 
v_sz_boxed_4565_ = lean_unbox_usize(v_sz_4553_);
lean_dec(v_sz_4553_);
v_i_boxed_4566_ = lean_unbox_usize(v_i_4554_);
lean_dec(v_i_4554_);
v_res_4567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__3(v_as_4552_, v_sz_boxed_4565_, v_i_boxed_4566_, v_b_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec_ref(v_as_4552_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(lean_object* v_as_4568_, size_t v_sz_4569_, size_t v_i_4570_, lean_object* v_b_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___redArg(v_as_4568_, v_sz_4569_, v_i_4570_, v_b_4571_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4___boxed(lean_object* v_as_4582_, lean_object* v_sz_4583_, lean_object* v_i_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
size_t v_sz_boxed_4595_; size_t v_i_boxed_4596_; lean_object* v_res_4597_; 
v_sz_boxed_4595_ = lean_unbox_usize(v_sz_4583_);
lean_dec(v_sz_4583_);
v_i_boxed_4596_ = lean_unbox_usize(v_i_4584_);
lean_dec(v_i_4584_);
v_res_4597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__4(v_as_4582_, v_sz_boxed_4595_, v_i_boxed_4596_, v_b_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec_ref(v_as_4582_);
return v_res_4597_;
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
